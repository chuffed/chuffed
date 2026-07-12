#include "chuffed/globals/blackbox.h"

#include "chuffed/core/propagator.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/int-view.h"
#include "chuffed/vars/vars.h"

#include <algorithm>
#include <cassert>
#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <limits>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#ifdef _WIN32
#include <iostream>
#else
#include <dlfcn.h>
#include <stdio.h>  // NOLINT(modernize-deprecated-headers): POSIX getline/fdopen
#include <sys/types.h>
#include <unistd.h>
#endif

namespace {

/// Resolve \a name from a loaded \a library. On 32-bit Windows also try the
/// stdcall-decorated forms `_name@bytes` and `name@bytes`.
template <class T>
T library_symbol(void* library, const char* name, unsigned int stdcall_bytes) {
#ifdef _WIN32
	FARPROC symbol = GetProcAddress(static_cast<HMODULE>(library), name);
#if defined(_M_IX86) || defined(__i386__)
	if (symbol == nullptr) {
		const std::string decorated = std::string("_") + name + "@" + std::to_string(stdcall_bytes);
		symbol = GetProcAddress(static_cast<HMODULE>(library), decorated.c_str());
	}
	if (symbol == nullptr) {
		const std::string decorated = std::string(name) + "@" + std::to_string(stdcall_bytes);
		symbol = GetProcAddress(static_cast<HMODULE>(library), decorated.c_str());
	}
#else
	(void)stdcall_bytes;
#endif
	return reinterpret_cast<T>(symbol);
#else
	(void)stdcall_bytes;
	T symbol = nullptr;
	*reinterpret_cast<void**>(&symbol) = dlsym(library, name);
	return symbol;
#endif
}

/// Validate that a black-box output fits in Chuffed's integer range, returning
/// it as an `int`.
int check_int(int64_t v, const char* source, int index) {
	if (v < IntVar::min_limit || v > IntVar::max_limit) {
		throw std::string("BlackBox: ") + source + " integer " + std::to_string(index) +
				" is outside Chuffed's integer range";
	}
	return static_cast<int>(v);
}

}  // namespace

BlackBoxDLL::BlackBoxDLL(const std::string& name, const std::vector<std::string>& args) {
	std::string loadError;
#ifdef _WIN32
	library = LoadLibraryA(name.c_str());
	if (library == nullptr) {
		loadError = std::string("unable to locate library `") + name + "'";
		library = LoadLibraryA((std::string(name) + ".dll").c_str());
	}
	if (library == nullptr) {
		library = LoadLibraryA((std::string("lib") + name + ".dll").c_str());
	}
#else
	library = dlopen(name.c_str(), RTLD_LAZY);
	if (library == nullptr) {
		loadError = std::string(dlerror());
		library = dlopen((name + ".so").c_str(), RTLD_NOW);
	}
	if (library == nullptr) {
		library = dlopen((std::string("lib") + name + ".so").c_str(), RTLD_NOW);
	}
#ifdef __APPLE__
	if (library == nullptr) {
		library = dlopen((name + ".dylib").c_str(), RTLD_NOW);
	}
	if (library == nullptr) {
		library = dlopen((std::string("lib") + name + ".dylib").c_str(), RTLD_NOW);
	}
#endif
#endif
	if (library == nullptr) {
		throw std::string("BlackboxDLL: Unable to open dynamic library: " + loadError);
	}

	// fzn_blackbox is the only required entry point; fzn_init / fzn_clone /
	// fzn_free are optional. A library exporting fzn_init must also export
	// fzn_clone, and its instance is released with fzn_free (see blackbox.h).
	root_instance = nullptr;
	dll_fzn_free = nullptr;
	try {
		dll_fzn_blackbox = library_symbol<decltype(dll_fzn_blackbox)>(library, "fzn_blackbox", 36);
		if (dll_fzn_blackbox == nullptr) {
			throw std::string("BlackBoxDLL: Unable to find symbol `fzn_blackbox' in dynamic library");
		}
		auto init_fn = library_symbol<void*(__stdcall*)(const char**, size_t)>(library, "fzn_init", 8);
		auto clone_fn = library_symbol<void*(__stdcall*)(void*)>(library, "fzn_clone", 4);
		dll_fzn_free = library_symbol<decltype(dll_fzn_free)>(library, "fzn_free", 4);
		if ((init_fn != nullptr) && (clone_fn == nullptr)) {
			throw std::string("BlackBoxDLL: dynamic library exports `fzn_init' but not `fzn_clone'");
		}
		if (init_fn != nullptr) {
			std::vector<const char*> argv;
			argv.reserve(args.size());
			for (const std::string& a : args) {
				argv.push_back(a.c_str());
			}
			root_instance = init_fn(argv.data(), argv.size());
		}
	} catch (...) {
		if (root_instance != nullptr && dll_fzn_free != nullptr) {
			dll_fzn_free(root_instance);
		}
#ifdef _WIN32
		FreeLibrary(static_cast<HMODULE>(library));
#else
		dlclose(library);
#endif
		library = nullptr;
		throw;
	}
}

BlackBoxDLL::~BlackBoxDLL() {
	if (root_instance != nullptr && dll_fzn_free != nullptr) {
		dll_fzn_free(root_instance);
	}
	if (library != nullptr) {
#ifdef _WIN32
		FreeLibrary((HMODULE)library);
#else
		dlclose(library);
#endif
	}
}

void BlackBoxDLL::run(const std::vector<int64_t>& int_in, const std::vector<double>& float_in,
											std::vector<int64_t>& int_out, std::vector<double>& float_out) {
	// Chuffed is single-threaded, so the root instance is used directly.
	dll_fzn_blackbox(root_instance, int_in.data(), int_in.size(), float_in.data(), float_in.size(),
									 int_out.data(), int_out.size(), float_out.data(), float_out.size());
}

BlackBoxExec::BlackBoxExec(const std::string& program, const std::vector<std::string>& args) {
#ifdef _WIN32
	SECURITY_ATTRIBUTES saAttr;
	saAttr.nLength = sizeof(SECURITY_ATTRIBUTES);
	saAttr.bInheritHandle = TRUE;
	saAttr.lpSecurityDescriptor = NULL;

	HANDLE g_hChildStd_IN_Rd = NULL;
	HANDLE g_hChildStd_IN_Wr = NULL;
	HANDLE g_hChildStd_OUT_Rd = NULL;
	HANDLE g_hChildStd_OUT_Wr = NULL;

	// Create a pipe for the child process's STDOUT.
	if (!CreatePipe(&g_hChildStd_OUT_Rd, &g_hChildStd_OUT_Wr, &saAttr, 0))
		std::cerr << "Stdout CreatePipe" << std::endl;
	// Ensure the read handle to the pipe for STDOUT is not inherited.
	if (!SetHandleInformation(g_hChildStd_OUT_Rd, HANDLE_FLAG_INHERIT, 0))
		std::cerr << "Stdout SetHandleInformation" << std::endl;

	// Create a pipe for the child process's STDIN
	if (!CreatePipe(&g_hChildStd_IN_Rd, &g_hChildStd_IN_Wr, &saAttr, 0))
		std::cerr << "Stdin CreatePipe" << std::endl;
	// Ensure the write handle to the pipe for STDIN is not inherited.
	if (!SetHandleInformation(g_hChildStd_IN_Wr, HANDLE_FLAG_INHERIT, 0))
		std::cerr << "Stdin SetHandleInformation" << std::endl;

	PROCESS_INFORMATION piProcInfo;
	STARTUPINFOA siStartInfo;

	// Set up members of the PROCESS_INFORMATION structure.
	ZeroMemory(&piProcInfo, sizeof(PROCESS_INFORMATION));

	// Set up members of the STARTUPINFO structure.
	// This structure specifies the STDIN and STDOUT handles for redirection.
	ZeroMemory(&siStartInfo, sizeof(STARTUPINFOA));
	siStartInfo.cb = sizeof(STARTUPINFOA);
	siStartInfo.hStdOutput = g_hChildStd_OUT_Wr;
	siStartInfo.hStdInput = g_hChildStd_IN_Rd;
	siStartInfo.dwFlags |= STARTF_USESTDHANDLES;

	// Build the command line: the program followed by the (quoted) arguments.
	std::string prog = program;
	for (const std::string& a : args) {
		prog += " \"";
		for (char ch : a) {
			if (ch == '"' || ch == '\\') {
				prog += '\\';
			}
			prog += ch;
		}
		prog += '"';
	}
	BOOL processStarted = CreateProcessA(nullptr,
																			 &prog[0],      // command line
																			 nullptr,       // process security attributes
																			 nullptr,       // primary thread security attributes
																			 TRUE,          // handles are inherited
																			 0,             // creation flags
																			 nullptr,       // use parent's environment
																			 nullptr,       // use parent's current directory
																			 &siStartInfo,  // STARTUPINFO pointer
																			 &piProcInfo);  // receives PROCESS_INFORMATION

	if (!processStarted) {
		throw std::string("BlackBoxExec: Unable to start program `" + program + "'");
	}

	CloseHandle(piProcInfo.hThread);
	// Stop ReadFile from blocking
	CloseHandle(g_hChildStd_OUT_Wr);
	// Just close the child's in pipe here
	CloseHandle(g_hChildStd_IN_Rd);

	pipe_send = g_hChildStd_IN_Wr;
	pipe_receive = g_hChildStd_OUT_Rd;
#else
	const int READ = 0;
	const int WRITE = 1;
	int child_in[2];
	int child_out[2];
	pipe(child_in);
	pipe(child_out);

	if (fork() != 0) {
		close(child_in[READ]);
		close(child_out[WRITE]);

		pipe_send = child_in[WRITE];
		const int pipe_receive = child_out[READ];
		file_receive = fdopen(pipe_receive, "r");
		return;
	}
	close(STDIN_FILENO);
	close(STDOUT_FILENO);
	dup2(child_in[READ], STDIN_FILENO);
	dup2(child_out[WRITE], STDOUT_FILENO);
	close(child_in[WRITE]);
	close(child_out[READ]);

	// Launch the program directly (no shell), passing the annotation arguments as
	// its command-line arguments.
	std::vector<char*> argv;
	argv.push_back(const_cast<char*>(program.c_str()));
	for (const std::string& a : args) {
		argv.push_back(const_cast<char*>(a.c_str()));
	}
	argv.push_back(nullptr);
	execvp(program.c_str(), argv.data());
	// execvp only returns on failure.
	std::exit(127);
#endif
};

BlackBoxExec::~BlackBoxExec() {
#ifdef _WIN32
	CloseHandle(pipe_send);
	CloseHandle(pipe_receive);
#else
	close(pipe_send);
	fclose(file_receive);
#endif
}

void BlackBoxExec::run(const std::vector<int64_t>& int_in, const std::vector<double>& float_in,
											 std::vector<int64_t>& int_out, std::vector<double>& float_out) {
	// Construct program input: comma-separated integers, a semicolon, then
	// comma-separated floats, terminated by a newline (e.g. "5,-7;2.5,1.125\n").
	std::stringstream out;
	out.precision(std::numeric_limits<double>::max_digits10);
	for (size_t i = 0; i < int_in.size(); ++i) {
		if (i != 0) {
			out << ",";
		}
		out << int_in[i];
	}
	out << ";";
	for (size_t i = 0; i < float_in.size(); ++i) {
		if (i != 0) {
			out << ",";
		}
		out << float_in[i];
	}
	out << "\n";
	const std::string out_buf = out.str();
#ifdef _WIN32
	// Write to process input pipe
	BOOL success = WriteFile(pipe_send, out_buf.c_str(), out_buf.size(), nullptr, nullptr);
	assert(success);

	// Read output from process by pipe
	char c[2] = {0, 0};
	std::ostringstream oss;
	while (c[0] != '\n') {
		DWORD count = 0;
		BOOL success = ReadFile(pipe_receive, c, sizeof(c) - 1, &count, NULL);
		if (!success) {
			throw std::string(
					"BlackBoxExec: Reading blackbox process output from pipe resulted did not succeed");
		} else if (count == 0) {
			throw std::string("BlackBoxExec: Blackbox process provided an incomplete response");
		}
		assert(count == 1);
		oss << c[0];
	}
	const std::string in_buffer(oss.str());
#else
	// Write to process input pipe
	const ssize_t bytes_written = write(pipe_send, out_buf.c_str(), out_buf.size());
	if (bytes_written != static_cast<ssize_t>(out_buf.size())) {
		throw std::string("BlackBoxExec: failed to write the full request to the blackbox process.");
	}

	// Read from process output pipe
	char* str = nullptr;
	size_t size = 0;

	if (getline(&str, &size, file_receive) == -1) {
		throw std::string(
				"BlackBoxExec: Reading blackbox process output from pipe resulted in error no. " +
				std::to_string(errno));
	}
	const std::string in_buffer(str);
	free(str);
#endif
	// Parse the response in a single left-to-right pass: comma-separated
	// integers, a semicolon, then comma-separated floats (e.g. "5,-7;2.5,1.125\n").
	const char* p = in_buffer.c_str();
	// NOLINTNEXTLINE(misc-const-correctness): out-parameter for strtoll/strtod (char**)
	char* end = nullptr;
	auto skip_ws = [](const char*& q) {
		while (*q == ' ' || *q == '\t' || *q == '\r') {
			++q;
		}
	};
	for (size_t i = 0; i < int_out.size(); ++i) {
		const long long v = std::strtoll(p, &end, 10);
		if (end == p) {
			throw std::string("BlackBoxExec: Failed to read output integer " + std::to_string(i) +
												" from blackbox process output, " + std::to_string(int_out.size()) +
												" integer values where expected.");
		}
		int_out[i] = static_cast<int64_t>(v);
		p = end;
		skip_ws(p);
		if (*p == ',') {
			++p;
		}
	}
	skip_ws(p);
	if (*p != ';') {
		throw std::string(
				"BlackBoxExec: Blackbox process response is missing the "
				"`;' separator between the integer and floating point "
				"outputs.");
	}
	++p;
	for (size_t i = 0; i < float_out.size(); ++i) {
		const double v = std::strtod(p, &end);
		if (end == p) {
			throw std::string("BlackBoxExec: Failed to read output float " + std::to_string(i) +
												" from blackbox process output, " + std::to_string(float_out.size()) +
												" floating point values where expected.");
		}
		float_out[i] = v;
		p = end;
		skip_ws(p);
		if (*p == ',') {
			++p;
		}
	}
}

template <int U = 0, int V = 0>
class BlackBox : public Propagator {
public:
	const int sz_in;
	const int sz_out;
	IntView<U>* int_input;
	IntView<V>* int_output;
	BlackBoxFn* bb_fn;

	BlackBox(vec<IntView<U>> _int_input, vec<IntView<V>> _int_output, BlackBoxFn* _bb_fn)
			: sz_in(_int_input.size()),
				sz_out(_int_output.size()),
				int_input(_int_input.release()),
				int_output(_int_output.release()),
				bb_fn(_bb_fn) {
		priority = 5;
		for (int i = 0; i < sz_in; ++i) {
			int_input[i].attach(this, i, EVENT_F);
		}
	}

	bool propagate() override {
		// std::cerr << "Black Box Fn input: ";
		std::vector<int64_t> int_in(sz_in);
		for (int i = 0; i < sz_in; ++i) {
			if (!int_input[i].isFixed()) {
				// std::cerr << "(cancelled: not all fixed)\n";
				return true;
			}
			// std::cerr << int_input[i].val() << " ";
			int_in[i] = int_input[i].getVal();
		}
		std::vector<int64_t> int_out(sz_out);

		const std::vector<double> float_in(0);
		std::vector<double> float_out(0);

		bb_fn->run(int_in, float_in, int_out, float_out);

		// std::cerr << "Black Box Fn output: ";
		Clause* reason = nullptr;
		for (int i = 0; i < sz_out; i++) {
			// std::cerr << int_out[i] << " ";
			const int val = check_int(int_out[i], "value output", i);
			if (int_output[i].setValNotR(val)) {
				if (reason == nullptr) {
					reason = Reason_new(sz_in + 1);
					for (int j = 0; j < sz_in; ++j) {
						(*reason)[j + 1] = int_input[j].getValLit();
					}
				}

				if (!int_output[i].setVal(val, reason)) {
					return false;
				}
			}
		}
		// std::cerr << std::endl;

		return true;
	}
};

template <int U = 0, int V = 0>
class BlackBoxBounds : public Propagator {
public:
	const int sz;
	IntView<U>* x;
	std::vector<std::vector<std::pair<int, PropBnd>>> reason;
	BlackBoxFn* bb_fn;

	BlackBoxBounds(vec<IntView<U>> _x, std::vector<std::vector<std::pair<int, PropBnd>>> _reason,
								 BlackBoxFn* _bb_fn)
			: sz(_x.size()), x(_x.release()), reason(std::move(_reason)), bb_fn(_bb_fn) {
		priority = 5;
		// Attach only to the specific bounds the propagator based on the possible
		// reason: a lower bound literal (PR_LB) means the propagator reads that
		// bound, so it should wake on a lower-bound (EVENT_L); likewise (PR_UB)
		// enables (EVENT_U). Empty reason falls back to both bounds for all
		// variables.
		const bool any =
				std::any_of(reason.begin(), reason.end(),
										[](const std::vector<std::pair<int, PropBnd>>& part) { return !part.empty(); });
		std::vector<int> events(sz, 0);
		for (const auto& part : reason) {
			for (const auto& lit : part) {
				events[lit.first] |= (lit.second == PR_LB ? EVENT_L : EVENT_U);
			}
		}
		for (int i = 0; i < sz; ++i) {
			const int ev = any ? events[i] : EVENT_LU;
			if (ev != 0) {
				x[i].attach(this, i, ev);
			}
		}
	}

	Clause* create_reason(int i, PropBnd b) {
		const std::vector<std::pair<int, PropBnd>>& my_reason = reason[(i * 2) + (b - 1)];
		Clause* reason = Reason_new(my_reason.size() + 1);
		for (size_t j = 0; j < my_reason.size(); ++j) {
			const std::pair<int, PropBnd>& term = my_reason[j];
			(*reason)[static_cast<int>(j) + 1] =
					term.second == PR_LB ? x[term.first].getMinLit() : x[term.first].getMaxLit();
		}
		return reason;
	}

	bool propagate() override {
		// std::cerr << "Black Box Fn input: ";
		std::vector<int64_t> bounds_in(static_cast<size_t>(sz) * 2);
		for (int i = 0; i < sz; ++i) {
			// std::cerr << x[i].getMin() << " " << x[i].getMax() << " ";
			const size_t idx = static_cast<size_t>(i) * 2;
			bounds_in[idx] = x[i].getMin();
			bounds_in[idx + 1] = x[i].getMax();
		}
		// std::cerr << std::endl;
		std::vector<int64_t> bounds_out(static_cast<size_t>(sz) * 2);

		const std::vector<double> float_in(0);
		std::vector<double> float_out(0);

		bb_fn->run(bounds_in, float_in, bounds_out, float_out);

		// std::cerr << "Black Box Fn output: ";
		for (int i = 0; i < sz; i++) {
			// std::cerr << bounds_out[i*2] << " " << bounds_out[i*2+1] << " ";
			const size_t idx = static_cast<size_t>(i) * 2;
			const int lb = check_int(bounds_out[idx], "bounds output", i);
			const int ub = check_int(bounds_out[idx + 1], "bounds output", i);
			if (x[i].setMinNotR(lb)) {
				if (!x[i].setMin(lb, create_reason(i, PR_LB))) {
					return false;
				}
			}
			if (x[i].setMaxNotR(ub)) {
				if (!x[i].setMax(ub, create_reason(i, PR_UB))) {
					return false;
				}
			}
		}
		// std::cerr << std::endl;

		return true;
	}
};

void blackbox(vec<IntVar*>& int_in, vec<IntVar*>& int_out, const std::string& mode,
							const std::string& instantiation, const std::vector<std::string>& args) {
	// NOLINTNEXTLINE(misc-const-correctness): handed to a propagator that calls the non-const run()
	BlackBoxFn* black_box(nullptr);
	if (mode == "dll") {
		black_box = new BlackBoxDLL(instantiation, args);
	} else if (mode == "exec") {
		black_box = new BlackBoxExec(instantiation, args);
	} else {
		throw std::string("blackbox: unknown blackbox protocol `" + mode + "'");
	}

	vec<IntView<>> in_view;
	for (unsigned int i = 0; i < int_in.size(); i++) {
		in_view.push(IntView<>(int_in[i]));
	}

	vec<IntView<>> out_view;
	for (unsigned int i = 0; i < int_out.size(); i++) {
		out_view.push(IntView<>(int_out[i]));
	}

	new BlackBox<>(in_view, out_view, black_box);
}

void blackbox_bounds(vec<IntVar*>& ivar, std::vector<std::vector<std::pair<int, PropBnd>>> reason,
										 const std::string& mode, const std::string& instantiation,
										 const std::vector<std::string>& args) {
	// NOLINTNEXTLINE(misc-const-correctness): handed to a propagator that calls the non-const run()
	BlackBoxFn* black_box(nullptr);
	if (mode == "dll") {
		black_box = new BlackBoxDLL(instantiation, args);
	} else if (mode == "exec") {
		black_box = new BlackBoxExec(instantiation, args);
	} else {
		throw std::string("blackbox: unknown blackbox protocol `" + mode + "'");
	}

	vec<IntView<>> views;
	for (unsigned int i = 0; i < ivar.size(); i++) {
		views.push(IntView<>(ivar[i]));
	}

	new BlackBoxBounds<>(views, std::move(reason), black_box);
}
