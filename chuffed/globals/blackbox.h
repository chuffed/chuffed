#ifndef BLACKBOX_H
#define BLACKBOX_H

#include <cstdint>
#include <string>
#include <vector>

#ifdef _WIN32
#ifdef HAS_PROFILER
#include <winsock2.h>
#endif
#define NOMINMAX  // Ensure the words min/max remain available
#include <Windows.h>
#else
// NOLINTNEXTLINE(bugprone-reserved-identifier)
#define __stdcall
#endif

/// Abstract class implemented by different methods to run blackbox functions
class BlackBoxFn {
public:
	virtual void run(const std::vector<int64_t>& int_in, const std::vector<double>& float_in,
									 std::vector<int64_t>& int_out, std::vector<double>& float_out) = 0;
};

/// Implementation of a black box function that dynamically loads a library and
/// run a contained function.
class BlackBoxDLL : public BlackBoxFn {
public:
	BlackBoxDLL(const std::string& name, const std::vector<std::string>& args);
	~BlackBoxDLL();
	void run(const std::vector<int64_t>& int_in, const std::vector<double>& float_in,
					 std::vector<int64_t>& int_out, std::vector<double>& float_out) override {
		dll_fzn_blackbox(int_in.data(), int_in.size(), float_in.data(), float_in.size(), int_out.data(),
										 int_out.size(), float_out.data(), float_out.size());
	}

protected:
	void* library;
	void(__stdcall* dll_fzn_blackbox)(const int64_t*, size_t, const double*, size_t, int64_t*, size_t,
																		double*, size_t);
};

/// Implementation of a black function that starts a seperate process to
/// repeatedly run a blackbox function, communication I/O over pipe.
class BlackBoxExec : public BlackBoxFn {
public:
	BlackBoxExec(const std::string& program, const std::vector<std::string>& args);
	~BlackBoxExec();
	void run(const std::vector<int64_t>& int_in, const std::vector<double>& float_in,
					 std::vector<int64_t>& int_out, std::vector<double>& float_out) override;

protected:
#ifdef _WIN32
	HANDLE pipe_send;
	HANDLE pipe_receive;
#else
	int pipe_send;
	FILE* file_receive;
#endif
};

enum PropBnd : std::uint8_t {
	PR_LB = 1,
	PR_UB = 2,
};

#endif
