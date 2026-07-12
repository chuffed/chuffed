#ifndef BLACKBOX_H
#define BLACKBOX_H

#include <cstddef>
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
	virtual ~BlackBoxFn() = default;
	virtual void run(const std::vector<int64_t>& int_in, const std::vector<double>& float_in,
									 std::vector<int64_t>& int_out, std::vector<double>& float_out) = 0;
};

/// Implementation of a black box function that dynamically loads a library and
/// runs a contained function.
///
/// A library exporting `fzn_init` creates a per-constraint instance that is
/// passed to every `fzn_blackbox` call and released with `fzn_free`; such a
/// library must also export `fzn_clone`. A library without `fzn_init` is
/// stateless and receives a null instance. Chuffed is single-threaded, so the
/// root instance is used directly and never cloned.
class BlackBoxDLL : public BlackBoxFn {
public:
	BlackBoxDLL(const std::string& name, const std::vector<std::string>& args);
	~BlackBoxDLL() override;
	void run(const std::vector<int64_t>& int_in, const std::vector<double>& float_in,
					 std::vector<int64_t>& int_out, std::vector<double>& float_out) override;

protected:
	void* library;
	void* root_instance;
	void(__stdcall* dll_fzn_blackbox)(void*, const int64_t*, size_t, const double*, size_t, int64_t*,
																		size_t, double*, size_t);
	void(__stdcall* dll_fzn_free)(void*);
};

/// Implementation of a black function that starts a seperate process to
/// repeatedly run a blackbox function, communication I/O over pipe.
class BlackBoxExec : public BlackBoxFn {
public:
	BlackBoxExec(const std::string& program, const std::vector<std::string>& args);
	~BlackBoxExec() override;
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
