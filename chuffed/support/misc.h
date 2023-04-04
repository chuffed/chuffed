#ifndef misc_h
#define misc_h

#include <cassert>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <ctime>

#ifdef WIN32
#ifdef HAS_PROFILER
#include <winsock2.h>
#endif
#include <windows.h>
#define SEP_ '\\'
#else
#include <sys/time.h>
#include <unistd.h>
#define SEP_ '/'
#endif

#include <chuffed/support/vec.h>

#include <cstdint>

extern uint64_t bit[65];

// #define low(s) ((int)(s))
// #define high(s) ((int)((s) >> 32))
#define inSet(i, s) (bit[(i)] & (s))
#define getbit(i, s) (((s) >> (i)) & 1)

//------
#ifdef NDEBUG
#define FILENAME_ (strrchr(__FILE__, SEP_) ? strrchr(__FILE__, SEP_) + 1 : __FILE__)
#else
#define FILENAME_ __FILE__
#endif
#define CHUFFED_ERROR(...)                           \
	do {                                               \
		fprintf(stderr, "%s:%d: ", FILENAME_, __LINE__); \
		fprintf(stderr, __VA_ARGS__);                    \
		abort();                                         \
	} while (0)

#define NOT_SUPPORTED CHUFFED_ERROR("Not yet supported\n")
#define NEVER CHUFFED_ERROR("Assertion failed.\n")

// Run time assert
#define rassert(expr)                                              \
	do {                                                             \
		if (!(expr)) CHUFFED_ERROR("Assertion `%s' failed.\n", #expr); \
	} while (0)

// Compile time assert, adapted from Boost library
template <int x>
struct static_assert_test {};
template <bool b>
struct STATIC_ASSERTION_FAILURE;
template <>
struct STATIC_ASSERTION_FAILURE<true> {
	enum { value = 1 };
};
#define BOOST_JOIN(X, Y) BOOST_DO_JOIN(X, Y)
#define BOOST_DO_JOIN(X, Y) BOOST_DO_JOIN2(X, Y)
#define BOOST_DO_JOIN2(X, Y) X##Y
#define cassert(expr)                                                                    \
	typedef static_assert_test<sizeof(STATIC_ASSERTION_FAILURE<(bool)(expr)>)> BOOST_JOIN( \
			boost_static_assert_typedef_, __LINE__)

#define TL_FAIL()                        \
	do {                                   \
		printf("=====UNSATISFIABLE=====\n"); \
		printf("%% Top level failure!\n");   \
		exit(0);                             \
	} while (0)

//------

#define MYRAND_MAX 4294967296.0

//------

using chuffed_clock = std::chrono::steady_clock;
using time_point = std::chrono::time_point<chuffed_clock>;
using duration = std::chrono::milliseconds;

static inline double to_sec(duration d) {
	return std::chrono::duration_cast<std::chrono::duration<double>>(d).count();
}

template <class T>
static inline int bitcount(T s) {
	int c = 0;
	while (s) {
		s &= s - 1;
		c++;
	}
	return c;
}

static inline double wallClockTime() {
#ifdef WIN32
	static const unsigned __int64 epoch = ((unsigned __int64)116444736000000000ULL);
	FILETIME file_time;
	SYSTEMTIME system_time;
	ULARGE_INTEGER ularge;

	GetSystemTime(&system_time);
	SystemTimeToFileTime(&system_time, &file_time);
	ularge.LowPart = file_time.dwLowDateTime;
	ularge.HighPart = file_time.dwHighDateTime;

	long sec = (ularge.QuadPart - epoch) / 10000000L;
	long msec = system_time.wMilliseconds;
	return (double)sec + (double)msec / 1000;
#else
	struct timeval tp;
	gettimeofday(&tp, nullptr);
	return (double)tp.tv_sec + (double)tp.tv_usec / 1000000;
#endif
}

/*
static inline double wallClockTime() {
	return (double) time(NULL);
}
*/

static int mylog2(int val) {
	int ret = -1;
	while (val != 0) {
		val >>= 1;
		ret++;
	}
	return ret;
}

static double memUsed() {
	return 0;
	/* char name[256]; */
	/* sprintf(name, "/proc/%d/statm", getpid()); */
	/* FILE* in = fopen(name, "rb"); */
	/* if (in == NULL) return 0; */
	/* int value; */
	/* rassert(fscanf(in, "%d", &value) == 1); */
	/* fclose(in); */
	/* return (double) value * getpagesize() / 1048576; */
}

template <class T>
static T** new2d(int n, int m) {
	T** a = new T*[n];
	T* b = new T[n * m];
	for (int i = 0; i < n; i++) {
		a[i] = b + i * m;
	}
	return a;
}

template <class T, class U>
T conv(const U& x) {
	static_assert(sizeof(T) == sizeof(U), "Must bit-cast between values of equal size.");
	T ret;
	memcpy(&ret, &x, sizeof(U));
	return ret;
}

#endif
