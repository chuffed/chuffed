#ifndef CIRCUTIL_H
#define CIRCUTIL_H

#include <unordered_map>

#define SEED 0xdeadbeef

extern int stat_count;

// Utility stuff
template <class S>
struct AutoS {
	struct eq {
		bool operator()(const S& a, const S& b) const {
			if (sizeof(S) % sizeof(uint32_t) == 0) {
				auto* ap((uint32_t*)&a);
				auto* bp((uint32_t*)&b);
				for (unsigned int ii = 0; ii < sizeof(S) / sizeof(uint32_t); ii++) {
					if (ap[ii] != bp[ii]) {
						return false;
					}
				}
				return true;
			}
			char* ap((char*)&a);
			char* bp((char*)&b);
			for (unsigned int ii = 0; ii < sizeof(S); ii++) {
				if (ap[ii] != bp[ii]) {
					return false;
				}
			}
			return true;
		}
	};

	struct hash {
		unsigned int operator()(const S& s) const {
			uint32_t ret;
			MurmurHash3_x86_32(&s, sizeof(S), SEED, &ret);
			return ret;
		}
	};
};

template <class S, class V>
struct AutoC {
	typedef std::unordered_map<const S, V, typename AutoS<S>::hash, typename AutoS<S>::eq> cache;
	//  typedef std::tr1::unordered_map<const S, V, typename AutoS<S>::hash, typename AutoS<S>::eq>
	//  cache;
};

/*
template<class T>
inline T imax(const T a, const T b)
{
	return a < b ? b : a;
}

template<class T>
inline T imin(const T a, const T b)
{
	return a < b ? a : b;
}

inline int ceil(int a, int b)
{
	return (a % b) ? (a/b)+1 : (a/b);
}
*/
#endif
