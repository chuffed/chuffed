#ifndef BITVEC_H_
#define BITVEC_H_

#include "chuffed/core/engine.h"

#include <cassert>
#include <cstdlib>
/************************************************
 * Classes for bit-vector and k-width bit-vector.
 * Warning: doesn't do any bounds checking.
 * Also, don't use the push/pop interface with growTo.
 * Since pop doesn't reset the value, successive growTo
 * calls may leave some ghost elements.
 ************************************************/
template <unsigned int B>
struct BitMask {
	enum { value = 2 * BitMask<B - 1>::value + 1 };
};

template <>
struct BitMask<0> {
	enum { value = 0 };
};

template <class T = unsigned int, unsigned int B = 1>
class ValVec {
public:
	static const unsigned int eltsT = (8 * sizeof(T)) / B;
	static const unsigned int mask = BitMask<B>::value;

	ValVec(unsigned int i = 0) : elts(i), sz(1 + (i / eltsT)), data((T*)malloc(sizeof(T) * sz)) {
		for (unsigned int ii = 0; ii < sz; ii++) {
			data[ii] = 0;
		}
	}

	~ValVec() { free(data); }

	unsigned int operator[](unsigned int el) {
		unsigned int shift = B * (el % eltsT);
		return (data[el / eltsT] & (mask << shift)) >> shift;
	}

	bool elem(unsigned int el) { return data[el / eltsT] & (mask << (B * (el % eltsT))); }

	void set(unsigned int el, unsigned int val) {
		T Smask = ~(mask << (B * (el % eltsT)));
		data[el / eltsT] = (data[el / eltsT] & Smask) | val << (B * (el % eltsT));
	}

	void push(unsigned int val) {
		if (elts + 1 >= sz * eltsT) {
			unsigned int newsz = 2 * sz;
			data = (T*)realloc(data, sizeof(T) * sz);
			for (; sz < newsz; sz++) {
				data[sz] = 0;
			}
		}

		set(elts, val);
		elts++;
	}

	unsigned int pop() {
		assert(elts > 0);
		elts--;
		return (*this)[elts];
	}

	unsigned int size() { return elts; }

protected:
	unsigned int elts;
	unsigned int sz;
	T* data;
};

template <class T = unsigned int>
class BitVec {
public:
	static const unsigned int eltsT = 8 * sizeof(T);

	BitVec(unsigned int i = 0) : elts(i), sz(1 + (i / eltsT)), data((T*)malloc(sizeof(T) * sz)) {
		for (unsigned int ii = 0; ii < sz; ii++) {
			data[ii] = 0;
		}
	}

	~BitVec() { free(data); }

	bool operator[](unsigned int el) { return elem(el); }

	bool elem(unsigned int el) { return data[el / eltsT] & (1 << (el % eltsT)); }

	void insert(unsigned int el) { data[el / eltsT] |= 1 << (el % eltsT); }

	void remove(unsigned int el) { data[el / eltsT] &= ~(1 << (el % eltsT)); }

	void push(bool val) {
		if (elts + 1 >= sz * eltsT) {
			unsigned int newsz = sz * 2;
			data = (T*)realloc(data, sizeof(T) * newsz);
			for (; sz < newsz; sz++) {
				data[sz] = 0;
			}
		}

		if (val) {
			insert(elts);
		} else {
			remove(elts);
		}
		elts++;
	}

	void growTo(unsigned int newsz) {
		if (newsz > sz * eltsT) {
			sz = 1 + newsz / eltsT;
			data = (T*)realloc(data, sizeof(T) * sz);
		}
	}

	bool pop() {
		assert(elts > 0);

		elts--;
		return elem(elts);
	}

	unsigned int size() { return elts; }

protected:
	unsigned int elts;
	unsigned int sz;
	T* data;
};

// Trailed variant of the bit-vector.
// template<class T = unsigned int>
class TBitVec : public BitVec<unsigned int> {
public:
	TBitVec(unsigned int i = 0) : BitVec<unsigned int>(i) {}

	void insert(unsigned int el) {
		trailChange(data[el / eltsT], data[el / eltsT] | 1 << (el % eltsT));
	}
};

#endif
