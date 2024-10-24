#ifndef vec_h
#define vec_h

#include <algorithm>
#include <cassert>
#include <cstdlib>

template <class T>
class vec {
	unsigned int sz;
	unsigned int cap;
	T* data;

public:
	// Constructors:
	vec() : sz(0), cap(0), data(nullptr) {}
	vec(unsigned int _sz) : sz(_sz), cap(sz) {
		data = sz != 0 ? (T*)malloc(cap * sizeof(T)) : nullptr;
		for (unsigned int i = 0; i < sz; i++) {
			new (&data[i]) T();
		}
	}
	vec(unsigned int _sz, const T& pad) : sz(_sz), cap(sz) {
		data = sz != 0 ? (T*)malloc(cap * sizeof(T)) : nullptr;
		for (unsigned int i = 0; i < sz; i++) {
			new (&data[i]) T(pad);
		}
	}
	template <class U>
	vec(vec<U>& other) : sz(other.size()), cap(sz) {
		assert(sizeof(U) == sizeof(T));
		data = (T*)malloc(cap * sizeof(T));
		for (unsigned int i = 0; i < sz; i++) {
			new (&data[i]) T(other[i]);
		}
		//		for (int i = 0; i < sz; i++) data[i] = other[i];
	}

	~vec() {
		for (unsigned int i = 0; i < sz; i++) {
			data[i].~T();
		}
		if (data) {
			free(data);
		}
		data = nullptr;
	}

	// Size operations:
	unsigned int size() const { return sz; }
	unsigned int& _size() { return sz; }
	unsigned int capacity() const { return cap; }
	void resize(unsigned int nelems) {
		assert(nelems <= sz);
		for (unsigned int i = nelems; i < sz; i++) {
			data[i].~T();
		}
		sz = nelems;
	}
	void shrink(unsigned int nelems) {
		assert(nelems <= sz);
		resize(sz - nelems);
	}
	void pop() { data[--sz].~T(); }

	// Stack interface:
	void push() {
		if (sz == cap) {
			cap = std::max(2u, (cap * 3 + 1) >> 1);
			data = (T*)realloc(data, cap * sizeof(T));
		}
		new (&data[sz++]) T();
	}
	void push(const T& elem) {
		if (sz == cap) {
			cap = std::max(2u, (cap * 3 + 1) >> 1);
			data = (T*)realloc(data, cap * sizeof(T));
		}
		new (&data[sz++]) T(elem);
	}

	const T& last() const { return data[sz - 1]; }
	T& last() { return data[sz - 1]; }

	// Vector interface:
	const T& operator[](unsigned int index) const { return data[index]; }
	T& operator[](unsigned int index) { return data[index]; }

	// Raw access to data
	T* release() {
		T* ret = data;
		data = nullptr;
		sz = 0;
		cap = 0;
		return ret;
	}
	operator T*() { return data; }

	// Duplicatation (preferred instead):
	void copyTo(vec<T>& copy) const {
		copy.clear();
		copy.growTo(sz);
		for (unsigned int i = 0; i < sz; i++) {
			new (&copy[i]) T(data[i]);
		}
	}
	void moveTo(vec<T>& dest) {
		dest.clear(true);
		dest.data = data;
		dest.sz = sz;
		dest.cap = cap;
		data = nullptr;
		sz = 0;
		cap = 0;
	}

	void reserve(unsigned int size) {
		if (size > cap) {
			if (cap == 0) {
				cap = (size > 2) ? size : 2;
			} else {
				do {
					cap = (cap * 3 + 1) >> 1;
				} while (cap < size);
			}
			data = (T*)realloc(data, cap * sizeof(T));
		}
	}

	void growTo(unsigned int size) {
		if (size <= sz) {
			return;
		}
		reserve(size);
		for (unsigned int i = sz; i < size; i++) {
			new (&data[i]) T();
		}
		sz = size;
	}

	void growTo(unsigned int size, const T& pad) {
		if (size <= sz) {
			return;
		}
		reserve(size);
		for (unsigned int i = sz; i < size; i++) {
			new (&data[i]) T(pad);
		}
		sz = size;
	}

	void growBy(unsigned int extra, const T& pad = T()) { growTo(sz + extra, pad); }

	void clear(bool dealloc = false) {
		if (!data) {
			return;
		}
		for (unsigned int i = 0; i < sz; i++) {
			data[i].~T();
		}
		sz = 0;
		if (dealloc) {
			cap = 0;
			free(data);
			data = nullptr;
		}
	}

	void remove(const T& t) {
		unsigned int j;
		for (j = 0; j < sz && data[j] != t; j++) {
			;
		}
		if (j < sz) {
			data[j] = last();
			pop();
		}
	}
};

//-----

template <class T>
class queue {
public:
	unsigned int sz{0};
	unsigned int cap{10};
	unsigned int head{0};
	unsigned int tail{0};
	bool fifo{false};
	T* data;

	queue() { data = (T*)malloc(cap * sizeof(T)); }

	void reserve() {
		if (++sz == cap) {
			cap = cap * 3 / 2;
			data = (T*)realloc(data, cap * sizeof(T));
		}
	}

	bool empty() { return tail == head; }
	void push(const T& e) {
		data[tail++] = e;
		if (fifo && tail == cap) {
			tail = 0;
		}
	}
	T pop() {
		if (!fifo) {
			return data[--tail];
		}
		T& e = data[head++];
		if (head == cap) {
			head = 0;
		}
		return e;
	}
};

#endif
