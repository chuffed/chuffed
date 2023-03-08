#ifndef vec_h
#define vec_h

#include <cassert>
#include <cstdlib>

template <class T>
class vec {
	int sz;
	int cap;
	T* data;

public:
	// Constructors:
	vec() : sz(0), cap(0), data(nullptr) {}
	vec(int _sz) : sz(_sz), cap(sz) {
		data = sz != 0 ? (T*)malloc(cap * sizeof(T)) : nullptr;
		for (int i = 0; i < sz; i++) {
			new (&data[i]) T();
		}
	}
	vec(int _sz, const T& pad) : sz(_sz), cap(sz) {
		data = sz != 0 ? (T*)malloc(cap * sizeof(T)) : nullptr;
		for (int i = 0; i < sz; i++) {
			new (&data[i]) T(pad);
		}
	}
	template <class U>
	vec(vec<U>& other) : sz(other.size()), cap(sz) {
		assert(sizeof(U) == sizeof(T));
		data = (T*)malloc(cap * sizeof(T));
		for (int i = 0; i < sz; i++) {
			new (&data[i]) T(other[i]);
		}
		//		for (int i = 0; i < sz; i++) data[i] = other[i];
	}

	~vec() {
		for (int i = 0; i < sz; i++) {
			data[i].~T();
		}
		if (data) {
			free(data);
		}
		data = nullptr;
	}

	// Size operations:
	int size() const { return sz; }
	int& _size() { return sz; }
	int capacity() const { return cap; }
	void resize(int nelems) {
		assert(nelems <= sz);
		for (int i = nelems; i < sz; i++) {
			data[i].~T();
		}
		sz = nelems;
	}
	void shrink(int nelems) {
		assert(nelems <= sz);
		resize(sz - nelems);
	}
	void pop() { data[--sz].~T(); }

	// Stack interface:
	void push() {
		if (sz == cap) {
			cap = imax(2, (cap * 3 + 1) >> 1);
			data = (T*)realloc(data, cap * sizeof(T));
		}
		new (&data[sz++]) T();
	}
	void push(const T& elem) {
		if (sz == cap) {
			cap = imax(2, (cap * 3 + 1) >> 1);
			data = (T*)realloc(data, cap * sizeof(T));
		}
		new (&data[sz++]) T(elem);
	}

	const T& last() const { return data[sz - 1]; }
	T& last() { return data[sz - 1]; }

	// Vector interface:
	const T& operator[](int index) const { return data[index]; }
	T& operator[](int index) { return data[index]; }

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
		for (int i = 0; i < sz; i++) {
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

	int imin(int x, int y) {
		int mask = ((x - y) >> 31);
		return (x & mask) + (y & (~mask));
	}

	int imax(int x, int y) {
		int mask = ((y - x) >> 31);
		return (x & mask) + (y & (~mask));
	}

	void reserve(int size) {
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

	void growTo(int size) {
		if (size <= sz) {
			return;
		}
		reserve(size);
		for (int i = sz; i < size; i++) {
			new (&data[i]) T();
		}
		sz = size;
	}

	void growTo(int size, const T& pad) {
		if (size <= sz) {
			return;
		}
		reserve(size);
		for (int i = sz; i < size; i++) {
			new (&data[i]) T(pad);
		}
		sz = size;
	}

	void growBy(int extra, const T& pad = T()) { growTo(sz + extra, pad); }

	void clear(bool dealloc = false) {
		if (!data) {
			return;
		}
		for (int i = 0; i < sz; i++) {
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
		int j;
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
	int sz;
	int cap;
	int head;
	int tail;
	bool fifo;
	T* data;

	queue() : sz(0), cap(10), head(0), tail(0), fifo(false) { data = (T*)malloc(cap * sizeof(T)); }

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
