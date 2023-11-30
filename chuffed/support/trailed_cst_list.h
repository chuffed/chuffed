#ifndef TRAILED_CST_LIST_H
#define TRAILED_CST_LIST_H

#include "chuffed/branching/branching.h"

#include <cassert>
#include <iostream>
#include <vector>
template <class T, typename E = Tint>
class TrailedConstantAccessList {
protected:
	int max_size;
	std::vector<int> sparse;
	std::vector<T> dense;

	/*T*/ E size;

public:
	TrailedConstantAccessList(int n) : max_size(n) {
		sparse = std::vector<int>(max_size, -1);
		dense = std::vector<T>(max_size);
		size = 0;
	}

	~TrailedConstantAccessList() = default;

	virtual int key(T k) = 0;

	bool get(int k, T* val = nullptr) {
		if (k < 0 || k >= max_size) {
			return false;
		}
		if (sparse[k] > -1 && sparse[k] < size) {
			if (key(dense[sparse[k]]) != k) {
				return false;
			}
			if (val != nullptr) {
				*val = dense[sparse[k]];
			}
			return true;
		}
		return false;
	}

	void add(T val) {
		int k = key(val);
		assert(k >= 0 && k < max_size);
		assert(size < max_size);
		if (!get(k)) {
			sparse[k] = size;
			dense[size] = val;
			size++;
		}
	}

	template <typename ValueType>
	class Iterator {
		friend TrailedConstantAccessList;
		TrailedConstantAccessList* l;
		int i;

	public:
		Iterator(int _i = 0) : l(nullptr), i(_i) {}
		Iterator(TrailedConstantAccessList* _l, int _i = 0) : l(_l), i(_i) {}
		Iterator& operator++() {
			i++;
			return *this;
		}
		Iterator& operator--() {
			i--;
			return *this;
		}
		Iterator& operator++(int dummy) {
			++i;
			return *this;
		}
		Iterator& operator--(int dummy) {
			--i;
			return *this;
		}
		bool operator==(Iterator<ValueType> o) { return o.l == this->l && o.i == this->i; }
		bool operator!=(Iterator<ValueType> o) { return o.l != this->l || o.i != this->i; }
		ValueType& operator*() { return l->dense[i]; }
	};

	// typedef Iterator<T> iterator;
	using const_iterator = Iterator<const T>;
	const_iterator begin() { return Iterator<const T>(this, 0); }
	const_iterator end() { return Iterator<const T>(this, size); }
};

#endif
