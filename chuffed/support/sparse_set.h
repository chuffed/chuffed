#ifndef SPARSE_SET_H_
#define SPARSE_SET_H_
// U indicates whether to use FAST_FSET.

#include <chuffed/core/engine.h>

#include <cassert>
#include <cstdlib>

template <int U = 0>
class SparseSet {
public:
	SparseSet() : dom(0), sparse(nullptr), dense(nullptr), members(0) {}

	SparseSet(unsigned int size)
			: dom(size),
				sparse((unsigned int*)malloc(size * sizeof(unsigned int))),
				dense((unsigned int*)malloc(size * sizeof(unsigned int))),
				members(0) {
		if ((U & 1) != 0) {
			assert(members == 0);
			for (unsigned int i = 0; i < dom; i++) {
				sparse[i] = i;
				dense[i] = i;
			}
		}
	}

	~SparseSet() {
		if (sparse != nullptr) {
			free(sparse);
		}
		if (dense != nullptr) {
			free(dense);
		}
	}

	bool elem(unsigned int value) const {
		if ((U & 1) != 0) {
			return (sparse[value] < members);
		}
		unsigned int a = sparse[value];

		if (a < members && dense[a] == value) {
			return true;
		}
		return false;
	}

	bool elemLim(unsigned int lim, unsigned int el) { return (sparse[el] < lim) && elem(el); }

	virtual bool insert(unsigned int value) {
		if ((U & 1) != 0) {
			unsigned int old_dense = sparse[value];
			unsigned int lost_val = dense[members];

			sparse[value] = members;
			dense[members] = value;

			sparse[lost_val] = old_dense;
			dense[old_dense] = lost_val;
		} else {
			assert(!elem(value));

			sparse[value] = members;
			dense[members] = value;
		}
		members++;

		return true;
	}

	void clear() { members = 0; }

	unsigned int pos(unsigned int val) const {
		assert(elem(val));
		return sparse[val];
	}

	unsigned int operator[](unsigned int index) {
		assert(index < members);
		return dense[index];
	}

	void growTo(unsigned int sz) {
		if (sz > dom) {
			sparse = (unsigned int*)realloc(sparse, sizeof(unsigned int) * sz);
			dense = (unsigned int*)realloc(dense, sizeof(unsigned int) * sz);

			if ((U & 1) != 0) {
				assert(members == 0);
				for (; dom < sz; dom++) {
					sparse[dom] = dom;
					dense[dom] = dom;
				}
			}
		}
	}

	unsigned int size() { return members; }

	unsigned int domain() { return dom; }

protected:
	unsigned int dom;
	unsigned int* sparse;
	unsigned int* dense;
	unsigned int members;
};

class TrailedSet : public SparseSet<0> {
public:
	TrailedSet(int sz) : SparseSet<0>(sz) {}

	bool insert(int value) {
		// Assumes not FFSET.
		assert(!elem(value));

		sparse[value] = members;
		dense[members] = value;

		trailChange(members, members + 1);

		return true;
	}
};

// Variant of a trailed sparse set which
// only trails at the end of a series of operations.
class DeferredSet : public SparseSet<0> {
public:
	DeferredSet(int sz) : SparseSet<0>(sz) {}

	// Ensure members is given the correct value.
	inline void refresh() { members = stored; }

	inline void commit() {
		if (stored != members) {
			trailChange(stored, members);
		}
	}

protected:
	unsigned int stored;
};
#endif
