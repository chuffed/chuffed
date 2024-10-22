#ifndef sat_types_h
#define sat_types_h

//=================================================================================================
// Variables, literals, lifted booleans, clauses:

// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

#include <cassert>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <new>

#define var_Undef (-1)

class Lit {
	int x;

public:
	Lit() : x(2 * var_Undef) {}  // (lit_Undef)
	explicit Lit(int var, bool sign = false) : x((var + var) + (int)sign) {}

	// Don't use these for constructing/deconstructing literals. Use the normal constructors instead.
	friend int toInt(Lit p);  // Guarantees small, positive integers suitable for array indexing.
	friend Lit toLit(int i);  // Inverse of 'toInt()'
	friend Lit operator~(Lit p);
	friend bool sign(Lit p);
	friend int var(Lit p);
	friend Lit unsign(Lit p);
	friend Lit id(Lit p, bool sgn);

	bool operator==(Lit p) const { return x == p.x; }
	bool operator!=(Lit p) const { return x != p.x; }
	bool operator<(Lit p) const {
		return x < p.x;
	}  // '<' guarantees that p, ~p are adjacent in the ordering.
	int operator^(Lit p) const { return x ^ p.x; }
};

inline int toInt(Lit p) { return p.x; }
inline Lit toLit(int i) {
	Lit p;
	p.x = i;
	return p;
}
inline Lit operator~(Lit p) {
	Lit q;
	q.x = p.x ^ 1;
	return q;
}
inline bool sign(Lit p) { return (p.x & 1) != 0; }
inline int var(Lit p) { return p.x >> 1; }
inline Lit unsign(Lit p) {
	Lit q;
	q.x = p.x & ~1;
	return q;
}
inline Lit id(Lit p, bool sgn) {
	Lit q;
	q.x = p.x ^ (int)sgn;
	return q;
}

const Lit lit_Undef(var_Undef, false);  // }- Useful special constants.
const Lit lit_Error(var_Undef, true);   // }
const Lit lit_False(0, false);
const Lit lit_True(0, true);

//=================================================================================================
// Lifted booleans:

class lbool {
	int8_t value;
	explicit lbool(int v) : value(v) {}

public:
	lbool() : value(0) {}
	lbool(bool x) : value((int)x * 2 - 1) {}
	int toInt() const { return value; }

	bool operator==(lbool b) const { return value == b.value; }
	bool operator!=(lbool b) const { return value != b.value; }
	lbool operator^(bool b) const { return b ? lbool(-value) : lbool(value); }

	friend int toInt(lbool l);
	friend lbool toLbool(int v);
};
inline int toInt(lbool l) { return l.toInt(); }
inline lbool toLbool(int v) { return lbool(v); }

const lbool l_True = toLbool(1);
const lbool l_False = toLbool(-1);
const lbool l_Undef = toLbool(0);

//=================================================================================================
// Clause -- a simple class for representing a clause:

class Clause {
public:
	unsigned int learnt : 1;     // is it a learnt clause
	unsigned int temp_expl : 1;  // is it a temporary explanation clause
	unsigned int padding : 6;    // save some bits for other bitflags
	unsigned int sz : 24;        // the size of the clause
	Lit data[1];                 // the literals of the clause
															 /* 	float data2[0]; */
															 /* int data3[0]; */
															 /* int data4[0]; */

	// NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
	template <class V>
	Clause(const V& ps, bool learnt) {
		assert(ps.size() < (1 << 24));
		clearFlags();
		sz = ps.size();
		this->learnt = learnt;
		for (int i = 0; i < ps.size(); i++) {
			data[i] = ps[i];
		}
	}

	// -- use this function instead:
	void clearFlags() {
		learnt = 0;
		temp_expl = 0;
	}
	int size() const { return sz; }

	void resize(unsigned int newSize) {
		// Careful of the order of operations here: don't overwrite sz
		// with newSize until we've copied the activities, and make sure
		// you copy data2 before data3 in case one would overwrite the
		// other.
		auto* data2 = (float*)data;
		int* data3 = (int*)data;
		int* data4 = (int*)data;
		if (learnt) {
			data2[newSize] = data2[sz];
			data3[newSize + 1] = data3[sz + 1];
			data4[newSize + 2] = data4[sz + 2];
		}
		sz = newSize;
	}

	Lit& operator[](int i) {
		if (i >= sz) {
			abort();
		}
		return data[i];
	}
	Lit operator[](int i) const { return data[i]; }
	operator const Lit*() const { return data; }

	float& activity() {
		auto* data2 = (float*)data;
		return data2[sz];
	}
	int& rawActivity() {
		int* data3 = (int*)data;
		return data3[sz + 1];
	}
	int& clauseID() {
		int* data4 = (int*)data;
		return data4[sz + 2];
	}

	void debug() const;
};

template <class V>
static Clause* Clause_new(const V& ps, bool learnt = false) {
	size_t s = 0;
	if (ps.size() != 0) {
		s = ps.size() - 1;
	}
	const int mem_size = sizeof(Clause) + s * sizeof(Lit) + (learnt ? 3 : 0) * sizeof(int);
	void* mem = malloc(mem_size);
	auto* newClause = new (mem) Clause(ps, learnt);
	return newClause;
}

//=================================================================================================
// LitFlags -- store info concerning literal:

class LitFlags {
private:
	unsigned int _decidable : 1;  // can be used as decision var
	unsigned int _uipable : 1;    // can be used as head of learnt clause
	unsigned int _learnable : 1;  // can be used in tail of learnt clause
	unsigned int _padding : 5;    // leave some space for other flags
public:
	LitFlags(bool d, bool u, bool l) : _decidable(d), _uipable(u), _learnable(l), _padding(0) {}

	void setDecidable(bool b) {
		if (b) {
			_decidable = _uipable = 1;
		} else {
			_decidable = 0;
		}
	}
	void setUIPable(bool b) {
		if (b) {
			_uipable = 1;
		} else {
			_uipable = _decidable = 0;
		}
	}
	void setLearnable(bool b) { _learnable = b; }

	bool decidable() const { return _decidable; }
	bool uipable() const { return _uipable; }
	bool learnable() const { return _learnable; }
};

//=================================================================================================
// ChannelInfo -- store origin of literal:

struct ChannelInfo {
	unsigned int cons_id : 29;
	unsigned int cons_type : 2;
	unsigned int val_type : 1;
	int val;
	ChannelInfo(unsigned int cid, unsigned int ct, unsigned int vt, int v)
			: cons_id(cid), cons_type(ct), val_type(vt), val(v) {}
};

const ChannelInfo ci_null(0, 0, 0, 0);

//=================================================================================================
// WatchElem -- watch list element:
// relies on all pointers being aligned to multiples of 4

class WatchElem {
private:
	union {
		Clause* _pt;  // clause pointer
		uint64_t _a;
	};

public:
	unsigned int type() const {
		return static_cast<unsigned int>(reinterpret_cast<std::ptrdiff_t>(_pt) & 3);
	}
	unsigned int d1() const {
		assert(type() == 2);
		return static_cast<unsigned int>((_a & 0xFFFFFFFF) >> 2);
	}
	unsigned int d2() const {
		assert(type() != 0);
		return static_cast<unsigned int>(_a >> 32);
	}
	Clause* pt() const {
		assert(type() == 0);
		return _pt;
	}

	WatchElem() : _a(0) {}
	WatchElem(Clause* c) : _pt(c) {
		if (sizeof(Clause*) == 4) {
			// Make sure the highest and lowest bits are 0
			_a = _a & 0xFFFFFFFC;
		}
	}

	WatchElem(Lit p) {
		const auto d = static_cast<uint64_t>(toInt(p));
		_a = (d << 32) | 1;
	}
	WatchElem(int prop_id, int pos) {
		const auto d = static_cast<uint64_t>(prop_id) << 32;
		const auto d2 = static_cast<uint64_t>(pos) << 2;
		_a = d | d2 | 2;
	}
	bool operator!=(WatchElem o) const { return _a != o._a; }
};

//=================================================================================================
// Reason -- stores reason for inference:
// relies on all pointers being aligned to multiples of 4

class Reason {
private:
	union {
		Clause* _pt;  // clause pointer
		uint64_t _a;
	};

public:
	unsigned int type() const {
		return static_cast<unsigned int>(reinterpret_cast<std::ptrdiff_t>(_pt) & 3);
	}
	unsigned int d1() const {
		assert(type() != 0);
		return static_cast<unsigned int>((_a & 0xFFFFFFFF) >> 2);
	}
	unsigned int d2() const {
		assert(type() == 1 || type() == 3);
		return static_cast<unsigned int>(_a >> 32);
	}
	Clause* pt() const {
		assert(type() == 0);
		return _pt;
	}

	Reason() : _a(0) {}
	Reason(Clause* c) : _pt(c) {
		if (sizeof(Clause*) == 4) {
			// Make sure the highest and lowest bits are 0
			_a = _a & 0xFFFFFFFC;
		}
	}
	Reason(int prop_id, int inf_id) {
		const auto d2 = static_cast<uint64_t>(prop_id) << 32;
		const auto d1 = static_cast<uint64_t>(inf_id) << 2;
		_a = d2 | d1 | 1;
	}

	Reason(Lit p) {
		const auto d1 = static_cast<uint64_t>(toInt(p));
		_a = (d1 << 2) | 2;
	}

	Reason(Lit p, Lit q) {
		const auto d1 = static_cast<uint64_t>(toInt(p)) << 2;
		const auto d2 = static_cast<uint64_t>(toInt(q)) << 32;
		_a = d2 | d1 | 3;
	}
	bool operator==(Reason o) const { return _a == o._a; }
	bool isLazy() const { return type() == 1; }
};

#endif
