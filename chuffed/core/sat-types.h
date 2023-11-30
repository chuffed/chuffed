#ifndef sat_types_h
#define sat_types_h

//=================================================================================================
// Variables, literals, lifted booleans, clauses:

// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

#include <cassert>
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
	Lit data[0];                 // the literals of the clause
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
	void clearFlags() { *((char*)this) = 0; }
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
	const int mem_size = sizeof(Clause) + ps.size() * sizeof(Lit) + (learnt ? 3 : 0) * sizeof(int);
	void* mem = malloc(mem_size);
	auto* newClause = new (mem) Clause(ps, learnt);
	return newClause;
}

//=================================================================================================
// LitFlags -- store info concerning literal:

struct LitFlags {
	unsigned int decidable : 1;  // can be used as decision var
	unsigned int uipable : 1;    // can be used as head of learnt clause
	unsigned int learnable : 1;  // can be used in tail of learnt clause
	unsigned int padding : 5;    // leave some space for other flags

	LitFlags(char f) { *((char*)this) = f; }
	void setDecidable(bool b) {
		if (b) {
			decidable = uipable = 1;
		} else {
			decidable = 0;
		}
	}
	void setUIPable(bool b) {
		if (b) {
			uipable = 1;
		} else {
			uipable = decidable = 0;
		}
	}
	void setLearnable(bool b) { learnable = b; }
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
public:
	union {
		Clause* pt;  // clause pointer
		struct {
			unsigned int type : 2;  // which type of watch elem if it's not a clause pointer
			unsigned int d1 : 30;   // data 1
			unsigned int d2 : 32;   // data 2
		} d;
		int64_t a;
	};
	WatchElem() : a(0) {}
	WatchElem(Clause* c) : pt(c) {
		if (sizeof(Clause*) == 4) {
			d.d2 = 0;
		}
	}
	WatchElem(Lit p) {
		d.type = 1;
		d.d2 = toInt(p);
	}
	WatchElem(int prop_id, int pos) { d.type = 2, d.d1 = pos, d.d2 = prop_id; }
	bool operator!=(WatchElem o) const { return a != o.a; }
};

//=================================================================================================
// Reason -- stores reason for inference:
// relies on all pointers being aligned to multiples of 4

class Reason {
public:
	union {
		Clause* pt;  // clause pointer
		struct {
			unsigned int type : 2;  // which type of reason if it's not a clause pointer
			unsigned int d1 : 30;   // data 1
			unsigned int d2 : 32;   // data 2
		} d;
		int64_t a;
	};
	Reason() : a(0) {}
	Reason(Clause* c) : pt(c) {
		if (sizeof(Clause*) == 4) {
			d.d2 = 0;
		}
	}
	Reason(int prop_id, int inf_id) {
		d.type = 1;
		d.d1 = inf_id;
		d.d2 = prop_id;
	}
	Reason(Lit p) {
		d.type = 2;
		d.d1 = toInt(p);
	}
	Reason(Lit p, Lit q) {
		d.type = 3;
		d.d1 = toInt(p);
		d.d2 = toInt(q);
	}
	bool operator==(Reason o) const { return a == o.a; }
	bool isLazy() const { return d.type == 1; }
};

#endif
