#ifndef int_var_h
#define int_var_h

#include <new>
#include <stdint.h>
#include <chuffed/support/misc.h>
#include <chuffed/core/sat-types.h>
#include <chuffed/core/engine.h>
#include <chuffed/vars/vars.h>
#include <chuffed/vars/bool-view.h>

#ifndef INT64_MAX
#define INT64_MAX 9223372036854775807LL
#endif
#ifndef INT64_MIN
#define INT64_MIN (-INT64_MAX-1)
#endif

// Controls whether active domain values are stored in a trailed linked list,
// to allow fast enumeration of domain values.  Also whether a count is kept.
// NOTE:  Makes search a bit slower, so kept it conditional at this stage,
// turning this off selects compatibility routines that scan value-by-value.
#define INT_DOMAIN_LIST 0

#define IMPACT_DAMPING  0.16

/*

IntVar descriptions

IntVar: Base class, no lits

IntVarEL: Eager lit class, lits are eagerly generated
	supports bounds and/or value lits
	use for "small" vars, or when we need the lits for clausified propagators

IntVarLL;: Lazy lit class, lits are lazily generated
	supports bounds lits only
	remVal ignored
	use for large or unbounded vars

*/

// Bye bye macros
#undef min
#undef max

//-----

class IntVar : public Var {
public:
	int const var_id;

	Tint min;
	Tint max;
	int min0;	// Initial minimum
	int max0;	// Initial maximum
	int shadow_val;
	bool in_scip;
	bool all_in_scip;

        bool should_be_learnable;
        bool should_be_decidable;

	Tchar *vals;
#if INT_DOMAIN_LIST
	Tint *vals_list;
	Tint vals_count;
#endif

	PreferredVal preferred_val;

	double activity;
#ifdef HAS_VAR_IMPACT
	double impact;
	int impact_count;
#endif

	IntVar(int min, int max);

	friend IntVar* newIntVar(int min, int max);

#if !INT_DOMAIN_LIST
	void updateMin();
	void updateMax();
#endif
	void updateFixed();


public:

	static const int max_limit = 500000000;
	static const int min_limit = -500000000;

//--------------------------------------------------
// Engine stuff

	struct PropInfo {
		Propagator *p;
		int pos;        // what is var's id w.r.t. the propagator
		int eflags;     // what var events should wake this propagator

		PropInfo(Propagator *_p, int _pos, int _eflags)
			: p(_p), pos(_pos), eflags(_eflags) {}
	};

	// intermediate state
	int changes;
	bool in_queue;

	// persistent state
	vec<PropInfo> pinfo;

	virtual void attach(Propagator *p, int pos, int eflags);

	void pushInQueue();
	void wakePropagators();
	void clearPropState();
	int simplifyWatches();

//--------------------------------------------------
// Branching stuff

	bool finished() { return isFixed(); }
	double getScore(VarBranch vb);
#ifdef HAS_VAR_IMPACT
	double updateImpact(double const newImpact) {
		double const weight = (1 - IMPACT_DAMPING) * impact_count++;
		return impact = (weight * impact + newImpact) / (weight + 1);
	}
#endif
	void setPreferredVal(PreferredVal p) { preferred_val = p; }
	DecInfo* branch();

//--------------------------------------------------
// Type specialisation

	VarType getType() { return INT_VAR; }

	void specialiseToEL();
	void specialiseToLL();
	void specialiseToSL(vec<int>& values);

	void initVals(bool optional = false);

//--------------------------------------------------
// Read data
	
	bool isFixed() const { return min == max; }
	int  getMin()  const { return min; }
	int  getMax()  const { return max; }
	int  getMin0()  const { return min0; }
	int  getMax0()  const { return max0; }
	int  getVal()  const { assert(isFixed()); return min; }
	int  getShadowVal() const {
		if (in_scip) return shadow_val;
		return min;
	}

	bool indomain(int64_t v) const {
		return v >= min && v <= max && (!vals || vals[v]);
	}

	class iterator {
		const IntVar* var;
		int val;
	public:
		iterator() {}
		iterator(const IntVar* _var, int _val) : var(_var), val(_val) {}
		int operator *() const {
			assert(val >= var->min && val <= var->max && var->vals && var->vals[val]);
			return val;
		}
		iterator& operator ++() {
			assert(val >= var->min && val <= var->max && var->vals && var->vals[val]);
			if (val == var->max)
				val = static_cast<int>(0x80000000);
			else
#if INT_DOMAIN_LIST
				val = var->vals_list[2*val+1];
#else
				while (!var->vals[++val])
					;
#endif
			return *this;
		}
		iterator operator ++(int dummy) {
			iterator temp = *this;
			++*this;
			return temp;
		}
		iterator& operator --() {
			if (val == static_cast<int>(0x80000000))
				val = var->max;
			else {
				assert(val > var->min && val <= var->max && var->vals && var->vals[val]);
#if INT_DOMAIN_LIST
				val = var->vals_list[2*val];
#else
				while (!var->vals[--val])
					;
#endif
			}
			return *this;
		}
		iterator operator --(int dummy) {
			iterator temp = *this;
			--*this;
			return temp;
		}
		bool operator ==(const iterator& rhs) const {
			assert(var == rhs.var);
			return (val == rhs.val);
		}
		bool operator !=(const iterator& rhs) const {
			assert(var == rhs.var);
			return (val != rhs.val);
		}
	};
	typedef iterator const_iterator;
	iterator begin() const { return iterator(this, min); }
	iterator end() const { return iterator(this, static_cast<int>(0x80000000)); }

	class reverse_iterator {
		iterator forward;
	public:
		reverse_iterator() {}
		reverse_iterator(iterator _forward) : forward(_forward) {}
		int operator *() const {
			iterator temp = forward;
			return *--temp;
		}
		reverse_iterator& operator ++() {
			--forward;
			return *this;
		}
		reverse_iterator operator ++(int dummy) {
			reverse_iterator temp = *this;
			++*this;
			return temp;
		}
		reverse_iterator& operator --() {
			++forward;
			return *this;
		}
		reverse_iterator operator --(int dummy) {
			reverse_iterator temp = *this;
			--*this;
			return temp;
		}
		iterator base() const {
			return forward;
		}
		bool operator ==(const reverse_iterator& rhs) const {
			return (forward == rhs.forward);
		}
		bool operator !=(const reverse_iterator& rhs) const {
			return (forward != rhs.forward);
		}
	};
	typedef reverse_iterator const_reverse_iterator;
	reverse_iterator rbegin() const { return reverse_iterator(end()); }
	reverse_iterator rend() const { return reverse_iterator(begin()); }

	int size() const {
#ifdef HAS_VAR_IMPACT
		if (!vals) return max - min;
#else
		assert(vals);
#endif
#if INT_DOMAIN_LIST
		return vals_count;
#else
		if (isFixed())
			return 1;
		int count = 2;
		for (int i = min + 1; i < max; ++i)
			count += vals[i];
		return count;
#endif
	}

//--------------------------------------------------
// Explanations:

	virtual Lit getMinLit() const { NEVER; }
	virtual Lit getMaxLit() const { NEVER; }
	virtual Lit getValLit() const { NEVER; }
	virtual Lit getFMinLit(int64_t v) { NEVER; }
	virtual Lit getFMaxLit(int64_t v) { NEVER; }

	// NOTE: No support for INT_VAR_LL vars yet!
	// t = 0: [x != v], t = 1: [x = v], t = 2: [x >= v], t = 3: [x <= v]
	virtual Lit getLit(int64_t v, int t) { NEVER; }

//--------------------------------------------------
// Domain operations

	void set(int val, int type, bool channel = true);

	bool setMinNotR(int64_t v) const { return v > min; }
	bool setMaxNotR(int64_t v) const { return v < max; }
	bool setValNotR(int64_t v) const { return v != min || v != max; }
	bool remValNotR(int64_t v) const { return indomain(v); }

	virtual bool setMin(int64_t v, Reason r = NULL, bool channel = true);
	virtual bool setMax(int64_t v, Reason r = NULL, bool channel = true);
	virtual bool setVal(int64_t v, Reason r = NULL, bool channel = true);
	virtual bool remVal(int64_t v, Reason r = NULL, bool channel = true);
	virtual bool allowSet(vec<int>& v, Reason r = NULL, bool channel = true);

	virtual void channel(int val, int val_type, int sign) {
		set(val, val_type * 3 ^ sign, false);
	}

	Lit operator >= (int val) { return getLit(val, 2); }
	Lit operator <= (int val) { return getLit(val, 3); }
	Lit operator >  (int val) { return getLit(val+1, 2); }
	Lit operator <  (int val) { return getLit(val-1, 3); }
	Lit operator =  (int val) { return getLit(val, 1); }
	Lit operator != (int val) { return getLit(val, 0); }

	operator BoolView () { assert(min >= 0 && max <= 1); return getLit(1, 2); }

//--------------------------------------------------
// Debug

	void printLit(int val, int type);
	void print();

};

IntVar* newIntVar(int min = IntVar::min_limit, int max = IntVar::max_limit);
IntVar* getConstant(int v);

inline void IntVar::pushInQueue() {
	if (!in_queue) {
		in_queue = true;
		engine.v_queue.push(this);
	}
}

inline void IntVar::clearPropState() {
	changes = 0;
	in_queue = false;
}

inline void IntVar::set(int val, int type, bool channel) {
	switch (type) {
		case 0: remVal(val, NULL, channel); break;
		case 1: setVal(val, NULL, channel); break;
		case 2: setMin(val+1, NULL, channel); break;
		case 3: setMax(val, NULL, channel); break;
		default: NEVER;
	}
}

inline void IntVar::printLit(int val, int type) {
	printf("[v%d ", var_id);
	switch (type) {
		case 0: printf("!= %d]", val); break;
		case 1: printf("== %d]", val); break;
		case 2: printf(">= %d]", val+1); break;
		case 3: printf("<= %d]", val); break;
	}
}

inline void IntVar::print() {
	fprintf(stderr, "v%d: min = %d, max = %d\n", var_id, (int) min, (int) max);
}

#undef IMPACT_DAMPING


#include <chuffed/vars/int-var-el.h>
#include <chuffed/vars/int-var-ll.h>
#include <chuffed/vars/int-var-sl.h>

#endif
