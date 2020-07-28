/*

Checklist for propagators:

1. Must return false if all vars are fixed and constraint is unsatisfied (correctness)
2. Only go redundant if known bounds on vars prove constraint is satisfied (do not rely on holes in domains)
3. Persistent state should be trailed if necessary
4. Intermediate state should be cleared in clearPropState()
5. Check for overflow
6. Check for idempotence

Assumptions:

1. Every variable is watched by the propagator in some way

*/

#ifndef propagator_h
#define propagator_h

#include <climits>
#include <new>
#include <algorithm>
#include <vector>
#include <chuffed/support/misc.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/sat-types.h>
#include <chuffed/core/sat.h>
//#include "core/prop-group.h"

enum ConLevel { CL_DEF, CL_VAL, CL_BND, CL_DOM };

class Propagator {
public:
	int const prop_id;
	int priority;

	// Persistent state
	Tchar satisfied;

	// Intermediate state
	bool in_queue;

	Propagator() : prop_id(engine.propagators.size()), priority(0),
		satisfied(false), in_queue(false) {
		engine.propagators.push(this);
	}
  
  virtual ~Propagator() {}

	// Push propgator into queue if it isn't already there
	void pushInQueue() {
		if (!in_queue) {
			in_queue = true;
			engine.p_queue[priority].push(this);
		}
	}

	// Wake up only parts relevant to this event
	virtual void wakeup(int i, int c) { pushInQueue(); }

	// Propagate woken up parts
	virtual bool propagate() = 0;

	// Clear intermediate states
	virtual void clearPropState() {	in_queue = false;	}

	// Explain propagation
	virtual Clause* explain(Lit p, int inf_id) { NEVER; }

	// Free a lazily generated literal
	virtual void freeLazyVar(int v) { NEVER; }

	// Check if constraint is satisfied, return cost of check
	virtual int checkSatisfied() { return 0; }

	// Print meaning of literal
	virtual void printLit(int v, bool sign) { NEVER; }

	// Print statistics
	virtual void printStats() {}

};

class Requeueable {
public:
	IntVar *v;
	Requeueable();
	void init_requeue(Propagator *p);
	void requeue();
};


// Pseudo "propagators" that do stuff at fix point. Must not change any domains or cause failure.

class PseudoProp {
public:
	PseudoProp() { engine.pseudo_props.push(this); }
	virtual void doFixPointStuff() = 0;
};

// Checks to see if a constraint is satisfied. Assumes that all vars are fixed.

class Checker {
public:
	Checker() { engine.checkers.push(this); }
	virtual bool check() = 0;
};


static inline Clause* Reason_new(int sz) {
  Clause *c = (Clause*) malloc(sizeof(Clause) + sz * sizeof(Lit));
	c->clearFlags(); c->temp_expl = 1; c->sz = sz;
	sat.rtrail.last().push(c);
  return c;
}

static inline Clause* Reason_new(vec<Lit>& ps) {
	Clause *c = Clause_new(ps);
	c->temp_expl = 1;
	sat.rtrail.last().push(c);
	return c;
}

static inline Clause* Reason_new(std::vector<Lit> ps) {
  Clause *c = Reason_new(ps.size() + 1);
  for (int i = 0; i < ps.size(); i++) {
    (*c)[i+1] = ps[i];
  }
	return c;
}

#define TL_SET(var, op, val) do {                                     \
	if (var->op ## NotR(val) && !var->op(val)) TL_FAIL(); } while (0)


#define setDom(var, op, val, ...) do {           \
	int64_t m_v = (val);                           \
	if (var.op ## NotR(m_v)) {                     \
		Reason m_r = NULL;                           \
		if (so.lazy) new (&m_r) Reason(__VA_ARGS__); \
		if (!var.op(m_v, m_r)) return false;         \
	}                                              \
} while (0)

#define setDom2(var, op, val, index) do {                                         \
	int64_t v = (val);                                                              \
	if (var.op ## NotR(v) && !var.op(v, Reason(prop_id, index))) return false;      \
} while (0)



#include <chuffed/vars/bool-view.h>
#include <chuffed/vars/int-var.h>
#include <chuffed/vars/int-view.h>

#include <chuffed/primitives/primitives.h>
#include <chuffed/globals/globals.h>


#endif
