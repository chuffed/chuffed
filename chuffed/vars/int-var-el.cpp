#include "chuffed/core/options.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/core/sat.h"
#include "chuffed/support/misc.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/vars.h"

#include <algorithm>
#include <cassert>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <utility>

extern std::map<IntVar*, std::string> intVarString;

IntVarEL::IntVarEL(const IntVar& other)
		: IntVar(other), lit_min(INT_MIN), lit_max(INT_MIN), base_vlit(INT_MIN), base_blit(INT_MIN) {
	initVals();
	initVLits();
	initBLits();
	setVLearnable(should_be_learnable);
	setBLearnable(should_be_learnable);
	setVDecidable(should_be_decidable);
	setBDecidable(should_be_decidable);
	if (!should_be_learnable) {
		setVDecidable(false);
		setBDecidable(false);
	}

	if (so.debug) {
		std::cerr << "created integer variable " << intVarString[(IntVar*)(&other)] << "\n";
		if (intVarString[(IntVar*)(&other)].empty()) {
			std::abort();
		}
	}

	for (int v = lit_min; v <= lit_max; v++) {
		std::string label;
		std::stringstream ss;
		ss << intVarString[(IntVar*)(&other)];
		std::stringstream ssv;
		ssv << v;
		std::string val = ssv.str();
		label = ss.str();
		label.append("!=");
		label.append(val);
		litString.insert(std::pair<int, std::string>(base_vlit + 2 * v, label));
		label = ss.str();
		label.append("==");
		label.append(val);
		litString.insert(std::pair<int, std::string>(base_vlit + 2 * v + 1, label));
		label = ss.str();
		label.append(">=");
		label.append(val);
		litString.insert(std::pair<int, std::string>(base_blit + 2 * v, label));
		label = ss.str();
		label.append("<=");
		label.append(val);
		litString.insert(std::pair<int, std::string>(base_blit + 2 * v + 1, label));
	}
	// The extra <= min-1 and >= max+1 bounds literals (both
	// obviously false).
	std::string label;
	std::stringstream ss;
	ss << intVarString[(IntVar*)(&other)] << "<=" << (lit_min - 1);
	litString.insert(std::pair<int, std::string>(base_blit + 2 * (lit_min - 1) + 1, ss.str()));
	ss.str("");
	ss << intVarString[(IntVar*)(&other)] << ">=" << (lit_max + 1);
	litString.insert(std::pair<int, std::string>(base_blit + 2 * (lit_max + 1), ss.str()));
}

// lit_min is the smallest value for which we can get a literal for
// this variable.  For example, if we already have "n" SAT variables,
// and lit_min=3 and lit_max=6, the SAT variables are arranged like
// this:
//
// n-5 n-4 n-3 n-2 n-1  n  n+1 n+2 n+3 n+4
//  X   X   X   X   X   X   3   4   5   6
//
// where X is an already-in-use SAT variable, and 3,4,5.. are the SAT
// variables representing this integer variable.  There are two
// literals for each variable, so the literals are arranged like this:
//
//  SAT variable  value     literal    literal index
//      n-2         X
//
//      n-1         X
//
//      n           3         !=3        2*n
//                             =3        2*n+1
//      n+1         4         !=4        2*(n+1)
//                             =4        2*(n+1)+1
//      n+2         5         !=5        2*(n+2)
//                             =5        2*(n+2)+1
//      n+3         6         !=6        2*(n+3)
//                             =6        2*(n+3)+1
//
// base_vlit is chosen such that base_vlit+2*v gives the !=v literal,
// i.e. base_vlit = 2*(n - lit_min).

void IntVarEL::initVLits() {
	if (base_vlit != INT_MIN) {
		return;
	}
	initVals();
	if (lit_min == INT_MIN) {
		lit_min = min;
		lit_max = max;
	}
	base_vlit = 2 * (sat.nVars() - lit_min);
	sat.newVar(lit_max - lit_min + 1, ChannelInfo(var_id, 1, 0, lit_min));
	for (int i = lit_min; i <= lit_max; i++) {
		if (!indomain(i)) {
			sat.cEnqueue(getNELit(i), nullptr);
		}
	}
	if (isFixed()) {
		sat.cEnqueue(getEQLit(min), nullptr);
	}
}

// Bounds literals are arranged similarly to the value/equality
// literals above.  There is one more SAT variable than there are
// values in the integer variable.
//
//  SAT variable  value        literal      literal index
//      n-2         X
//
//      n-1         X
//
//      n           3          <3  <=2        2*n
//                                 >=3        2*n+1
//      n+1         4          <4  <=3        2*(n+1)
//                                 >=4        2*(n+1)+1
//      n+2         5          <5  <=4        2*(n+2)
//                                 >=5        2*(n+2)+1
//      n+3         6          <6  <=5        2*(n+3)
//                                 >=6        2*(n+3)+1
//      n+4         7          <7  <=6        2*(n+4)
//                                 >=7        2*(n+4)+1
//
// base_blit is chosen such that base_blit+2*v gives the >=v literal,
// and base_blit+2*v+1 gives the <=v literal.  Note that these are not
// negations of one another, and that base_vlit is odd!
// base_blit = 2*(n - lit_min) + 1.

void IntVarEL::initBLits() {
	if (base_blit != INT_MIN) {
		return;
	}
	if (lit_min == INT_MIN) {
		lit_min = min;
		lit_max = max;
	}
	base_blit = 2 * (sat.nVars() - lit_min) + 1;
	sat.newVar(lit_max - lit_min + 2, ChannelInfo(var_id, 1, 1, lit_min - 1));
	for (int i = lit_min; i <= min; i++) {
		sat.cEnqueue(getGELit(i), nullptr);
	}
	for (int i = max; i <= lit_max; i++) {
		sat.cEnqueue(getLELit(i), nullptr);
	}
}

void IntVarEL::setVLearnable(bool b) const {
	for (int i = lit_min; i <= lit_max; i++) {
		sat.flags[base_vlit / 2 + i].setLearnable(b);
		sat.flags[base_vlit / 2 + i].setUIPable(b);
	}
}

void IntVarEL::setBLearnable(bool b) const {
	for (int i = lit_min; i <= lit_max + 1; i++) {
		sat.flags[(base_blit - 1) / 2 + i].setLearnable(b);
		sat.flags[(base_blit - 1) / 2 + i].setUIPable(b);
	}
}

void IntVarEL::setVDecidable(bool b) const {
	for (int i = lit_min; i <= lit_max; i++) {
		sat.flags[base_vlit / 2 + i].setDecidable(b);
	}
}

void IntVarEL::setBDecidable(bool b) const {
	for (int i = lit_min; i <= lit_max + 1; i++) {
		sat.flags[(base_blit - 1) / 2 + i].setDecidable(b);
	}
}

Lit IntVarEL::getLit(int64_t v, LitRel t) {
	//    std::cerr << "IntVarEL::getLit\n";
	if (v < lit_min) {
		return toLit(1 ^ (t & 1));  // 1, 0, 1, 0
	}
	if (v > lit_max) {
		return toLit(((t - 1) >> 1) & 1);  // 1, 0, 0, 1
	}
	switch (t) {
		case LR_NE:
			return getNELit(v);
		case LR_EQ:
			return getEQLit(v);
		case LR_GE:
			return getGELit(v);
		case LR_LE:
			return getLELit(v);
		default:
			NEVER;
	}
}

// Use when you've just set [x >= v]
inline void IntVarEL::channelMin(int v) {
	// Set [x >= v-1] to [x >= min+1] using [x >= i] \/ ![x >= v]
	// Set [x != v-1] to [x != min] using [x != i] \/ ![x >= v]
	Reason r(~getGELit(v));
	for (int i = v - 1; i > min; i--) {
		sat.cEnqueue(getGELit(i), r);
		if (vals[i] != 0) {
			sat.cEnqueue(getNELit(i), r);
		}
	}
	assert(vals[min]);
	sat.cEnqueue(getNELit(min), r);
}

// Use when you've just set [x <= v]
inline void IntVarEL::channelMax(int v) {
	// Set [x <= v+1] to [x <= max-1] to using [x <= i] \/ ![x <= v]
	// Set [x != v+1] to [x != max] to using ![x = i] \/ ![x <= v]
	Reason r(~getLELit(v));
	for (int i = v + 1; i < max; i++) {
		sat.cEnqueue(getLELit(i), r);
		if (vals[i] != 0) {
			sat.cEnqueue(getNELit(i), r);
		}
	}
	assert(vals[max]);
	sat.cEnqueue(getNELit(max), r);
}

// Use when you've just set [x = v]
inline void IntVarEL::channelFix(int v) {
	Reason r(getNELit(v));
	if (min < v) {
		// Set [x >= v] using [x >= v] \/ ![x = v]
		sat.cEnqueue(getGELit(v), r);
		channelMin(v);
	}
	if (max > v) {
		// Set [x <= v] using [x <= v] \/ ![x = v]
		sat.cEnqueue(getLELit(v), r);
		channelMax(v);
	}
}

#if INT_DOMAIN_LIST
inline void IntVarEL::updateMin(int v, int i) {
	for (; v < i; ++v) {
		// Set [x >= v+1] using [x >= v+1] \/ [x <= v-1] \/ [x = v]
		Reason r(getLELit(v - 1), getEQLit(v));
		sat.cEnqueue(getGELit(v + 1), r);
	}
	min = v;
	changes |= EVENT_C | EVENT_L;
}

inline void IntVarEL::updateMax(int v, int i) {
	for (; v > i; --v) {
		// Set [x <= v-1] using [x <= v-1] \/ [x >= v+1] \/ [x = v]
		Reason r(getGELit(v + 1), getEQLit(v));
		sat.cEnqueue(getLELit(v - 1), r);
	}
	max = v;
	changes |= EVENT_C | EVENT_U;
}
#else
inline void IntVarEL::updateMin() {
	int v = min;
	while (vals[v] == 0) {
		// Set [x >= v+1] using [x >= v+1] \/ [x <= v-1] \/ [x = v]
		Reason r(getLELit(v - 1), getEQLit(v));
		sat.cEnqueue(getGELit(v + 1), r);
		v++;
	}
	if (v > min) {
		min = v;
		changes |= EVENT_L;
	}
}

inline void IntVarEL::updateMax() {
	int v = max;
	while (vals[v] == 0) {
		// Set [x <= v-1] using [x <= v-1] \/ [x >= v+1] \/ [x = v]
		Reason r(getGELit(v + 1), getEQLit(v));
		sat.cEnqueue(getLELit(v - 1), r);
		v--;
	}
	if (v < max) {
		max = v;
		changes |= EVENT_U;
	}
}
#endif

inline void IntVarEL::updateFixed() {
	if (isFixed()) {
		int v = min;
		// Set [x = v] using [x = v] \/ [x <= v-1] \/ [x >= v+1]
		Reason r(getLELit(v - 1), getGELit(v + 1));
		sat.cEnqueue(getEQLit(v), r);
		changes |= EVENT_F;
	}
}

bool IntVarEL::setMin(int64_t v, Reason r, bool channel) {
	assert(setMinNotR(v));
	if (channel) {
		sat.cEnqueue(getLit(v, LR_GE), r);
	}
	if (v > max) {
		assert(sat.confl);
		return false;
	}
	channelMin(v);
#if INT_DOMAIN_LIST
	int i;
	int j = vals_count;
	for (i = min; i < v; i = vals_list[2 * i + 1]) --j;
	updateMin(v, i);
	vals_count = j;
#else
	min = v;
	changes |= EVENT_C | EVENT_L;
	updateMin();
#endif
	updateFixed();
	pushInQueue();
	return true;
}

bool IntVarEL::setMax(int64_t v, Reason r, bool channel) {
	assert(setMaxNotR(v));
	if (channel) {
		sat.cEnqueue(getLit(v, LR_LE), r);
	}
	if (v < min) {
		assert(sat.confl);
		return false;
	}
	channelMax(v);
#if INT_DOMAIN_LIST
	int i;
	int j = vals_count;
	for (i = max; i > v; i = vals_list[2 * i]) --j;
	updateMax(v, i);
	vals_count = j;
#else
	max = v;
	changes |= EVENT_C | EVENT_U;
	updateMax();
#endif
	updateFixed();
	pushInQueue();
	return true;
}

bool IntVarEL::setVal(int64_t v, Reason r, bool channel) {
	assert(setValNotR(v));
	if (channel) {
		sat.cEnqueue(getLit(v, LR_EQ), r);
	}
	if (!indomain(v)) {
		assert(sat.confl);
		return false;
	}
	changes |= EVENT_C | EVENT_F;
	channelFix(v);
	if (min < v) {
		min = v;
		changes |= EVENT_L;
	}
	if (max > v) {
		max = v;
		changes |= EVENT_U;
	}
#if INT_DOMAIN_LIST
	vals_count = 1;
#endif
	pushInQueue();
	return true;
}

bool IntVarEL::remVal(int64_t v, Reason r, bool channel) {
	assert(remValNotR(v));
	assert(vals);
	if (channel) {
		sat.cEnqueue(getLit(v, LR_NE), r);
	}
	if (isFixed()) {
		assert(sat.confl);
		return false;
	}
#if INT_DOMAIN_LIST
	if (v == min)
		updateMin(min, vals_list[2 * min + 1]);
	else if (v == max)
		updateMax(max, vals_list[2 * max]);
	else {
		vals[v] = 0;
		vals_list[vals_list[2 * v] * 2 + 1] = vals_list[2 * v + 1];
		vals_list[vals_list[2 * v + 1] * 2] = vals_list[2 * v];
		changes |= EVENT_C;
	}
	--vals_count;
#else
	changes |= EVENT_C;
	vals[v] = 0;
	updateMin();
	updateMax();
#endif
	updateFixed();
	pushInQueue();
	return true;
}

Lit IntVarEL::createSetLit(vec<Lit>& head) {
	// lb, ub and holes, which together cause the conflict
	int lower_bound = lit_min;
	int upper_bound = lit_max;
	vec<int> holes;

	std::sort((Lit*)head, (Lit*)head + head.size());

	// process bounds lits first
	for (int i = 0; i < head.size(); i++) {
		ChannelInfo& ci = sat.c_info[var(head[i])];
		if (ci.val_type == 0) {
			continue;
		}
		int v = ci.val;
		if (sign(head[i])) {
			if (v < upper_bound) {
				upper_bound = v;
			}
		} else {
			if (v + 1 > lower_bound) {
				lower_bound = v + 1;
			}
		}
	}

	// process val lits
	for (int i = 0; i < head.size(); i++) {
		ChannelInfo& ci = sat.c_info[var(head[i])];
		if (ci.val_type == 1) {
			continue;
		}
		int v = ci.val;
		if (sign(head[i])) {
			if (v < lower_bound || v > upper_bound) {
				continue;
			}
			if (v == lower_bound) {
				lower_bound++;
				continue;
			}
			if (v == upper_bound) {
				upper_bound--;
				continue;
			}
			holes.push(v);
		} else {
			return getNELit(v);
		}
	}

	if (lower_bound > upper_bound) {
		printf("Domain wipeout??\n");
		assert(false);
	}

	//	printf("lower_bound = %d, upper_bound = %d\n", lower_bound, upper_bound);
	//	for (int i = 0; i < holes.size(); i++) printf("%d ", holes[i]); printf("\n");

	fflush(stdout);

	// Check cases where an original lit is sufficient

	if (lower_bound == lit_min && holes.size() == 0) {
		return getGELit(upper_bound + 1);
	}
	if (upper_bound == lit_max && holes.size() == 0) {
		return getLELit(lower_bound - 1);
	}

	// Create new lit that complements failure set

	Lit q = Lit(sat.getLazyVar(ci_null), true);
	sat.flags[var(q)].setUIPable(false);
	sat.flags[var(q)].setLearnable(false);

	vec<Lit> ps(2);
	ps[1] = ~q;

	if (lower_bound == lit_min) {
		// can use bounds lit for lower bound
		sat.addClause(getGELit(holes[0]), ~q);
		lower_bound = holes[0];
		//		printf("GE: %d\n", holes[0]);
	}
	if (upper_bound == lit_max) {
		// can use bounds lit for upper bound
		sat.addClause(getLELit(holes.last()), ~q);
		upper_bound = holes.last();
		//		printf("LE: %d\n", holes.last());
	}
	int j = 0;
	for (int i = lower_bound; i <= upper_bound; i++) {
		if (j < holes.size() && i == holes[j]) {
			j++;
			continue;
		}
		ps[0] = getNELit(i);
		sat.addClause(*Clause_new(ps), true);
		//		printf("NE: %d\n", i);
	}

	//	printf("New lit = %d\n", toInt(q));

	return q;
}
