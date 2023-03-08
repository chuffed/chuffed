#ifndef mip_h
#define mip_h

#include <chuffed/core/propagator.h>
#include <chuffed/support/misc.h>

#include <map>
#include <set>

using namespace std;

class VarGroup;

struct LinearIneq {
	vec<int> a;
	vec<IntVar*> x;
	long double lb;
	long double ub;
	bool lb_notR;
	bool ub_notR;
	LinearIneq() {}
};

struct BoundChange {
	int v;  // which original variable
	int w;  // 0 = lower bound, 1 = upper bound
	int d;  // how much it increased by
	BoundChange(int _v, int _w, int _d) : v(_v), w(_w), d(_d) {}
};

class MIP : public Propagator {
	enum SimplexStatus {
		SIMPLEX_OPTIMAL,
		SIMPLEX_GOOD_ENOUGH,
		SIMPLEX_IN_PROGRESS,
		SIMPLEX_UNBOUNDED
	};

public:
	set<IntVar*> var_set;
	map<IntVar*, int> var_map;
	vec<IntVar*> vars;
	vec<LinearIneq> ineqs;

	vec<long double> RL;
	vec<Lit> ps;
	vec<int> place;

	vec<BoundChange> bctrail;
	vec<int> bctrail_lim;

	int level_lb;
	int level_ub;

	int status;

	duration simplex_time;

	VarGroup* toplevelgroup;

	// temp data
	vec<int> new_bc;

	MIP();

	// Interface methods

	void addConstraint(vec<int>& a, vec<IntVar*>& x, long double lb, long double ub);
	void init();
	void presolve() {}

	void newDecisionLevel();
	void btToLevel(int level);

	void setObjective(int val) {}
	long double getRC(IntVar* v);
	void printStats() override;

	// Main propagator methods

	void wakeup(int i, int c) override;
	bool propagate() override;
	void clearPropState() override;

	// LP methods

	int getLimit() const;
	void updateBounds();
	int doSimplex() const;
	void unboundedFailure();
	bool propagateAllBounds();
	template <int T>
	bool propagateBound(int i, long double s);
	long double objVarBound();

	// Inline functions

	inline int decisionLevel() const { return bctrail_lim.size(); }
};

extern MIP* mip;

#endif
