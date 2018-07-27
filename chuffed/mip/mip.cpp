#include <chuffed/mip/mip.h>
#include <chuffed/mip/simplex.h>

#define MIP_DEBUG 0
#define RC_BOUNDS 1
#define DEFAULT_ROUNDS 0
#define RESTORE_ROOT 0
#define RAND_RC 1
#define ULEVEL_LIMIT 3
#define LLEVEL_LIMIT 3

MIP *mip;

//-----
// Main propagator methods

MIP::MIP() : level_lb(-1), level_ub(-1), status(0), simplex_time(duration::zero()) {
//	priority = 3;
	priority = 0;
}

void MIP::addConstraint(vec<int>& a, vec<IntVar*>& x, long double lb, long double ub) {
	for (int i = 0; i < x.size(); i++) var_set.insert(x[i]);
	ineqs.push();
	LinearIneq& li = ineqs.last();
	a.copyTo(li.a);
	x.copyTo(li.x);
	int red_lb = 0, red_ub = 0;
	for (int i = 0; i < a.size(); i++) {
		if (a[i] > 0) {
			red_lb += a[i] * x[i]->getMin();
			red_ub += a[i] * x[i]->getMax();
		} else {
			red_lb += a[i] * x[i]->getMax();
			red_ub += a[i] * x[i]->getMin();
		}
	}
	li.lb_notR = (lb > red_lb);
	li.ub_notR = (ub < red_ub);
	li.lb = (li.lb_notR ? lb : red_lb);
	li.ub = (li.ub_notR ? ub : red_ub);
}

void MIP::init() {
	if (engine.opt_var == NULL) {
		printf("Not an optimization problem, turning off MIP\n");
		so.mip = false;
		return;
	}

	var_set.erase(engine.opt_var);
	var_map.insert(pair<IntVar*,int>(engine.opt_var, 0));
	vars.push(engine.opt_var);

	for (set<IntVar*>::iterator it = var_set.begin(); it != var_set.end(); it++) {
		IntVar* v = *it;
		var_map.insert(pair<IntVar*,int>(v, vars.size()));
		v->attach(this, vars.size(), EVENT_LU);
		vars.push(v);
	}

	RL.growTo(vars.size());
	place.growTo(vars.size());

	simplex.init();

}

void MIP::wakeup(int i, int c) {
	new_bc.push(i);
	pushInQueue();
}


bool MIP::propagate() {
	time_point start = chuffed_clock::now();
//	printObjective();

	updateBounds();

	status = doSimplex();

//	printObjective();
//	checkObjective();

//	printf("Depth = %d\n", decisionLevel());

	simplex_time += std::chrono::duration_cast<duration>(chuffed_clock::now() - start);

	if (status == SIMPLEX_UNBOUNDED) {
		if (MIP_DEBUG) printf("MIP failure\n");
		return false;
	}

	if (!propagateAllBounds()) {
		if (MIP_DEBUG) printf("MIP failure\n");
		return false;
	}

	engine.last_prop = this;

	return true;
}

void MIP::clearPropState() {
	in_queue = false;
	new_bc.clear();
}

//-----
// Interface methods

void MIP::newDecisionLevel() {
	bctrail_lim.push(bctrail.size());
}

void MIP::btToLevel(int level) {
	if (RESTORE_ROOT && level == 0) {
		bctrail.resize(bctrail_lim[0]);
		bctrail_lim.resize(0);
		simplex.loadState(simplex.root);
		return;
	}
  for (int i = bctrail.size(); i-- > bctrail_lim[level]; ) {
		BoundChange& bc = bctrail[i];
		if (bc.w == simplex.shift[bc.v]) {
			simplex.boundChange(bc.v, -bc.d);
		}
	}
  bctrail.resize(bctrail_lim[level]);
  bctrail_lim.resize(level);
	if (level > 0) {
//		printf("reset level limit\n");
		level_lb = level-LLEVEL_LIMIT;
		level_ub = level+ULEVEL_LIMIT;
	}
}

//-----
// Auxiliary propagator methods


void MIP::unboundedFailure() {
//	NOT_SUPPORTED;
//	if (MIP_DEBUG) 
//		simplex.unboundedDebug();

	assert(simplex.row[0] == 0);

	vec<Lit> ps;
	for (int i = 1; i < vars.size(); i++) {
		ps.push(simplex.shift[i] == 0 ? vars[i]->getMinLit() : vars[i]->getMaxLit());
	}
	Clause *m_r = Clause_new(ps);
	m_r->temp_expl = 1;
	sat.rtrail.last().push(m_r);
	sat.confl = m_r;
}

bool MIP::propagateAllBounds() {

//	simplex.checkBasis();
//	simplex.recalculateRHS();
//	simplex.checkObjective();
//	simplex.checkObjective2();


	for (int i = 1; i < vars.size(); i++) {
		RL[i] = simplex.obj[i];
//		printf("%.3f ", RL[i]);
	}
//	printf("level = %d\n", decisionLevel());
//	printf("\n");

	bool rc = false;

	ps.clear();

	if (so.lazy) {
		place[0] = 0;
		ps.push(engine.opt_type == OPT_MIN ? vars[0]->getMaxLit() : vars[0]->getMinLit());
		for (int i = 1; i < vars.size(); i++) {
			place[i] = ps.size();
			if (RL[i] > 0) ps.push(vars[i]->getMinLit());
			if (RL[i] < 0) ps.push(vars[i]->getMaxLit());
		}
	}

	// Propagate bounds on all vars

//	fprintf(stderr, "objVarBound() = %.3Lf, optimum = %.3Lf\n", objVarBound(), simplex.optimum()); 

	long double slack = objVarBound() - simplex.optimum(); // can this be sharpend?


	if (slack < 0) {
//		printf("F");
//		for (int i = 0; i < ps.size(); i++) {
//			printf("%d ", sat.level[var(ps[i])]);
//		}
//		printf("\n");
	}

	if (engine.opt_type == OPT_MIN && !propagateBound<1>(0, slack)) return false;
	if (engine.opt_type == OPT_MAX && !propagateBound<0>(0, slack)) return false;

	if (RC_BOUNDS) for (int i = 1; i < vars.size(); i++) {
		if (RL[i] == 0) continue;
		if (simplex.shift[i] == 0 && !propagateBound<0>(i, slack/RL[i])) return false;
		if (simplex.shift[i] == 1 && !propagateBound<1>(i, -slack/RL[i])) return false;
	}

	if (rc) {
//		printf("Slack = %.3f\n", slack);
//		for (int i = 0; i < n; i++) printf("%.3f ", RL[i]);
//		printf("\n");
//		exit(0);
	}

	return true;
}

template <int T>
bool MIP::propagateBound(int i, long double s) {
	if (s > 4e9) return true;
	IntView<T> v(vars[i]);
	int64_t max = v.getMin() + (int64_t) floor(s);
//	fprintf(stderr, "%.3Lf %lld %lld %lld\n", s, v.getMin(), v.getMax(), max);
	if (v.setMaxNotR(max)) {
		Clause *m_r = NULL;
		if (so.lazy) {
			m_r = Clause_new(ps);
			(*m_r)[place[i]] = (*m_r)[0];
			m_r->temp_expl = 1;
			sat.rtrail.last().push(m_r);
		}
		if (!v.setMax(max, m_r)) return false;
	}
	return true;
}

long double MIP::objVarBound() {
	return engine.opt_type == OPT_MIN ? vars[0]->getMax() : -vars[0]->getMin();
}

long double MIP::getRC(IntVar* v) {
	int r = var_map.find(v)->second;
	if (!(0 <= r && r < vars.size())) printf("%d %d\n", r, vars.size());
	assert(0 <= r && r < vars.size());
	if (simplex.ctor[r] == -1) {
		simplex.reduced_costs[r] = simplex.obj[r];
	}
	if (simplex.reduced_costs[r] >= 0) {
		v->preferred_val = PV_MIN;
		if (RAND_RC) return simplex.reduced_costs[r] * myrand(so.rnd_seed) / MYRAND_MAX;
		return simplex.reduced_costs[r];
	} else {
		v->preferred_val = PV_MAX;
		if (RAND_RC) return -simplex.reduced_costs[r] * myrand(so.rnd_seed) / MYRAND_MAX;
		return -simplex.reduced_costs[r];
	}
}


void MIP::updateBounds() {
	// Update all bounds changes
	for (int i = 0; i < new_bc.size(); i++) {
		int v = new_bc[i];
		assert(0 < v && v < vars.size());
		int min = vars[v]->getMin();
		int max = vars[v]->getMax();
		if (min != simplex.lb[v]) {
			assert(min > simplex.lb[v]);
//			fprintf(stderr, "var %d lb changed to %d\n", v, min);
			bctrail.push(BoundChange(v, 0, min-simplex.lb[v]));
			if (simplex.shift[v] == 0) simplex.boundChange(v, min-simplex.lb[v]);
			simplex.lb[v] = min;
		}
		if (max != simplex.ub[v]) {
			assert(max < simplex.ub[v]);
//			fprintf(stderr, "var %d ub changed to %d\n", v, max);
			bctrail.push(BoundChange(v, 1, max-simplex.ub[v]));
			if (simplex.shift[v] == 1) simplex.boundChange(v, max-simplex.ub[v]);
			simplex.ub[v] = max;
		}
	}
	new_bc.clear();
}

int MIP::getLimit() {
  if (so.verbosity >= 2)
    fprintf(stderr, "l = %d\n", decisionLevel());
	if (decisionLevel() == 0) return 100000;
	if (level_lb <= decisionLevel() && decisionLevel() <= level_ub) return 100;
	return DEFAULT_ROUNDS;
}

int MIP::doSimplex() {
//	printf("start simplex\n");
	int r = SIMPLEX_IN_PROGRESS;
	int steps = 0;
	int limit = getLimit();
	for ( ; steps < limit; steps++) {
		if ((r = simplex.simplex()) != SIMPLEX_IN_PROGRESS) break;
//		if (i == limit-1) printf("limit exceeded\n");
//		if (i%10 == 0) printf("Optimum = %.3f, ", optimum());
	}
	simplex.calcObjBound();

//	if (MIP_DEBUG) {
		int bound = (int) ceil((double) simplex.optimum());
		if (engine.opt_type == OPT_MAX) bound = -bound;
		if (steps && so.verbosity >= 2) fprintf(stderr, "level = %d, %d simplex steps, status = %d, bound = %d\n", decisionLevel(), steps, r, bound);
//		fprintf(stderr, "%d simplex steps, status = %d, bound = %d\n", steps, r, bound);
//		fprintf(stderr, "%d %d\n", bound, engine.opt_type == OPT_MIN ? vars[0]->getMin() : -vars[0]->getMax());
//	}
//		exit(0);


	if (decisionLevel() == 0) simplex.saveState(simplex.root);

	return r;
}

void MIP::printStats() {
	printf("%%%%%%mzn-stat: simplex=%lld\n", simplex.simplexs);
	printf("%%%%%%mzn-stat: refactors=%lld\n", simplex.refactors);
}

