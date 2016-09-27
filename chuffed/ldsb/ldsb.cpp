#include <chuffed/ldsb/ldsb.h>
#include <chuffed/core/propagator.h>
#include <chuffed/core/sat.h>

#define LDSB_DEBUG 0

LDSB ldsb;

//-------

class Symmetry {
public:
	int sym_id;

	Symmetry() : sym_id(ldsb.symmetries.size()) {
		ldsb.symmetries.push(this);
	}

	virtual void init() = 0;
	virtual void processDec(Lit p, int pos) = 0;
	virtual bool processImpl(Clause *r, int pos) = 0;
	virtual Lit getSymLit(Lit p, int r1, int r2) = 0;

	Clause* getSymClause(Clause* r, int r1, int r2) {
		vec<Lit> ps(r->size());
		for (int i = 1; i < r->size(); i++) {
			ps[i] = getSymLit((*r)[i], r1, r2);
			if (sat.value(ps[i]) != l_False) return NULL;
		}
		ps[0] = getSymLit((*r)[0], r1, r2);
		return Clause_new(ps, true);
	}

};

//-------

void LDSB::init() {
	ldsb_time = 0;
	for (int i = 0; i < engine.vars.size(); i++) lookupTable.push();
	for (int i = 0; i < symmetries.size(); i++) symmetries[i]->init();
}

void LDSB::processDec(Lit p) {
	int var_id = sat.c_info[var(p)].cons_id;
	if (var_id == -1) NOT_SUPPORTED;

	vec<pair<int,int> >& syms = lookupTable[var_id];

	for (int i = 0; i < syms.size(); i++) {
		symmetries[syms[i].first]->processDec(p, syms[i].second);
	}
}

bool LDSB::processImpl(Clause *c) {
	ldsb_time -= wallClockTime();

	sym_learnts.clear();
	sl_origin.clear();

	addLearntClause(*c, -1);

	for (int k = 0; k < sym_learnts.size(); k++) {
//	for (int k = 0; k < 1; k++) {
		Lit p = (*sym_learnts[k])[0];

		int var_id = sat.c_info[var(p)].cons_id;
		if (var_id == -1) {
			if (LDSB_DEBUG) printf("Implication ignored\n");
			continue;
		}

		vec<pair<int,int> >& syms = lookupTable[var_id];

		for (int i = 0; i < syms.size(); i++) {
			if (syms[i].first == sl_origin[k]) continue;
			if (!symmetries[syms[i].first]->processImpl(sym_learnts[k], syms[i].second)) {
				ldsb_time += wallClockTime();
				return false;
			}
		}
	}

/*

	printf("Learnt clause: ");
	sat.printClause(*sym_learnts[0]);

	for (int i = 0; i < sym_learnts.size(); i++) {
		printf("%d %d\n", sat.c_info[var((*sym_learnts[i])[0])].cons_id, sat.c_info[var((*sym_learnts[i])[0])].v);
	}
*/
	ldsb_time += wallClockTime();
	return true;
}

void LDSB::addLearntClause(Clause& c, int sym_id) {
	sym_learnts.push(&c);
	sl_origin.push(sym_id);
	if (sym_id == -1) return;
	c.activity() = 1;
	if (c.size() >= 2) {
		if (so.learn) sat.addClause(c, so.one_watch);
		if (!so.learn || c.size() == 2) sat.rtrail.last().push(&c);
	}
	sat.enqueue(c[0], &c);
}


//-----

class VarSym : public Symmetry {
public:
	int n;
	int *vars;
	Tchar *active;

	VarSym(vec<IntVar*>& v) : n(v.size()) {
		vars = (int*) malloc(n * sizeof(int));
		active = (Tchar*) malloc(n * sizeof(Tchar));
		for (int i = 0; i < n; i++) {
			vars[i] = v[i]->var_id;
			active[i] = true;
			// this is not quite good enough
			if (v[i]->getMin() != v[0]->getMin()) NOT_SUPPORTED;
			if (v[i]->getMax() != v[0]->getMax()) NOT_SUPPORTED;
		}
	}

	void init() {
		for (int i = 0; i < n; i++) {
			assert(engine.vars[vars[i]]->getType() == INT_VAR_EL);
			ldsb.lookupTable[vars[i]].push(pair<int,int>(sym_id, i));
		}
	}

	void processDec(Lit p, int pos) {
		assert(active[pos]);
		active[pos] = 0;
		if (LDSB_DEBUG) printf("VarSym: %d, %d broken\n", sym_id, pos);
	}

	bool processImpl(Clause *r, int pos) {
		if (!so.ldsbta && !active[pos]) return true;

		Lit p = (*r)[0];

		for (int i = 0; i < n; i++) {
			if (!so.ldsbta && !active[i]) continue;
			if (i == pos) continue;
			Lit q = getSymLit(p, vars[pos], vars[i]);
			lbool b = sat.value(q);
			if (b == l_True) continue;
			if (b == l_False) {
				// can fail here!
				Clause *c = getSymClause(r, vars[pos], vars[i]);
				if (!c) { if (LDSB_DEBUG) printf("Skip VarSym Failure\n"); continue; }
				c->temp_expl = 1;
				sat.rtrail.last().push(c);
				sat.confl = c;
				if (LDSB_DEBUG) printf("VarSym Failure\n");
				return false;
			}
			Clause *s = getSymClause(r, vars[pos], vars[i]);
			if (!s) {
				if (LDSB_DEBUG) printf("Skip VarSym Implication");
				continue;
			}
			if (LDSB_DEBUG) printf("Extra VarSym implication\n");
			assert((*s)[0] == q);
//			if (!active[pos] || !active[i]) printf("Extra!\n");
			ldsb.addLearntClause(*s, sym_id);
		}

		return true;
	}

	Lit getSymLit(Lit p, int a, int b) {
		int var_id = sat.c_info[var(p)].cons_id;
		Lit q = p;
		// Not very safe!!!!
		if (var_id == a) {
			int base_a = ((IntVarEL*) engine.vars[a])->getBaseVLit();
			int base_b = ((IntVarEL*) engine.vars[b])->getBaseVLit();
			q = toLit(toInt(p) - base_a + base_b);
//			assert(sat.c_info[var(q)].cons_id == b);
		}
		if (var_id == b) {
			int base_a = ((IntVarEL*) engine.vars[a])->getBaseVLit();
			int base_b = ((IntVarEL*) engine.vars[b])->getBaseVLit();
			q = toLit(toInt(p) - base_b + base_a);
//			assert(sat.c_info[var(q)].cons_id == a);
		}

//		assert(sat.c_info[var(q)].v == sat.c_info[var(p)].v);
		return q;
	}

};

//-----

class ValSym : public Symmetry {
public:
	int n;
	int min;
	int max;
	int *vars;
	bool *which_vars;
	bool *active;

	static const int not_a_val = -1000000000;

	ValSym(vec<IntVar*>& v, int _min, int _max) : n(v.size()),
		min(_min), max(_max) {
		vars = (int*) malloc(n * sizeof(int));
		active = (bool*) malloc((max-min+1) * sizeof(bool));
		for (int i = 0; i < n; i++) {
			vars[i] = v[i]->var_id;
			if (v[i]->getMin() > min) NOT_SUPPORTED;
			if (v[i]->getMax() < max) {
				printf("%d %d\n", v[i]->getMax(), max);
				NOT_SUPPORTED;
			}
		}
		for (int i = min; i <= max; i++) active[i-min] = true;
	}

	void init() {
		which_vars = (bool*) malloc(engine.vars.size() * sizeof(bool));
		for (int i = 0; i < engine.vars.size(); i++) which_vars[i] = false;
		for (int i = 0; i < n; i++) {
			assert(engine.vars[vars[i]]->getType() == INT_VAR_EL);
			ldsb.lookupTable[vars[i]].push(pair<int,int>(sym_id, i));
			which_vars[vars[i]] = true;
		}
	}

	void processDec(Lit p, int pos) {
		int v = getLitVal(p);
		if (v == not_a_val) NOT_SUPPORTED;
		assert(engine.vars[sat.c_info[var(p)].cons_id]->getVal() == v);
		if (v < min || v > max) return;
		if (active[v-min]) {
			active[v-min] = 0;
//			printf("Level %d, ValSym: %d, %d broken\n", engine.decisionLevel(), sym_id, v);
		}
	}

	bool processImpl(Clause *r, int pos) {
		Lit p = (*r)[0];

		int v = getLitVal(p);
		assert(v != not_a_val);
		if (v < min || v > max) { if (LDSB_DEBUG) printf("Skip PValSym oor\n"); return true; }
		if (!so.ldsbta && !active[v-min]) return true;

//		Clause *rc = cleanClause(r);
		Clause *rc = r;

		for (int i = min; i <= max; i++) {
			if (!so.ldsbta && !active[i-min]) continue;
			if (i == v) continue;
	//		printf("try %d\n", i);
			Lit q = getSymLit(p, v, i);
			lbool b = sat.value(q);
			if (b == l_True) continue;
			if (b == l_False) {
				Clause *c = getSymClause(rc, v, i);
				if (!c) { if (LDSB_DEBUG) printf("Skip ValSym Failure\n"); continue; }
				c->temp_expl = 1;
				sat.rtrail.last().push(c);
				sat.confl = c;
				if (LDSB_DEBUG) printf("ValSym Failure\n");
//				free(rc);
				return false;
			}
			Clause *s = getSymClause(rc, v, i);
			if (!s) {
				if (LDSB_DEBUG) printf("Skip ValSym implication");
				continue;
			}
			if (LDSB_DEBUG) printf("Level %d, Extra ValSym implication %d -> %d\n", engine.decisionLevel(), v, i);
			assert((*s)[0] == q);
//			if (!active[v-min] || !active[i-min]) printf("Extra!\n");
			ldsb.addLearntClause(*s, sym_id);
		}

//		free(rc);

		return true;
	}

	Clause* cleanClause(Clause *r) {
		vec<Lit> ps;
		ps.push((*r)[0]);

		Clause& c = *r;

		for (int i = 1; i < c.size(); i++) {
			int var_id = sat.c_info[var(c[i])].cons_id;
			// Not in sym, ignore
			if (var_id == -1 || !which_vars[var_id]) {
				ps.push(c[i]);
				continue;
			}
			// In sym, check value
			int v = getLitVal(c[i]);
			// Value is ok, ignore
			if (v != not_a_val) {
				ps.push(c[i]);
				continue;
			}
			// Not ok, must be bounds lit
			if (sat.c_info[var(c[i])].val_type) {
				IntVarEL *var = (IntVarEL*) engine.vars[var_id];
				int v = (toInt(c[i]) - ((IntVarEL*) engine.vars[var_id])->getBaseBLit());
				if (v % 2 == 1) {
					v /= 2;
					// lit means <= v, and is false
					for (int j = min; j <= v; j++) {
						ps.push(var->getLit(j,1));
					}
				} else {
					v /= 2;
					// lit means >= v, and is false
					for (int j = v; j <= max; j++) {
						ps.push(var->getLit(j,1));
					}
				}
				continue;
			}
			NEVER;
		}

		Clause *cc = Clause_new(ps);

		printf("Before clean: "); sat.printClause(*r);
		printf("After clean: "); sat.printClause(*cc);

		return cc;
	}

	Lit getSymLit(Lit p, int a, int b) {
		int var_id = sat.c_info[var(p)].cons_id;
		if (!which_vars[var_id]) return p;
		int v = getLitVal(p);
		if (v == not_a_val) NOT_SUPPORTED;
		Lit q = p;
		if (v == a) {
			q = toLit(toInt(p) - a*2 + b*2);
//			assert(sat.c_info[var(q)].cons_id == var_id);
//			assert(sat.c_info[var(q)].v == sat.c_info[var(p)].v + 4*(b-a));
		}
		if (v == b) {
			q = toLit(toInt(p) - b*2 + a*2);
//			assert(sat.c_info[var(q)].cons_id == var_id);
//			assert(sat.c_info[var(q)].v == sat.c_info[var(p)].v + 4*(a-b));
		}
		return q;
	}

	int getLitVal(Lit p) {
		int var_id = sat.c_info[var(p)].cons_id;
		if (var_id == -1) return not_a_val;
		if (sat.c_info[var(p)].val_type) return not_a_val;
		return (toInt(p) - ((IntVarEL*) engine.vars[var_id])->getBaseVLit())/2;
	}

};

//-----

static const int unfixed = -2000000000;

class VarSeqSym : public Symmetry, public Propagator {
public:
	int n;                                // number of rows
	int m;                                // number of columns
	IntVar ***vars;                       // variables
	vec<vec<int> > occ;                   // where each var occurs in this sym
	vec<vec<Tint> > values;


	VarSeqSym(int _n, int _m, vec<IntVar*>& v) : n(_n), m(_m) {
		if (n*m != v.size()) printf("n = %d, m = %d, v.size() = %d\n", n, m, v.size());
		rassert(n*m == v.size());
		vars = (IntVar***) malloc(n * sizeof(IntVar**));
		for (int i = 0; i < n; i++) {
			vars[i] = (IntVar**) malloc(m * sizeof(IntVar*));
			values.push();
			for (int j = 0; j < m; j++) {
				vars[i][j] = v[i*m+j];
				values[i].push(unfixed);
			}
		}
		priority = 2; 
		for (int i = 0; i < v.size(); i++) v[i]->attach(this, i, EVENT_F);
	}

	void init() {
		for (int i = 0; i < engine.vars.size(); i++) occ.push();
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < m; j++) {
				assert(vars[i][j]->getType() == INT_VAR_EL);
				ldsb.lookupTable[vars[i][j]->var_id].push(pair<int,int>(sym_id, i*m+j));
				occ[vars[i][j]->var_id].push(i*m+j);
			}
		}
	}

	void wakeup(int i, int c) {
		assert(values[i/m][i%m] == unfixed);
		values[i/m][i%m] = vars[i/m][i%m]->getVal();	
	}

	bool propagate() { return true;	}

	void processDec(Lit p, int pos) {}

	bool processImpl(Clause *r, int pos) {
		Lit p = (*r)[0];

		int var_id = sat.c_info[var(p)].cons_id;
		if (var_id == -1) return true;

	//	printf("processing var %d implication\n", sat.c_info[var(p)].cons_id);

		for (int i = 0; i < occ[var_id].size(); i++) {
			int r1 = occ[var_id][i]/m;
			for (int r2 = 0; r2 < n; r2++) {
				if (r1 == r2) continue;
				Lit q = getSymLit(p, r1, r2);
				lbool b = sat.value(q);
				if (b == l_True) continue;
				if (!so.ldsbta && !rowMatch(r1, r2)) continue;
				if (b == l_False) {
					// can fail here!
					Clause *c = getSymClause(r, r1, r2);
					if (!c) { if (LDSB_DEBUG) printf("Skip VarSeqSym Failure\n"); continue; }
					c->temp_expl = 1;
					sat.rtrail.last().push(c);
					sat.confl = c;
					if (LDSB_DEBUG) printf("VarSeqSym Failure\n");
					return false;
				}
				Clause *s = getSymClause(r, r1, r2);
				if (!s) {
					if (LDSB_DEBUG) printf("Skip VarSeqSym implication");
					continue;
				}
				if (LDSB_DEBUG) printf("Extra VarSeqSym implication\n");
				assert((*s)[0] == q);
//				if (!rowMatch(r1, r2)) printf("Extra!\n");
				ldsb.addLearntClause(*s, sym_id);
			}
		}


		return true;
	}

	bool rowMatch(int r1, int r2) {
/*
		for (int i = 0; i < m; i++) {
			IntVarEL* v1 = (IntVarEL*) vars[r1][i];
			IntVarEL* v2 = (IntVarEL*) vars[r2][i];
			if (v1->isFixed()) {
				if (v2->isFixed() && v1->getVal() == v2->getVal()) continue;
				return false;
			} else {
				if (!v2->isFixed()) continue;
				return false;
			}
		}
*/
		for (int i = 0; i < m; i++) {
			if (values[r1][i] != values[r2][i]) return false;
		}

		return true;

	}

	Lit getSymLit(Lit p, int r1, int r2) {
		int var_id = sat.c_info[var(p)].cons_id;
		if (var_id == -1) return p;
		if (occ[var_id].size() == 0) return p;

		for (int i = 0; i < occ[var_id].size(); i++) {
	//		printf("%d %d %d %d\n", var_id, occ.size(), i, occ[var_id].size());
			int r = occ[var_id][i]/m;
			int c = occ[var_id][i]%m;
			// Not very safe!!!!
			if (r == r1) {
				int base_r1 = ((IntVarEL*) vars[r1][c])->getBaseVLit();
				int base_r2 = ((IntVarEL*) vars[r2][c])->getBaseVLit();
				return toLit(toInt(p) - base_r1 + base_r2);
			}
			if (r == r2) {
				int base_r1 = ((IntVarEL*) vars[r1][c])->getBaseVLit();
				int base_r2 = ((IntVarEL*) vars[r2][c])->getBaseVLit();
				return toLit(toInt(p) - base_r2 + base_r1);
			}
		}
		return p;
	}

};

//-----

class ValSeqSym : public Symmetry {
public:
	int n;
	int m;
	int min;
	int max;
	vec<vec<int> > valseqs;
	vec<vec<int> > occ;
	vec<IntVar*> vars;
	bool *which_vars;
	Tchar *active;

	static const int not_a_val = -1000000000;

	ValSeqSym(int _n, int _m, vec<IntVar*>& v, vec<int>& a) : n(_n), m(_m) {
		assert(n*m == a.size());
		min = 1000000000;
		max = -1000000000;
		for (int i = 0; i < a.size(); i++) {
			if (a[i] < min) min = a[i];
			if (a[i] > max) max = a[i];
		}
		for (int i = min; i <= max; i++) occ.push();
		for (int i = 0; i < n; i++) {
			valseqs.push();
			for (int j = 0; j < m; j++) {
				valseqs[i].push(a[i*m+j]);
				occ[a[i*m+j]-min].push(i*m+j);
			}
		}
		for (int i = 0; i < v.size(); i++) {
			vars.push(v[i]);
		}
		active = (Tchar*) malloc(n * sizeof(Tchar));
		for (int i = 0; i < n; i++) active[i] = true;
		for (int i = 0; i < v.size(); i++) {
			assert(v[i]->getMin() == min);
			assert(v[i]->getMax() == max);
		}
	}

	void init() {
		which_vars = (bool*) malloc(engine.vars.size() * sizeof(bool));
		for (int i = 0; i < engine.vars.size(); i++) which_vars[i] = false;
		for (int i = 0; i < vars.size(); i++) {
			assert(vars[i]->getType() == INT_VAR_EL);
			ldsb.lookupTable[vars[i]->var_id].push(pair<int,int>(sym_id, i));
			which_vars[vars[i]->var_id] = true;
		}
	}

	void processDec(Lit p, int pos) {
		int v = getLitVal(p);
		if (v == not_a_val) NOT_SUPPORTED;
		assert(engine.vars[sat.c_info[var(p)].cons_id]->getVal() == v);
		if (v < min || v > max) return;
		for (int i = 0; i < occ[v-min].size(); i++) {
			int p = occ[v-min][i];
			if (active[p/m]) active[p/m] = 0;
		}
	}

	bool processImpl(Clause *r, int pos) {
		Lit p = (*r)[0];

		int v = getLitVal(p);
		if (v == not_a_val) return true;
		if (v < min || v > max) return true;

		Clause *rc = cleanClause(r);

		for (int k = 0; k < occ[v-min].size(); k++) {
			int r1 = occ[v-min][k]/m;
			if (!so.ldsbta && !active[r1]) continue;

			for (int r2 = 0; r2 < n; r2++) {
				if (!so.ldsbta && !active[r2]) continue;
				if (r1 == r2) continue;
				Lit q = getSymLit(p, r1, r2);
				lbool b = sat.value(q);
				if (b == l_True) continue;
				if (b == l_False) {
					Clause *c = getSymClause(rc, r1, r2);
					if (!c) { if (LDSB_DEBUG) printf("Skip ValSeqSym Failure\n"); continue; }
					c->temp_expl = 1;
					sat.rtrail.last().push(c);
					sat.confl = c;
					if (LDSB_DEBUG) printf("ValSeqSym Failure\n");
					free(rc);
					return false;
				}
				Clause *s = getSymClause(rc, r1, r2);
				if (!s) {
					if (LDSB_DEBUG) printf("Skip ValSeqSym implication");
					continue;
				}
		//		printf("Level %d, Extra ValSeqSym implication %d -> %d\n", engine.decisionLevel(), v, i);
				assert((*s)[0] == q);
				ldsb.addLearntClause(*s, sym_id);
			}

		}

		free(rc);

		return true;
	}

	Clause* cleanClause(Clause *r) {
		vec<Lit> ps;
		ps.push((*r)[0]);

		Clause& c = *r;

		for (int i = 1; i < c.size(); i++) {
			int var_id = sat.c_info[var(c[i])].cons_id;
			// Not in sym, ignore
			if (var_id == -1 || !which_vars[var_id]) {
				ps.push(c[i]);
				continue;
			}
			// In sym, check value
			int v = getLitVal(c[i]);
			// Value is ok, ignore
			if (v != not_a_val) {
				ps.push(c[i]);
				continue;
			}
			// Not ok, must be bounds lit
			if (sat.c_info[var(c[i])].val_type) {
				IntVarEL *var = (IntVarEL*) engine.vars[var_id];
				int v = (toInt(c[i]) - ((IntVarEL*) engine.vars[var_id])->getBaseBLit());
				if (v % 2 == 1) {
					v /= 2;
					// lit means <= v, and is false
					for (int j = min; j <= v; j++) {
						ps.push(var->getEQLit2(j));
					}
				} else {
					v /= 2;
					// lit means >= v, and is false
					for (int j = v; j <= max; j++) {
						ps.push(var->getEQLit2(j));
					}
				}
				continue;
			}
			NEVER;
		}

		return Clause_new(ps);
	}

	Lit getSymLit(Lit p, int r1, int r2) {
		int var_id = sat.c_info[var(p)].cons_id;
		if (!which_vars[var_id]) return p;
		int v = getLitVal(p);
		if (v == not_a_val) NOT_SUPPORTED;
		for (int i = 0; i < occ[v-min].size(); i++) {
			int r = occ[v-min][i]/m;
			int c = occ[v-min][i]%m;
			if (r == r1) {
				int v2 = valseqs[r2][c];
				return toLit(toInt(p) - v*2 + v2*2);
			}
			if (r == r2) {
				int v2 = valseqs[r1][c];
				return toLit(toInt(p) - v*2 + v2*2);
			}
		}
		return p;
	}

	int getLitVal(Lit p) {
		int var_id = sat.c_info[var(p)].cons_id;
		if (var_id == -1) return not_a_val;
		if (sat.c_info[var(p)].val_type) return not_a_val;
		return (toInt(p) - ((IntVarEL*) engine.vars[var_id])->getBaseVLit())/2;
	}

};

//-----

void var_sym_ldsb(vec<IntVar*>& x) {
	new VarSym(x);
}

void val_sym_ldsb(vec<IntVar*>& x, int l, int u) {
	new ValSym(x, l, u);
}

void var_seq_sym_ldsb(int n, int m, vec<IntVar*>& x) {
	new VarSeqSym(n, m, x);
}

void val_seq_sym_ldsb(int n, int m, vec<IntVar*>& x, vec<int>& a) {
	new ValSeqSym(n, m, x, a);
}
