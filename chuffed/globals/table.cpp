#include <chuffed/core/propagator.h>

class TableChecker : public Checker {
	vec<IntVar*> x;
	vec<vec<int> > t;

	TableChecker(vec<IntVar*>& _x, vec<vec<int> >& _t) {
		NOT_SUPPORTED;
	}

	bool check() {
		NOT_SUPPORTED;
	}


};

void table_GAC(vec<IntVar*>& x, vec<vec<int> >& t) {
	assert(x.size() >= 2);
	for (int i = 0; i < x.size(); i++) x[i]->specialiseToEL();
	int base_lit = 2*sat.nVars();
	if (x.size() != 2) {
		for (int i = 0; i < t.size(); i++) {
			sat.newVar();
			for (int j = 0; j < x.size(); j++) {
				sat.addClause(toLit(base_lit+2*i), x[j]->getLit(t[i][j], 1));
			}
		}
	}
	for (int w = 0; w < x.size(); w++) {
		int sup_off = x[w]->getMin();
		vec<vec<Lit> > sup;
		for (int i = sup_off; i <= x[w]->getMax(); i++) sup.push();
		for (int i = 0; i < t.size(); i++) {
			int k = t[i][w]-sup_off;
			if (k < 0 || k >= sup.size()) {
				if (DEBUG) {
					printf("Warning: useless tuple (");
					for (int j = 0; j < x.size(); j++) printf("%d, ", t[i][j]);
					printf(")\n");
				}
				continue;
			}
			if (x.size() == 2) sup[k].push(x[1-w]->getLit(t[i][1-w], 1));
			else sup[k].push(toLit(base_lit+2*i+1));
		}
		for (int i = 0; i < sup.size(); i++) {
			if (sup[i].size() == 0) {
				int_rel(x[w], IRT_NE, i+sup_off);
				continue;
			}
			assert(sup[i].size() >= 1);
			assert(i+sup_off <= x[w]->getMax());
			sup[i].push(x[w]->getLit(i+sup_off, 0));
			Lit p = sup[i][0]; sup[i][0] = sup[i].last(); sup[i].last() = p;
			sat.addClause(sup[i]);
		}
	}
}

void table(vec<IntVar*>& x, vec<vec<int> >& t) {
	table_GAC(x, t);
}
