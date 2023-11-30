#include "chuffed/core/engine.h"
#include "chuffed/core/propagator.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/core/sat.h"
#include "chuffed/primitives/primitives.h"
#include "chuffed/support/misc.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/vars.h"

#include <cassert>
#include <cstdio>

class TableChecker : public Checker {
	vec<IntVar*> x;
	vec<vec<int> > t;

	TableChecker(vec<IntVar*>& /*x*/, vec<vec<int> >& /*t*/) { NOT_SUPPORTED; }

	bool check() override { NOT_SUPPORTED; }
};

void table_GAC(vec<IntVar*>& x, vec<vec<int> >& t) {
	assert(x.size() >= 2);
	for (int i = 0; i < x.size(); i++) {
		x[i]->specialiseToEL();
	}
	const int base_lit = 2 * sat.nVars();
	if (x.size() != 2) {
		for (int i = 0; i < t.size(); i++) {
			sat.newVar();
			for (int j = 0; j < x.size(); j++) {
				sat.addClause(toLit(base_lit + 2 * i), x[j]->getLit(t[i][j], LR_EQ));
			}
		}
	}
	for (int w = 0; w < x.size(); w++) {
		const int sup_off = x[w]->getMin();
		vec<vec<Lit> > sup;
		for (int i = sup_off; i <= x[w]->getMax(); i++) {
			sup.push();
		}
		for (int i = 0; i < t.size(); i++) {
			const int k = t[i][w] - sup_off;
			if (k < 0 || k >= sup.size()) {
				if (DEBUG) {
					printf("Warning: useless tuple (");
					for (int j = 0; j < x.size(); j++) {
						printf("%d, ", t[i][j]);
					}
					printf(")\n");
				}
				continue;
			}
			if (x.size() == 2) {
				sup[k].push(x[1 - w]->getLit(t[i][1 - w], LR_EQ));
			} else {
				sup[k].push(toLit(base_lit + 2 * i + 1));
			}
		}
		for (int i = 0; i < sup.size(); i++) {
			if (sup[i].size() == 0) {
				int_rel(x[w], IRT_NE, i + sup_off);
				continue;
			}
			assert(sup[i].size() >= 1);
			assert(i + sup_off <= x[w]->getMax());
			sup[i].push(x[w]->getLit(i + sup_off, LR_NE));
			const Lit p = sup[i][0];
			sup[i][0] = sup[i].last();
			sup[i].last() = p;
			sat.addClause(sup[i]);
		}
	}
}

void table(vec<IntVar*>& x, vec<vec<int> >& t) { table_GAC(x, t); }
