#include "chuffed/branching/branching.h"
#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/core/sat.h"
#include "chuffed/globals/globals.h"
#include "chuffed/ldsb/ldsb.h"
#include "chuffed/primitives/primitives.h"
#include "chuffed/support/misc.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/bool-view.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/modelling.h"
#include "chuffed/vars/vars.h"

#include <cassert>
#include <cstdio>
#include <ostream>

class ConcertHall : public Problem {
public:
	int n;           // number of offers
	int k;           // number of halls
	vec<int> start;  // start times
	vec<int> end;    // end times
	vec<int> price;  // prices

	vec<IntVar*> x;   // hall assignment
	vec<BoolView> t;  // take offer or not
	vec<IntVar*> bi;  // bool2int version of t
	vec<BoolView> qs;
	IntVar* total;  // total profit

	ConcertHall(char* filename) : k(8) {
		readData(filename);

		createVars(x, n, 0, k, true);
		createVars(t, n);
		createVars(bi, n, 0, 1);
		createVar(total, 0, 500000, true);

		for (int i = 0; i < n; i++) {
			bool2int(t[i], bi[i]);
		}

		for (int i = 0; i < n; i++) {
			int_rel_reif(x[i], IRT_NE, k, t[i]);
		}

		for (int i = 0; i < n; i++) {
			for (int j = i + 1; j < n; j++) {
				if (start[i] > end[j] || start[j] > end[i]) {
					continue;
				}
				/*
								vec<BoolView> y;
								BoolView q = newBoolVar();
								int_rel_reif(x[i], IRT_NE, x[j], q);
								y.push(~t[i]);
								y.push(~t[j]);
								y.push(q);
								bool_clause(y);
				*/
				BoolView q = newBoolVar();
				qs.push(q);
				int_rel_reif(x[i], IRT_NE, x[j], q);
				bool_rel(~t[i], BRT_OR, q);
				bool_rel(~t[j], BRT_OR, q);
			}
		}

		bi.push(total);
		price.push(-1);

		int_linear(price, bi, IRT_GE, 0);

		branch(x, VAR_INORDER, VAL_MIN);
		//		branch(x, VAR_SIZE_MIN, VAL_MIN);

		output_vars(x);

		optimize(total, OPT_MAX);

		if (so.ldsb) {
			val_sym_ldsb(x, 0, k - 1);
		} else if (so.sym_static) {
			val_sym_break(x, 0, k - 1);
		}

		// order syms

		vec<IntVar*> sym;

		for (int base = 0; base < n;) {
			int i = base;
			while (i < n && start[i] == start[base] && end[i] == end[base] && price[i] == price[base]) {
				printf("%d, ", i);
				sym.push(x[i]);
				i++;
			}
			printf("\n");
			if (so.ldsb) {
				var_sym_ldsb(sym);
			} else if (so.sym_static) {
				var_sym_break(sym);
			}
			sym.clear();
			base = i;
		}
	}

	void restrict_learnable() override {
		printf("Setting learnable white list\n");
		for (int i = 0; i < sat.nVars(); i++) {
			sat.flags[i] = 0;
		}
		for (int i = 0; i < x.size(); i++) {
			assert(x[i]->getType() == INT_VAR_EL);
			((IntVarEL*)x[i])->setVLearnable();
		}
		for (int i = 0; i < bi.size(); i++) {
			assert(bi[i]->getType() == INT_VAR_EL);
			((IntVarEL*)bi[i])->setVLearnable();
			((IntVarEL*)bi[i])->setBLearnable();
		}
		for (int i = 0; i < t.size(); i++) {
			sat.flags[var(t[i].getLit(false))].setLearnable(true);
			sat.flags[var(t[i].getLit(false))].setUIPable(true);
		}
		for (int i = 0; i < qs.size(); i++) {
			sat.flags[var(qs[i].getLit(false))].setLearnable(true);
			sat.flags[var(qs[i].getLit(false))].setUIPable(true);
		}
	}

	void readData(char* filename) {
		FILE* fp = fopen(filename, "r");

		rassert(fscanf(fp, "%d\n", &n) == 1);

		start.growTo(n);
		end.growTo(n);
		price.growTo(n);

		for (int i = 0; i < n; i++) {
			rassert(fscanf(fp, "%d %d %d\n", &start[i], &end[i], &price[i]) == 3);
		}
	}

	void print(std::ostream& os) override {
		for (int i = 0; i < n; i++) {
			os << x[i]->getVal() << ", ";
		}
		os << "\n";
	}
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	assert(argc == 2);

	engine.solve(new ConcertHall(argv[1]));

	return 0;
}
