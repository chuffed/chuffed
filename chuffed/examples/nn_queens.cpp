#include "chuffed/branching/branching.h"
#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/core/sat.h"
#include "chuffed/globals/globals.h"
#include "chuffed/ldsb/ldsb.h"
#include "chuffed/primitives/primitives.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/modelling.h"
#include "chuffed/vars/vars.h"

#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <ostream>

class NNQueens : public Problem {
public:
	const int n;
	vec<vec<IntVar*> > x;  // squares labels

	NNQueens(int _n) : n(_n) {
		createVars(x, n, n, 1, n);

		vec<vec<IntVar*> > xt;
		transpose(x, xt);

		for (int i = 0; i < n; i++) {
			all_different(x[i]);
			all_different(xt[i]);
		}

		for (int d = 1; d < 2 * n - 2; d++) {
			vec<IntVar*> t;
			for (int i = 0; i < n; i++) {
				if (d - i < 0 || d - i >= n) {
					continue;
				}
				t.push(x[i][d - i]);
			}
			all_different(t);
		}

		for (int d = -(n - 2); d <= n - 2; d++) {
			vec<IntVar*> t;
			for (int i = 0; i < n; i++) {
				if (i - d < 0 || i - d >= n) {
					continue;
				}
				t.push(x[i][i - d]);
			}
			all_different(t);
		}

		vec<IntVar*> s;
		flatten(x, s);

		branch(s, VAR_INORDER, VAL_MIN);
		//		branch(s, VAR_SIZE_MIN, VAL_MIN);

		output_vars(s);

		if (so.ldsb) {
			val_sym_ldsb(s, 1, n);

			// horizontal flip
			vec<IntVar*> sym1;

			for (int i = 0; i < n; i++) {
				for (int j = 0; j < n / 2; j++) {
					sym1.push(x[i][j]);
				}
			}
			for (int i = 0; i < n; i++) {
				for (int j = 0; j < n / 2; j++) {
					sym1.push(x[i][n - j - 1]);
				}
			}

			var_seq_sym_ldsb(2, n * (n / 2), sym1);

			// diagonal sym
			vec<IntVar*> sym2;

			for (int i = 0; i < n; i++) {
				for (int j = 0; j < i; j++) {
					sym2.push(x[i][j]);
				}
			}
			for (int i = 0; i < n; i++) {
				for (int j = 0; j < i; j++) {
					sym2.push(x[j][i]);
				}
			}

			var_seq_sym_ldsb(2, n * (n - 1) / 2, sym2);

		} else if (so.sym_static) {
			for (int i = 0; i < n; i++) {
				int_rel(x[0][i], IRT_EQ, i + 1);
			}
		}
	}

	void restrict_learnable() override {
		printf("Setting learnable white list\n");
		for (int i = 0; i < sat.nVars(); i++) {
			sat.flags[i] = 0;
		}
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				assert(x[i][j]->getType() == INT_VAR_EL);
				((IntVarEL*)x[i][j])->setVLearnable();
				((IntVarEL*)x[i][j])->setVDecidable(true);
			}
		}
	}

	void print(std::ostream& os) override {
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				os << x[i][j]->getVal() << ", ";
			}
			os << "\n";
		}
		os << "\n";
	}
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	int n;

	assert(argc == 2);
	n = atoi(argv[1]);

	engine.solve(new NNQueens(n));

	return 0;
}
