#include <chuffed/branching/branching.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/ldsb/ldsb.h>
#include <chuffed/vars/modelling.h>

#include <cassert>
#include <cstdio>

class LatinSquare : public Problem {
public:
	int const n;
	vec<vec<IntVar*> > x;  // squares labels

	LatinSquare(int _n) : n(_n) {
		createVars(x, n, n, 1, n);

		vec<vec<IntVar*> > xt;
		transpose(x, xt);

		for (int i = 0; i < n; i++) {
			all_different(x[i]);
			all_different(xt[i]);
		}

		vec<IntVar*> s;
		flatten(x, s);

		branch(s, VAR_INORDER, VAL_MIN);
		//		branch(s, VAR_SIZE_MIN, VAL_MIN);

		output_vars(s);

		if (so.ldsb) {
			// row sym
			vec<IntVar*> sym1;
			flatten(x, sym1);
			var_seq_sym_ldsb(n, n, sym1);

			// column sym
			vec<IntVar*> sym2;
			flatten(xt, sym2);
			var_seq_sym_ldsb(n, n, sym2);

			// value sym
			val_sym_ldsb(s, 1, n);

		} else if (so.sym_static) {
			for (int i = 0; i < n; i++) {
				int_rel(x[0][i], IRT_EQ, i + 1);
			}
			for (int i = 1; i < n; i++) {
				int_rel(x[i][0], IRT_EQ, i + 1);
			}
		}
	}

	void restrict_learnable() {
		printf("Setting learnable white list\n");
		for (int i = 0; i < sat.nVars(); i++) sat.flags[i] = 0;
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				assert(x[i][j]->getType() == INT_VAR_EL);
				((IntVarEL*)x[i][j])->setVLearnable();
				((IntVarEL*)x[i][j])->setVDecidable(true);
			}
		}
	}

	void print(std::ostream& os) {
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

	engine.solve(new LatinSquare(n));

	return 0;
}
