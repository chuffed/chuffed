#include <cstdio>
#include <cassert>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/branching/branching.h>
#include <chuffed/vars/modelling.h>
#include <chuffed/ldsb/ldsb.h>

class MagicSquare : public Problem {
public:
	int const n;
	int const sum;
	vec<vec<IntVar*> > x;                           // squares labels

	MagicSquare(int _n) : n(_n), sum(n*(n*n+1)/2) {

		createVars(x, n, n, 1, n*n);

		vec<IntVar*> s;
		flatten(x, s);

		all_different(s);

		vec<vec<IntVar*> > xt;
		transpose(x, xt);

		for (int i = 0; i < n; i++) {
			int_linear(x[i], IRT_EQ, sum);
			int_linear(xt[i], IRT_EQ, sum);
		}

		vec<IntVar*> t1, t2;
		for (int i = 0; i < n; i++) {
			t1.push(x[i][i]);
			t2.push(x[i][n-1-i]);
		}
		int_linear(t1, IRT_EQ, sum);
		int_linear(t2, IRT_EQ, sum);

		branch(s, VAR_INORDER, VAL_MIN);

		output_vars(s);

		if (so.ldsb) {
			// horizontal flip 
			vec<IntVar*> sym1;

			for (int i = 0; i < n; i++) {
				for (int j = 0; j < n/2; j++) {
					sym1.push(x[i][j]);
				}
			}
			for (int i = 0; i < n; i++) {
				for (int j = 0; j < n/2; j++) {
					sym1.push(x[i][n-j-1]);
				}
			}

			var_seq_sym_ldsb(2, n*(n/2), sym1);

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

			var_seq_sym_ldsb(2, n*(n-1)/2, sym2);

		} else if (so.sym_static) {

			int_rel(x[0][0], IRT_LT, x[n-1][0]);
			int_rel(x[0][0], IRT_LT, x[0][n-1]);
			int_rel(x[0][0], IRT_LT, x[n-1][n-1]);
			int_rel(x[n-1][0], IRT_LT, x[0][n-1]);

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

	engine.solve(new MagicSquare(n));

	return 0;
}



