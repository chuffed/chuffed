#include <chuffed/branching/branching.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/ldsb/ldsb.h>
#include <chuffed/vars/modelling.h>

#include <cassert>
#include <cstdio>
#include <iomanip>

class GracefulGraph : public Problem {
public:
	int const m;      // size of cliques
	int const n;      // number of cliques
	vec<IntVar*> x;   // vertex labels
	vec<IntVar*> d;   // raw difference of vertex labels
	vec<IntVar*> ad;  // absolute differences of vertex labels

	GracefulGraph(int _m, int _n) : m(_m), n(_n) {
		int nodes = m * n;
		int nedges = m * (m - 1) / 2 * n + (n - 1) * m;

		vec<int> origins;
		vec<int> destinations;

		for (int i = 0; i < n; i++) {
			for (int j = 0; j < m; j++) {
				for (int k = j + 1; k < m; k++) {
					origins.push(i * m + j);
					destinations.push(i * m + k);
				}
			}
		}
		for (int i = 0; i < n - 1; i++) {
			for (int j = 0; j < m; j++) {
				origins.push(i * m + j);
				destinations.push((i + 1) * m + j);
			}
		}

		assert(origins.size() == nedges);

		createVars(x, nodes, 0, nedges);
		createVars(d, nedges, -nedges, nedges);
		createVars(ad, nedges, 1, nedges);

		for (int i = 0; i < nedges; i++) {
			int_minus(x[origins[i]], x[destinations[i]], d[i]);
			int_abs(d[i], ad[i]);
		}

		all_different(x);
		all_different(ad);

		branch(x, VAR_INORDER, VAL_MIN);
		//		branch(x, VAR_SIZE_MIN, VAL_MIN);

		output_vars(x);

		if (so.ldsb) {
			// clique sym
			vec<IntVar*> sym1;
			for (int i = 0; i < m; i++) {
				for (int j = 0; j < n; j++) {
					sym1.push(x[j * m + i]);
				}
			}
			var_seq_sym_ldsb(m, n, sym1);

			// flip sym
			vec<IntVar*> sym2;

			for (int i = 0; i < n / 2; i++) {
				for (int j = 0; j < m; j++) {
					sym2.push(x[i * m + j]);
				}
			}
			for (int i = 0; i < n / 2; i++) {
				for (int j = 0; j < m; j++) {
					sym2.push(x[(n - 1 - i) * m + j]);
				}
			}

			var_seq_sym_ldsb(2, m * (n / 2), sym2);

			// flip values symmetry

			vec<int> sym3;
			for (int i = 0; i <= nedges; i++) sym3.push(i);
			for (int i = 0; i <= nedges; i++) sym3.push(nedges - i);

			val_seq_sym_ldsb(2, nedges + 1, x, sym3);

		} else if (so.sym_static) {
			for (int i = 0; i < m - 1; i++) {
				int_rel(x[i], IRT_LT, x[i + 1]);
			}
			for (int i = 0; i < m; i++) {
				int_rel(x[0], IRT_LT, x[(n - 1) * m + i]);
			}
		}
	}

	void restrict_learnable() {
		printf("Setting learnable white list\n");
		for (int i = 0; i < sat.nVars(); i++) sat.flags[i] = 0;
		for (int i = 0; i < x.size(); i++) {
			assert(x[i]->getType() == INT_VAR_EL);
			((IntVarEL*)x[i])->setVLearnable();
			((IntVarEL*)x[i])->setVDecidable(true);
		}
	}

	void print(std::ostream& os) {
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < m; j++) {
				os << " " << std::setw(4) << std::setfill('0') << x[i * m + j]->getVal() << ", ";
			}
			os << " | ";
			for (int j = 0; j < m; j++) {
				for (int k = j + 1; k < m; k++) {
					os << " " << std::setw(4) << std::setfill('0')
						 << ((int)abs(x[i * m + j]->getVal() - x[i * m + k]->getVal())) << ", ";
				}
			}
			os << "\n";
		}
		os << "\n";
	}
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	int m, n;

	assert(argc == 3);
	m = atoi(argv[1]);
	n = atoi(argv[2]);

	engine.solve(new GracefulGraph(m, n));

	return 0;
}
