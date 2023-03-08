#include <chuffed/branching/branching.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/vars/modelling.h>

#include <cassert>
#include <cmath>
#include <cstdio>

class Photo : public Problem {
public:
	// Constants

	int n_names;
	int n_prefs;
	int* prefs;

	// Core variables

	vec<IntVar*> x;
	vec<BoolView> f;
	IntVar* sat;

	Photo() {
		srand(so.rnd_seed);
		//		n_names = 12 + (int) floor((double) rand()/RAND_MAX*4);
		//		n_prefs = 24 + (int) floor((double) rand()/RAND_MAX*12);
		n_names = 10 + (int)floor((double)rand() / RAND_MAX * 3);
		n_prefs = 20 + (int)floor((double)rand() / RAND_MAX * 10);
		prefs = (int*)malloc(static_cast<size_t>(2 * n_prefs) * sizeof(int));
		for (int i = 0; i < 2 * n_prefs; i++) {
			prefs[i] = rand() % n_names;
		}

		printf("%d preferences\n", n_prefs);

		// Create vars

		createVars(x, n_names, 1, n_names);
		createVars(f, 2 * n_prefs);
		createVar(sat, 0, n_prefs);

		// Post some constraints

		// Map preferences to fulfilment
		for (int i = 0; i < n_prefs; i++) {
			int_rel_reif(x[prefs[2 * i + 0]], IRT_EQ, x[prefs[2 * i + 1]], f[2 * i], 1);
			int_rel_reif(x[prefs[2 * i + 0]], IRT_EQ, x[prefs[2 * i + 1]], f[2 * i + 1], -1);
		}

		// Sum of fulfilment
		bool_linear(f, IRT_GE, sat);

		all_different(x);

		// Break some symmetries
		int_rel(x[0], IRT_LT, x[1]);

		// Post some branchings

		//		branch(x, VAR_INORDER, VAL_MIN);
		branch(x, VAR_DEGREE_MAX, VAL_MIN);

		// Declare output variables (optional)

		optimize(sat, OPT_MAX);
	}

	// Function to print out solution

	void print(std::ostream& os) override {
		for (int i = 0; i < n_names; i++) {
			os << x[i]->getVal() << ", ";
		}
		os << std::endl;
		os << "SAT = " << sat->getVal() << "\n";
	}
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	engine.solve(new Photo());

	return 0;
}
