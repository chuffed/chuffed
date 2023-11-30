#include "chuffed/branching/branching.h"
#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/globals/globals.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/modelling.h"

#include <cassert>
#include <cstdlib>
#include <ostream>

class ProblemName : public Problem {
public:
	// Constants

	int n;  // size of problem

	// Core variables

	vec<IntVar*> x;  // some vars

	// Intermediate variables

	//...

	ProblemName(int _n) : n(_n) {
		// Create vars

		createVars(x, n, 1, n);

		// Post some constraints

		all_different(x);

		// Post some branchings

		branch(x, VAR_INORDER, VAL_MIN);

		// Declare output variables (optional)

		output_vars(x);

		// Declare symmetries (optional)

		var_sym_break(x);
	}

	// Function to print out solution
	void print(std::ostream& out) override {
		for (int i = 0; i < n; i++) {
			out << x[i]->getVal() << ", ";
		}
		out << "\n";
	};
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	int n;

	assert(argc == 2);
	n = atoi(argv[1]);

	engine.solve(new ProblemName(n));

	return 0;
}
