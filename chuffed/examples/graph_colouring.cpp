#include <cstdio>
#include <cassert>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/branching/branching.h>
#include <chuffed/vars/modelling.h>

class GraphColouring : public Problem {
public:
	// Constants
	int v;                                          // Number of vertices
	int e;                                          // Number of edges
	vec<int> origins;                               // Origin of edge i
	vec<int> destinations;                          // Destination of edge i

	// Core variables

	vec<IntVar*> x;                                 // Vectex labels
	IntVar* colours;                                // Number of colours

	GraphColouring(char* filename) {

		int max_degree = v-1;

		// Create vars

		createVars(x, v, 1, max_degree+1);
		createVar(colours, 0, max_degree+1);

		// Post some constraints

		for (int i = 0; i < v; i++) {
			int_rel(x[i], IRT_LE, colours);
		}

		for (int i = 0; i < e; i++) {
			int_rel(x[origins[i]], IRT_NE, x[destinations[i]]);
		}

		// Post some branchings

		branch(x, VAR_INORDER, VAL_MIN);
		optimize(colours, OPT_MIN);

		// Declare output variables (optional)

		output_vars(x);

		// Declare symmetries (optional)

		val_sym_break(x, 1, max_degree+1);

	}

	// Function to print out solution

  void print(std::ostream& os) {
		for (int i = 0; i < v; i++) {
			os << x[i]->getVal() << ", ";
		}
		os << "\n";
	}

};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	assert(argc == 2);

	engine.solve(new GraphColouring(argv[1]));

	return 0;
}



