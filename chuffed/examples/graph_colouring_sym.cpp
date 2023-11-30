#include "chuffed/branching/branching.h"
#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/core/sat.h"
#include "chuffed/globals/globals.h"
#include "chuffed/ldsb/ldsb.h"
#include "chuffed/primitives/primitives.h"
#include "chuffed/support/misc.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/modelling.h"
#include "chuffed/vars/vars.h"

#include <cassert>
#include <cstdio>
#include <ostream>

class GraphColouringSym : public Problem {
public:
	// Constants
	int v;  // Number of vertices
	int p;

	// Core variables

	vec<IntVar*> x;   // Vectex labels
	IntVar* colours;  // Number of colours

	vec<vec<IntVar*> > partitions;

	GraphColouringSym(char* filename) {
		FILE* fp = fopen(filename, "r");
		int temp;
		int temp2;

		rassert(fscanf(fp, "%d\n", &v) == 1);
		rassert(fscanf(fp, "%d\n", &p) == 1);

		partitions.growTo(p);
		for (int i = 0; i < p; i++) {
			int x_size = x.size();
			rassert(fscanf(fp, "%d %d\n", &temp, &temp2) == 2);
			for (int j = 0; j < temp; j++) {
				x.push(newIntVar(1, v));
				partitions[i].push(x.last());
			}
			if (temp2 == 1) {
				for (int j = 0; j < temp; j++) {
					for (int k = j + 1; k < temp; k++) {
						int_rel(x[x_size + j], IRT_NE, x[x_size + k]);
					}
				}
			}
		}

		assert(x.size() == v);

		createVar(colours, 0, v);

		// Post some constraints

		for (int i = 0; i < v; i++) {
			int_rel(x[i], IRT_LE, colours);
		}

		int b;

		rassert(fscanf(fp, "%d\n", &b) == 1);

		for (int i = 0; i < b; i++) {
			int p1;
			int p2;
			rassert(fscanf(fp, "%d %d\n", &p1, &p2) == 2);
			for (int j = 0; j < partitions[p1].size(); j++) {
				for (int k = 0; k < partitions[p2].size(); k++) {
					int_rel(partitions[p1][j], IRT_NE, partitions[p2][k]);
				}
			}
		}

		fclose(fp);

		// Post some branchings

		branch(x, VAR_INORDER, VAL_MIN);
		optimize(colours, OPT_MIN);

		// Declare output variables (optional)

		output_vars(x);

		// Declare symmetries (optional)

		if (so.ldsb) {
			val_sym_ldsb(x, 1, v);
			for (int i = 0; i < p; i++) {
				var_sym_ldsb(partitions[i]);
			}
		} else if (so.sym_static) {
			val_sym_break(x, 1, v);
			for (int i = 0; i < p; i++) {
				var_sym_break(partitions[i]);
			}
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
			((IntVarEL*)x[i])->setVDecidable(true);
		}
	}

	// Function to print out solution

	void print(std::ostream& os) override {
		for (int i = 0; i < p; i++) {
			os << "|P" << i << ": ";
			for (int j = 0; j < partitions[i].size(); j++) {
				os << partitions[i][j]->getVal() << ", ";
			}
		}
		os << "\n";
		//		fprintf(stderr, "Objective = %d\n", colours->getVal());
		// hack for this problem
		if (so.ldsb) {
			int* a = (int*)ldsb.symmetries[0];
			//			for (int i = 0; i < 6; i++) printf("%d ", a[i]); printf("\n");
			a[5] = colours->getVal() - 1;
		}
	}
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	assert(argc == 2);

	engine.solve(new GraphColouringSym(argv[1]));

	return 0;
}
