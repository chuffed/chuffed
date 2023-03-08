#include <chuffed/branching/branching.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/vars/modelling.h>

#include <cassert>
#include <cstdio>

static const int length[] = {0, 0, 1, 3, 6, 11, 17, 25, 34, 44, 55, 72, 85, 106, 127};

class GolombRuler : public Problem {
public:
	// Constants

	int n;  // size of problem

	// Core variables

	vec<IntVar*> x;  // some vars

	// Intermediate variables

	//...

	int diag(int i, int j) const { return (i * (2 * n - i - 1)) / 2 + j - i - 1; }

	GolombRuler(int _n) : n(_n) {
		// Create vars

		createVars(x, n, 0, n * n);

		// Post some constraints

		int_rel(x[0], IRT_EQ, 0);

		vec<IntVar*> d;
		for (int j = 1; j < n; j++) {
			d.push(x[j]);
			int_rel(x[j], IRT_GE, length[j + 1]);
		}
		for (int i = 1; i < n; i++) {
			for (int j = i + 1; j < n; j++) {
				IntVar* v = newIntVar(0, n * n);
				int_minus(x[j], x[i], v);
				int_rel(v, IRT_GE, length[j - i + 1]);
				d.push(v);
			}
		}

		all_different(d);

		// Sym break
		vec<int> a;
		vec<IntVar*> y;
		a.push(1);
		y.push(x[1]);
		a.push(1);
		y.push(x[n - 2]);
		a.push(-1);
		y.push(x[n - 1]);
		int_linear(a, y, IRT_LT, 0);

		// Post some branchings

		branch(x, VAR_INORDER, VAL_MIN);

		optimize(x[n - 1], OPT_MIN);
	}

	// Function to print out solution

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

	engine.solve(new GolombRuler(atoi(argv[1])));

	return 0;
}
