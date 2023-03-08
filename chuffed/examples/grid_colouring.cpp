#include <chuffed/branching/branching.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/vars/modelling.h>

#include <cassert>
#include <cstdio>

#define BALANCE 1
#define USE_GLOBAL 1
#define SOFT_LIMIT 0
#define TEST 0

class GridColouring : public Problem {
public:
	// Constants

	int const n;  // number of rows
	int const m;  // number of columns
	int const c;  // number of colours

	// Core variables

	vec<vec<IntVar*> > x;  // colour of each square

	// Intermediate variables

	GridColouring(int _n, int _m, int _c) : n(_n), m(_m), c(_c) {
		// Create vars

		createVars(x, n, m, 1, c, true);

		// Constraints

		// For each rectangle, corners cannot all be the same colour
		for (int r1 = 0; r1 < n; r1++) {
			for (int r2 = r1 + 1; r2 < n; r2++) {
				for (int c1 = 0; c1 < m; c1++) {
					for (int c2 = c1 + 1; c2 < m; c2++) {
						for (int z = 1; z <= c; z++) {
							vec<BoolView> a;
							a.push(BoolView(x[r1][c1]->getLit(z, 0)));
							a.push(BoolView(x[r2][c1]->getLit(z, 0)));
							a.push(BoolView(x[r1][c2]->getLit(z, 0)));
							a.push(BoolView(x[r2][c2]->getLit(z, 0)));
							bool_clause(a);
						}
					}
				}
			}
		}

		// Balance constraints
		if (BALANCE) {
			IntVar* llimit = getConstant(m / c);
			IntVar* ulimit = getConstant(m / c + 1);
			for (int i = 0; i < n; i++) {
				for (int z = 1; z <= c; z++) {
					vec<BoolView> a;
					for (int j = 0; j < m; j++) {
						a.push(BoolView(x[i][j]->getLit(z, 1)));
					}
					bool_linear(a, IRT_LE, ulimit);
					bool_linear(a, IRT_GE, llimit);
				}
			}
		}

		// Mathamatical global constraint
		if (USE_GLOBAL) {
			addGlobalProp();
		}

		// Test
		if (TEST) {
			assert(n == 16);
			assert(m == 16);
			assert(c == 4);
			for (int i = 0; i < 4; i++) {
				for (int j = 0; j < 16; j++) {
					x[i][j]->setVal((i + j / 4) % 4 + 1);
				}
			}
		}

		// Post some branchings

		vec<IntVar*> s;
		flatten(x, s);

		branch(s, VAR_INORDER, VAL_MIN);
	}

	// Function to print out solution

	void print(std::ostream& os) override {
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < m; j++) {
				if (x[i][j]->isFixed()) {
					os << x[i][j]->getVal() << ", ";
				} else {
					os << "?, ";
				}
			}
			os << "\n";
		}
		os << "\n";
	}

	void addGlobalProp();
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	assert(argc == 4);

	int n = atoi(argv[1]);
	int m = atoi(argv[2]);
	int c = atoi(argv[3]);

	engine.solve(new GridColouring(n, m, c));

	return 0;
}

class GridColouringProp : public Propagator {
public:
	// constant data
	GridColouring& p;
	int n_sets;
	int* min_matches;
	int** limits;
	int* set_sizes;

	// Persistent state
	Tint** fixed;
	Tint* counts;
	Tint row;

	//	...

	// Intermediate state
	vec<int> new_fixed;

	//	...

	GridColouringProp(GridColouring& _p) : p(_p), n_sets(1 << p.m), row(0) {
		assert(!so.lazy);
		// set priority
		priority = 2;
		// attach to var events
		for (int i = 0; i < p.n; i++) {
			for (int j = 0; j < p.m; j++) {
				p.x[i][j]->attach(this, i * p.m + j, EVENT_F);
			}
		}
		set_sizes = (int*)malloc(n_sets * sizeof(int));
		for (int i = 0; i < n_sets; i++) {
			set_sizes[i] = 0;
			for (int j = i; j != 0; set_sizes[i]++) {
				j &= j - 1;
			}
		}
		fixed = (Tint**)malloc(p.n * sizeof(Tint*));
		for (int i = 0; i < p.n; i++) {
			fixed[i] = (Tint*)malloc(p.m * sizeof(Tint));
			for (int j = 0; j < p.m; j++) {
				fixed[i][j] = 0;
			}
		}
		counts = (Tint*)malloc(n_sets * sizeof(Tint));
		for (int i = 0; i < n_sets; i++) {
			counts[i] = 0;
		}
		calcLimits();
	}

	void calcLimits() {
		min_matches = (int*)malloc((p.m + 1) * sizeof(int));
		printf("min_matches:\n");
		for (int i = 0; i <= p.m; i++) {
			int b = i / p.c;
			int e = i % p.c;
			min_matches[i] = p.c * b * (b - 1) / 2 + e * b;
			printf("%d, ", min_matches[i]);
		}
		printf("\n");
		limits = (int**)malloc((p.n + 1) * sizeof(int*));
		for (int j = 0; j <= p.n; j++) {
			limits[j] = (int*)malloc((p.m + 1) * sizeof(int));
			printf("limits[%d]: ", j);
			for (int i = 0; i <= p.m; i++) {
				int hard_limit = i * (i - 1) / 2 * p.c - (p.n - j) * min_matches[i];
				int soft_limit = (int)ceil((double)i * static_cast<int>(p.m / p.c) / 2 +
																	 (double)j * i * (i - 1) / 2 / p.c);
				//				int soft_limit = (int) ceil((double)i*(p.m/p.c)/2 +
				//((double)i*(i-1)/2*p.c-(double)i*(p.m/p.c)/2)*j/p.n);
				limits[j][i] = hard_limit;
				if (SOFT_LIMIT && soft_limit < limits[j][i]) {
					limits[j][i] = soft_limit;
				}
				printf("%d, ", limits[j][i]);
			}
			printf("\n");
		}
	}

	void wakeup(int i, int c) override {
		new_fixed.push(i);
		pushInQueue();
	}

	bool propagate() override {
		for (int i = 0; i < new_fixed.size(); i++) {
			int r = new_fixed[i] / p.m;
			int c = new_fixed[i] % p.m;
			if (TEST && r != row) {
				row = r;
				printf("Processing %dth row\n", (int)row);
			}
			if (r != row) {
				printf("r = %d, c = %d\n", r, c);
				for (int i = 0; i < p.n; i++) {
					for (int j = 0; j < p.m; j++) {
						if (p.x[i][j]->isFixed()) {
							printf("%d, ", p.x[i][j]->getVal());
						} else {
							printf("?, ");
						}
					}
					printf("\n");
				}
				printf("\n");
			}

			assert(r == row);
			IntVar* v = p.x[r][c];
			for (int j = 0; j < p.m; j++) {
				if (fixed[row][j] == 0) {
					continue;
				}
				if (p.x[row][j]->getVal() != v->getVal()) {
					continue;
				}
				int s;
				int b;
				if (j < c) {
					s = j;
					b = c;
				} else {
					s = c;
					b = j;
				}
				int size1 = (1 << s);
				int size2 = (1 << (b - s - 1));
				int size3 = (1 << (p.m - b - 1));
				for (int v3 = 0; v3 < size3; v3++) {
					for (int v2 = 0; v2 < size2; v2++) {
						for (int v1 = 0; v1 < size1; v1++) {
							int z = v1 + (1 << s) + (v2 << (s + 1)) + (1 << b) + (v3 << (b + 1));
							counts[z] = counts[z] + 1;
							if (counts[z] > limits[row + 1][set_sizes[z]]) {
								printf("z = %d %x, counts[z] = %d\n", z, z, (int)counts[z]);
								printf("row+1 = %d, set_sizes[z] = %d, limit = %d\n", row + 1, set_sizes[z],
											 limits[row + 1][set_sizes[z]]);
								return false;
							}
						}
					}
				}
			}
			fixed[r][c] = 1;
		}
		bool finished_row = true;
		for (int j = 0; j < p.m; j++) {
			if (!p.x[row][j]->isFixed()) {
				finished_row = false;
				break;
			}
		}
		if (finished_row) {
			row = row + 1;
		}
		return true;
	}

	void clearPropState() override {
		in_queue = false;
		new_fixed.clear();
	}
};

void GridColouring::addGlobalProp() { new GridColouringProp(*this); }
