#include "chuffed/branching/branching.h"
#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/globals/globals.h"
#include "chuffed/primitives/primitives.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/modelling.h"

#include <cassert>
#include <cstdlib>
#include <ostream>

class MOSP : public Problem {
public:
	int n;
	int m;
	bool** a;
	vec<IntVar*> s;
	vec<IntVar*> e;
	vec<vec<BoolView> > sb;
	vec<vec<BoolView> > eb;
	vec<vec<BoolView> > o;

	IntVar* stacks;

	MOSP(int _n, int _m) : n(_n), m(_m) {
		generateInstance();

		createVars(s, n, 0, n - 1);
		createVars(e, n, 0, n - 1);
		createVars(sb, n, n);
		createVars(eb, n, n);
		createVars(o, n, n);
		createVar(stacks, 0, n);

		// create customer graph
		bool g[n][n];
		for (int i = 0; i < n; i++) {
			for (int j = 0; j < n; j++) {
				g[i][j] = false;
				for (int k = 0; k < m; k++) {
					if (a[i][k] && a[j][k]) {
						g[i][j] = true;
						break;
					}
				}
			}
		}

		// AllDiff constraint on e
		all_different(e);

		// Min constraints on s[i]
		for (int i = 0; i < n; i++) {
			vec<IntVar*> x;
			for (int j = 0; j < n; j++) {
				if (g[i][j]) {
					x.push(e[j]);
				}
			}
			minimum(x, s[i]);
		}

		// open constraints
		for (int i = 0; i < n; i++) {
			for (int t = 0; t < n; t++) {
				int_rel_reif(s[i], IRT_LE, t, sb[i][t]);
				int_rel_reif(e[i], IRT_GE, t, eb[i][t]);
				vec<BoolView> x;
				x.push(sb[i][t]);
				x.push(eb[i][t]);
				array_bool_and(x, o[t][i]);
			}
		}

		// stack constraints
		for (int i = 0; i < n; i++) {
			bool_linear(o[i], IRT_LE, stacks);
		}

		// dominance breaking constraints
		vec<vec<BoolView> > r;
		createVars(r, n, n);

		// Find out which stacks can immediately close
		for (int t = 0; t < n; t++) {
			for (int i = 0; i < n; i++) {
				vec<BoolView> a;
				for (int j = 0; j < n; j++) {
					if (g[i][j]) {
						a.push(sb[j][t]);
					}
				}
				a.push(eb[i][t]);
				array_bool_and(a, r[i][t]);
			}
		}

		// If none of the lex better stacks can instantly close
		// and this one can, close it now
		for (int t = 0; t < n - 1; t++) {
			for (int i = 0; i < n; i++) {
				vec<BoolView> a;
				vec<BoolView> b;
				for (int j = 0; j < i; j++) {
					a.push(r[j][t]);
				}
				b.push(r[i][t]);
				b.push(eb[i][t + 1]);
				bool_clause(a, b);
			}
		}

		// branch on end times
		branch(e, VAR_MIN_MIN, VAL_MIN);

		// set optimization target
		optimize(stacks, OPT_MIN);
	}

	void generateInstance() {
		srand(so.rnd_seed);

		const int cust_per_prod = rand() % 4 + 2;
		const double density = (double)cust_per_prod / n;

		a = (bool**)malloc(n * sizeof(bool*));
		for (int i = 0; i < n; i++) {
			a[i] = (bool*)malloc(m * sizeof(bool));
		}

		while (true) {
			int b[m];

			for (int j = 0; j < m; j++) {
				b[j] = 0;
			}

			for (int j = 0; j < n; j++) {
				int sum = 0;
				for (int k = 0; k < m; k++) {
					if (rand() < RAND_MAX * density) {
						a[j][k] = true;
						b[k]++;
						sum++;
					} else {
						a[j][k] = false;
					}
				}
				if (sum == 0) {
					j--;
					continue;
				}
			}

			for (int j = 0; j < m; j++) {
				while (b[j] < 2) {
					const int r = rand() % n;
					if (static_cast<int>(a[r][j]) == 1) {
						continue;
					}
					a[r][j] = true;
					b[j]++;
				}
			}

			int cross[n][n];

			for (int j = 0; j < n; j++) {
				for (int k = 0; k < n; k++) {
					cross[j][k] = 0;
				}
			}

			for (int j = 0; j < m; j++) {
				for (int k = 0; k < n; k++) {
					if (a[k][j]) {
						for (int l = k; l < n; l++) {
							if (a[l][j]) {
								cross[l][k] = 1;
								cross[k][l] = 1;
							}
						}
					}
				}
			}

			int connected[n];
			int num_connected = 0;
			int qhead = 0;
			int seen[n];

			for (int j = 0; j < n; j++) {
				seen[j] = 0;
			}

			connected[num_connected++] = 0;
			seen[0] = 1;

			while (qhead < num_connected) {
				assert(qhead < n);
				assert(num_connected <= n);
				const int c = connected[qhead++];
				assert(c >= 0);
				assert(c < n);
				for (int j = 0; j < n; j++) {
					if ((cross[c][j] != 0) && (seen[j] == 0)) {
						connected[num_connected++] = j;
						seen[j] = 1;
					}
				}
			}

			if (num_connected == n) {
				break;
			}
		}
	}

	void print(std::ostream& os) override {
		for (int i = 0; i < n; i++) {
			const int m = e[i]->getVal();
			os << "e_" << i << " = " << m << ", ";
		}
		os << "\n";
		os << "Stacks = " << stacks->getVal() << "\n\n";
	}
};
/*
void readData(char *filename, char name[], int& n, int& m, bool*& a) {
	FILE *fp = fopen(filename, "r");
	assert(fp);

	fscanf(fp, "%[^\n]\n", name);
	fscanf(fp, "%d %d", &n, &m);

	if (n > 64) {
		printf("Too many customers! %d\n", n);
		abort();
	}

	a = new bool[n*m];
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < m; j++) {
			int c;
			fscanf(fp, "%d", &c);
			a[i*m+j] = c;
		}
	}

	fclose(fp);
}
*/
int main(int argc, char** argv) {
	parseOptions(argc, argv);

	assert(argc == 3);

	engine.solve(new MOSP(atoi(argv[1]), atoi(argv[2])));

	return 0;
}
