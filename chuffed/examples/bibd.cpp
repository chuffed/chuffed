#include <cstdio>
#include <cassert>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/branching/branching.h>
#include <chuffed/vars/modelling.h>
#include <chuffed/ldsb/ldsb.h>

class BIBD : public Problem {
public:
	int v;
	int b;
	int r;
	int k;
	int l;

	vec<vec<IntVar*> > x;                           // vertex labels
	vec<vec<vec<IntVar*> > > m;                     // raw difference of vertex labels

	BIBD(int _v, int _b, int _r, int _k, int _l) : v(_v), b(_b), r(_r), k(_k), l(_l) {

//		b = (l * v * (v-1)) / (k * (k-1));
//		r = (l * (v-1)) / (k-1);

		printf("v = %d, b = %d, r = %d, k = %d, l = %d\n", v, b, r, k, l);


		createVars(x, v, b, 0, 1);

		m.growTo(v);
		for (int i = 0; i < v; i++) {
			m[i].growTo(v);
			for (int j = 0; j < v; j++) {
				if (j <= i) continue;
				for (int k = 0; k < b; k++) {
					m[i][j].push(newIntVar(0,1));
				}
			}
		}

		vec<vec<IntVar*> > xt;
		transpose(x, xt);

		for (int i = 0; i < v; i++) {
			int_linear(x[i], IRT_EQ, r);
		}

		for (int i = 0; i < b; i++) {
			int_linear(xt[i], IRT_EQ, k);
		}

		for (int i = 0; i < v; i++) {
			for (int j = i+1; j < v; j++) {
				for (int k = 0; k < b; k++) {
					int_times(x[i][k], x[j][k], m[i][j][k]);
				}
				int_linear(m[i][j], IRT_EQ, l);
			}
		}

		vec<IntVar*> s;
		flatten(x, s);

//		branch(s, VAR_INORDER, VAL_MIN);
		branch(s, VAR_INORDER, VAL_MAX);

		output_vars(s);

		if (so.ldsb) {
			// row sym
			vec<IntVar*> sym1;
			flatten(x, sym1);
			var_seq_sym_ldsb(v, b, sym1);

			// column sym
			vec<IntVar*> sym2;
			flatten(xt, sym2);
			var_seq_sym_ldsb(b, v, sym2);

		} else if (so.sym_static) {
			printf("No sym breaks!\n");
		}
	}

	void restrict_learnable() {
		printf("Setting learnable white list\n");
		for (int i = 0; i < sat.nVars(); i++) sat.flags[i] = 0;
		for (int i = 0; i < v; i++) {
			for (int j = 0; j < b; j++) {
				assert(x[i][j]->getType() == INT_VAR_EL);
				((IntVarEL*) x[i][j])->setVLearnable();
				((IntVarEL*) x[i][j])->setVDecidable(true);
			}
		}
	}

	void print() {
		for (int i = 0; i < v; i++) {
			for (int j = 0; j < b; j++) {
				printf("%d", x[i][j]->getVal());
			}
			printf("\n");
		}
		printf("\n");
	}

};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	int v, b, r, k, l;

	assert(argc == 6);
	v = atoi(argv[1]);
	b = atoi(argv[2]);
	r = atoi(argv[3]);
	k = atoi(argv[4]);
	l = atoi(argv[5]);

	engine.solve(new BIBD(v, b, r, k, l));

	return 0;
}



