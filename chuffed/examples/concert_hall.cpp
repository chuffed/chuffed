#include <cstdio>
#include <cassert>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/branching/branching.h>
#include <chuffed/vars/modelling.h>
#include <chuffed/ldsb/ldsb.h>

class ConcertHall : public Problem {
public:
	int n;                                          // number of offers
	int k;                                          // number of halls
	vec<int> start;                                 // start times
	vec<int> end;                                   // end times
	vec<int> price;                                 // prices

	vec<IntVar*> x;                                   // hall assignment
	vec<BoolView> t;                                  // take offer or not
	vec<IntVar*> bi;                                  // bool2int version of t
	vec<BoolView> qs;
	IntVar* total;                                // total profit


	ConcertHall(char *filename) {
		if (filename) readData(filename);
		else generateInstance();

		// create variables

		createVars(x, n, 0, k, true);
		createVars(t, n);
		createVars(bi, n, 0, 1);
		createVar(total, 0, 500000, true);

		// post constraints

		for (int i = 0; i < n; i++) {
			int_rel_reif(x[i], IRT_NE, k, t[i]);
			bool2int(t[i], bi[i]);
		}

		for (int i = 0; i < n; i++) {
			for (int j = i+1; j < n; j++) {
				if (start[i] > end[j] || start[j] > end[i]) continue;
/*
				vec<BoolView> y;
				BoolView q = newBoolVar();
				int_rel_reif(x[i], IRT_NE, x[j], q);
				y.push(~t[i]);
				y.push(~t[j]);
				y.push(q);
				bool_clause(y);
*/
				BoolView q = newBoolVar();
				qs.push(q);
				int_rel_reif(x[i], IRT_NE, x[j], q);
				bool_rel(~t[i], BRT_OR, q);
				bool_rel(~t[j], BRT_OR, q);

			}
		}

		bi.push(total);
		price.push(-1);

		int_linear(price, bi, IRT_GE, 0);

		branch(x, VAR_INORDER, VAL_MIN);
//		branch(x, VAR_SIZE_MIN, VAL_MIN);

		output_vars(x);

		optimize(total, OPT_MAX);

		if (so.ldsb) {
			val_sym_ldsb(x, 0, k-1);
		} else if (so.sym_static) {
			val_sym_break(x, 0, k-1);
		}


		// order syms

		vec<IntVar*> sym;

		for (int base = 0; base < n; ) {
			int i = base;
			while (i < n && start[i] == start[base] && end[i] == end[base] && price[i] == price[base]) {
//				printf("%d, ", i);
				sym.push(x[i]);
				i++;
			}
//			printf("\n");
			if (so.ldsb) var_sym_ldsb(sym);
			else if (so.sym_static) var_sym_break(sym);
			sym.clear();
			base = i;
		}

	}

	void restrict_learnable() {
		printf("Setting learnable white list\n");
		for (int i = 0; i < sat.nVars(); i++) sat.flags[i] = 0;
		for (int i = 0; i < x.size(); i++) {
			assert(x[i]->getType() == INT_VAR_EL);
			((IntVarEL*) x[i])->setVLearnable();
		}
		for (int i = 0; i < bi.size(); i++) {
			assert(bi[i]->getType() == INT_VAR_EL);
			((IntVarEL*) bi[i])->setVLearnable();
			((IntVarEL*) bi[i])->setBLearnable();
		}
		for (int i = 0; i < t.size(); i++) {
			sat.flags[var(t[i].getLit(0))].setLearnable(true);
			sat.flags[var(t[i].getLit(0))].setUIPable(true);
		}
		for (int i = 0; i < qs.size(); i++) {
			sat.flags[var(qs[i].getLit(0))].setLearnable(true);
			sat.flags[var(qs[i].getLit(0))].setUIPable(true);
		}
	}

	void readData(char *filename) {
		FILE *fp = fopen(filename, "r");
		
		rassert(fscanf(fp, "%d\n", &n) == 1);
		k = 8;

		start.growTo(n);
		end.growTo(n);
		price.growTo(n);
		
		for (int i = 0; i < n; i++) {
			rassert(fscanf(fp, "%d %d %d\n", &start[i], &end[i], &price[i]) == 3);
		}
	}

	void generateInstance() {
		srand(so.rnd_seed);
		n = 25;
		k = 5;
		int total = 100;
		for (int i = 0; i < n; i++) {
			int len = rand()%(total/4)+ total/8;
			int s = rand()%(total-len);
			int p = rand()%3000;
			start.push(s);
			end.push(s+len);
			price.push(p);
			printf("%d %d %d\n", s, s+len, p);
		}
	}

  void print(std::ostream& os) {
		for (int i = 0; i < n; i++) {
      os << x[i]->getVal() << ", ";
		}
		os << "\n";
		os << "total = " << total->getVal() << "\n";
	}

};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	engine.solve(new ConcertHall(argc == 2 ? argv[1] : NULL));

	return 0;
}



