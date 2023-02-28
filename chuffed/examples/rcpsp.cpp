#include <chuffed/branching/branching.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/vars/modelling.h>

#include <cassert>
#include <cstdio>

class RCPSP : public Problem {
public:
	// Constants

	int n_res;    // number of resources
	vec<int> rc;  // resource capacities

	int n_tasks;          // number of tasks
	vec<int> d;           // task durations
	int sum_d;            // total duration
	vec<vec<int> > rr;    // resource requirements
	vec<vec<int> > succ;  // task successors

	// Core variables

	vec<IntVar*> s;     // start times
	IntVar* objective;  // makespan

	// Intermediate variables
	vec<vec<IntVar*> > o;  // whether task i is open at time j

	RCPSP(char* filename) {
		readData(filename);

		int horizon = 250;

		// Create vars

		createVars(s, n_tasks, 0, horizon, true);
		createVars(o, n_tasks, horizon + 1, 0, 1, true);
		createVar(objective, 0, horizon);

		for (int i = 0; i < n_tasks; i++) {
			((IntVarEL*)s[i])->setVDecidable(false);
		}

		// Post some constraints

		for (int t = 0; t <= horizon; t++) {
			for (int i = 0; i < n_tasks; i++) {
				bool_rel(*s[i] <= t, BRT_AND, *s[i] > t - d[i], *o[i][t]);
			}
		}

		for (int r = 0; r < n_res; r++) {
			vec<int> a;
			bool in[n_tasks];
			for (int i = 0; i < n_tasks; i++) {
				in[i] = (d[i] > 0 && rr[r][i] > 0);
				if (in[i]) a.push(rr[r][i]);
			}
			for (int t = 0; t <= horizon; t++) {
				vec<IntVar*> x;
				for (int i = 0; i < n_tasks; i++) {
					if (in[i]) x.push(o[i][t]);
				}
				int_linear(a, x, IRT_LE, rc[r]);
			}
		}

		for (int i = 0; i < n_tasks; i++) {
			for (int j = 0; j < succ[i].size(); j++) {
				int k = succ[i][j];
				if (k == n_tasks) continue;
				int_rel(s[i], IRT_LE, s[k], -d[i]);
			}
		}

		for (int i = 0; i < n_tasks; i++) {
			int_rel(s[i], IRT_LE, objective, -d[i]);
		}

		// Post some branchings

		//		branch(s, VAR_ACTIVITY, VAL_MIN);

		branch(s, VAR_MIN_MIN, VAL_MIN);

		optimize(objective, OPT_MIN);

		//		assert(!so.vsids);
		//		so.vsids = true;
		//		engine.branching.add(&sat);
	}

	void readData(char* filename) {
		FILE* fp = fopen(filename, "r");
		assert(fp);

		rassert(fscanf(fp, "%d %d\n", &n_tasks, &n_res) == 2);

		n_tasks -= 2;

		rc.growTo(n_res);
		d.growTo(n_tasks);
		succ.growTo(n_tasks);

		rr.growTo(n_res);
		for (int i = 0; i < n_res; i++) rr[i].growTo(n_tasks);

		assert(n_res == 4);
		rassert(fscanf(fp, "%d %d %d %d\n", &rc[0], &rc[1], &rc[2], &rc[3]) == 4);

		for (int i = 0; i < n_tasks; i++) {
			//			printf("%d: ", i);
			char temp[1000], *s;
			rassert(fgets(temp, 1000, fp));
			if (i == 0) rassert(fgets(temp, 1000, fp));
			s = strtok(temp, " \t\n");
			d[i] = atoi(s);
			for (int j = 0; j < n_res; j++) {
				s = strtok(NULL, " \t\n");
				rr[j][i] = atoi(s);
			}
			s = strtok(NULL, " \t\n");
			int num_succ = atoi(s);
			for (int j = 0; j < num_succ; j++) {
				s = strtok(NULL, " \t\n");
				succ[i].push(atoi(s) - 2);
				//				printf("%d ", succ[i].last());
			}
			//			printf("\n");
		}

		fclose(fp);
	}

	// Function to print out solution

	void print(std::ostream& os) {
		for (int i = 0; i < n_tasks; i++) {
			os << s[i]->getVal() << ", ";
		}
		os << "\n";
		os << "makespan = " << objective->getVal() << "\n";
	}
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	assert(argc == 2);

	engine.solve(new RCPSP(argv[1]));

	return 0;
}
