#include "chuffed/branching/branching.h"
#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/globals/globals.h"
#include "chuffed/mdd/CFG.h"
#include "chuffed/mdd/CYK.h"
#include "chuffed/mdd/MDD.h"
#include "chuffed/mdd/mdd_to_lgraph.h"
#include "chuffed/mdd/opts.h"
#include "chuffed/mdd/weighted_dfa.h"
#include "chuffed/mdd/wmdd_prop.h"
#include "chuffed/primitives/primitives.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/bool-view.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/vars.h"

#include <cassert>
#include <cmath>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <vector>

// Using the simplified model, with infinite under-costs, and unit over-costs.
// This maps to hard coverage constraints, and minimizing the # of worked hours.

#define DECOMP 1
#define USEMDD 2
#define USEGCC 4

#define DISTINCT_REST

// Code for additional option handling.
static char* hasPrefix(char* str, const char* prefix) {
	int len = strlen(prefix);
	if (strncmp(str, prefix, len) == 0) {
		return str + len;
	}
	return nullptr;
}

#ifdef DISTINCT_REST
enum GapT { G_R = 2, G_B = 1, G_L = 0, maxG = 3 };
#else
enum GapT { G_R = 0, G_B = 0, G_L = 0, maxG = 1 };
#endif

class ShiftSched : public Problem {
public:
	int const staff;
	int const shifts;
	int const acts;
	int const dom;
	const vec<vec<int> > demand;
	vec<vec<IntVar*> > xv;

	vec<IntVar*> staff_cost;
	IntVar* cost;

	ShiftSched(int _staff, int _shifts, int _acts, vec<vec<int> >& _demand, int mode)
			: staff(_staff), shifts(_shifts), acts(_acts), dom(acts + maxG), demand(_demand) {
		for (int ww = 0; ww < staff; ww++) {
			xv.push();
			for (int ss = 0; ss < shifts; ss++) {
				xv[ww].push(newIntVar(0, dom - 1));
				xv[ww][ss]->specialiseToEL();
			}
		}

		// Build the grammar
		int first = 0;
		while (first < shifts) {
			for (int ii = 0; ii < acts; ii++) {
				if (demand[first][ii] != 0) {
					goto found_first;
				}
			}
			first++;
		}
	found_first:

		int last = first;
		for (int ss = first; ss < shifts; ss++) {
			for (int ii = 0; ii < acts; ii++) {
				if (demand[ss][ii] != 0) {
					last = ss;
					break;
				}
			}
		}
		CFG::CFG g(buildSchedG(acts, first, last));

		// Construct variables for the circuit
		MDDTable mdd_tab(shifts);
		std::vector<std::vector<MDD> > seq;
		for (int ii = 0; ii < shifts; ii++) {
			seq.emplace_back();
			for (int kk = 0; kk < dom; kk++) {
				seq[ii].push_back(mdd_tab.vareq(ii, kk));
			}
		}
		MDD gcirc(parseCYK(mdd_tab.fff(), seq, g));

		// Convert the MDD into an edge-valued graph.
		vec<int> slot_cost;
		for (int si = 0; si < acts; si++) {
			slot_cost.push(1);
		}
		for (int si = acts; si < dom; si++) {
			slot_cost.push(0);
		}

		EVLayerGraph graph;
		EVLayerGraph::NodeID gcirc_evgraph(mdd_to_layergraph(graph, gcirc, slot_cost));

		// Enforce the schedule for each worker.
		MDDOpts mopts;
		mopts.expl_strat = MDDOpts::E_KEEP;
		mopts.expl_alg = MDDOpts::E_MINIMAL;
		for (int ww = 0; ww < staff; ww++) {
			staff_cost.push(newIntVar(0, shifts));
			evgraph_to_wmdd(xv[ww], staff_cost[ww], graph, gcirc_evgraph, mopts);
		}

		for (int ww = 1; ww < staff; ww++) {
			lex(xv[ww - 1], xv[ww], false);
		}

		// Enforce coverage constraints.
		for (int ss = 0; ss < shifts; ss++) {
			for (int act = 0; act < acts; act++) {
				vec<BoolView> bv;
				for (int ww = 0; ww < staff; ww++) {
					bv.push(xv[ww][ss]->getLit(act, LR_EQ));
				}

				bool_linear_decomp(bv, IRT_GE, demand[ss][act]);
				//          IntVar* d_const = newIntVar(demand[ss][act], demand[ss][act]);
				//          bool_linear(bv, IRT_GE, d_const);
			}
		}

		unsigned int cMin(0);
		for (int ss = 0; ss < shifts; ss++) {
			for (int aa = 0; aa < acts; aa++) {
				cMin += demand[ss][aa];
			}
		}

		cost = newIntVar(cMin, (last - first + 1) * staff);
		int_linear(staff_cost, IRT_LE, cost);

		// vec<IntVar*> rostered_int;
		// for(int ss = 0; ss < shifts; ss++)
		// {
		//   if(ss < first || ss > last)
		//     continue;

		//   for(int ww = 0; ww < staff; ww++)
		//   {
		//     IntVar* sv = newIntVar(0,1);
		//     bool2int(xv[ww][ss]->getLit(acts-1, LR_LE),sv);
		//     rostered_int.push(sv);
		//   }
		// }
		// int_linear(rostered_int, IRT_GE, cost);

		vec<IntVar*> vs;
		for (int ss = 0; ss < shifts; ss++) {
			for (int ww = 0; ww < staff; ww++) {
				vs.push(xv[ww][ss]);
			}
		}

		branch(vs, VAR_INORDER, VAL_MAX);
		optimize(cost, OPT_MIN);

		//    vs.push(cost);
		output_vars(vs);
	}

	static CFG::CFG buildSchedG(int n_acts, int first, int last) {
		unsigned int rest(n_acts + G_R);
		unsigned int brk(n_acts + G_B);
		unsigned int lunch(n_acts + G_L);
		CFG::CFG g(n_acts + maxG);

		CFG::Sym S(g.newVar());
		g.setStart(S);

		CFG::Sym R(g.newVar());
		CFG::Sym P(g.newVar());
		CFG::Sym W(g.newVar());
		CFG::Sym L(g.newVar());
		CFG::Sym F(g.newVar());

		CFG::Cond actLB(g.attach(new CFG::SpanLB(4)));
		CFG::Cond lunEQ(g.attach(new CFG::Span(4, 4)));
		CFG::Cond part(g.attach(new CFG::Span(13, 24)));
		CFG::Cond full(g.attach(new CFG::Span(30, 38)));
		CFG::Cond open(g.attach(new CFG::Start(first, last)));

		std::vector<CFG::Sym> activities;
		for (int ii = 0; ii < n_acts; ii++) {
			CFG::Sym act(g.newVar());
			activities.push_back(act);
			g.prod(open(act), CFG::E() << ii << act);
			g.prod(open(act), CFG::E() << ii);

			g.prod(W, CFG::E() << actLB(act));
		}

		g.prod(S, CFG::E() << R << part(P) << R);
		g.prod(S, CFG::E() << R << full(F) << R);

		g.prod(R, CFG::E() << rest << R);
		g.prod(R, CFG::E() << rest);

		g.prod(L, CFG::E() << lunch << L);
		g.prod(L, CFG::E() << lunch);

		g.prod(P, CFG::E() << W << brk << W);
		g.prod(F, CFG::E() << P << lunEQ(L) << P);

		return g;
	}

	void print(std::ostream& os) override {
		for (int act = 0; act < acts; act++) {
			os << "[";
			for (int ss = 0; ss < shifts; ss++) {
				os << demand[ss][act];
			}
			os << "]\n";
		}
		os << "Hours worked: " << (1.0 * cost->getVal() / 4) << "\n";
		for (int ww = 0; ww < xv.size(); ww++) {
			os << "[";
			for (int ii = 0; ii < shifts; ii++) {
				//        if(ii)
				//            printf(", ");
				int val(xv[ww][ii]->getVal());
				if (val < acts) {
					os << val;
				} else {
					switch (val - acts) {
#ifdef DISTINCT_REST
						case G_R:
							os << "R";
							break;
						case G_B:
							os << "B";
							break;
						case G_L:
							os << "L";
							break;
#else
						case G_R:
							os << "R";
							break;
#endif
						default:
							assert(0);
							break;
					}
				}
			}
			os << "]\n";
		}
	}
};

void parseInst(std::istream& in, int& acts, int& shifts, vec<vec<int> >& demand) {
	in >> acts;
	in >> shifts;

	for (int ss = 0; ss < shifts; ss++) {
		demand.push();
		for (int aa = 0; aa < acts; aa++) {
			double d;
			in >> d;
			demand.last().push((int)ceil(d));
		}
	}
}

int main(int argc, char** argv) {
	int mode = 0;

	int jj = 1;
	char* value;
	for (int ii = 1; ii < argc; ii++) {
		value = hasPrefix(argv[ii], "-decomp=");
		if (value != nullptr) {
			if (strcmp(value, "true") == 0) {
				mode |= DECOMP;
			}
			continue;
		}
		value = hasPrefix(argv[ii], "-mdd=");
		if (value != nullptr) {
			if (strcmp(value, "true") == 0) {
				mode |= USEMDD;
			}
			continue;
		}
		value = hasPrefix(argv[ii], "-gcc=");
		if (value != nullptr) {
			if (strcmp(value, "true") == 0) {
				mode |= USEGCC;
			}
			continue;
		}

		argv[jj++] = argv[ii];
	}
	argc = jj;

	parseOptions(argc, argv);

	// Arguments:
	// #staff

	//	assert(argc == 2 || argc == 3);
	assert(argc == 2);
	int staff = 1;
	int acts = 1;
	int shifts = 96;

	staff = atoi(argv[1]);

	vec<vec<int> > demand;

	parseInst(std::cin, acts, shifts, demand);

	engine.solve(new ShiftSched(staff, shifts, acts, demand, mode));
	return 0;
}
