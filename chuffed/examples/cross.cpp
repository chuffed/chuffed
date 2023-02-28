#include <chuffed/branching/branching.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/globals/mddglobals.h>

#include <cassert>
#include <cstdio>
#include <iostream>

static void skipComments(std::istream& i) {
	assert(i.peek() == '#');

	while (i.peek() != '\n' && i.peek() != EOF) i.ignore();
}

class Cross : public Problem {
public:
	int nvars;
	int dom;
	int nrels;
	int ncons;

	vec<IntVar*> x;

	Cross() {
		// Generate instance

		while (std::cin.peek() == '#') skipComments(std::cin);

		std::cin >> nvars;
		std::cin >> dom;
		std::cin >> nrels;
		std::cin >> ncons;

		for (int i = 0; i < nvars; i++) {
			x.push(newIntVar(0, dom - 1));
			x.last()->specialiseToEL();
		}

		vec<vec<vec<int> > > tables;

		for (int i = 0; i < nrels; i++) {
			tables.push();
			vec<vec<int> >& tuples(tables.last());

			int arity;
			std::cin >> arity;

			while (std::cin.peek() != ';') {
				tuples.push();
				while (std::cin.peek() != ';' && std::cin.peek() != '|') {
					tuples.last().push();
					std::cin >> tuples.last().last();
				}
				if (std::cin.peek() == '|') std::cin.ignore();
			}
			std::cin.ignore();
		}

		for (int i = 0; i < ncons; i++) {
			vec<IntVar*> w;

			int rel;
			std::cin >> rel;

			while (std::cin.peek() != ';') {
				int v;
				std::cin >> v;

				w.push(x[v]);
			}
			std::cin.ignore();

			if (!so.mdd) {
				table(w, tables[rel]);
			} else {
				mdd_table(w, tables[rel], MDDOpts());
			}
		}

		vec<IntVar*> pref_order;
		for (int i = 0; i < x.size(); i++) {
			pref_order.push(x[i]);
		}

		branch(pref_order, VAR_INORDER, VAL_MIN);
		//        branch(pref_order, VAR_MIN_MIN, VAL_SPLIT_MIN);
	}

	void print(std::ostream& os) {
		for (int i = 0; i < nvars; i++) {
			int v = x[i]->getVal();
			os << i << ": " << v << "\n";
		}
	}
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	engine.solve(new Cross());

	return 0;
}
