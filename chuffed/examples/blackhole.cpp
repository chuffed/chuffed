#include "chuffed/branching/branching.h"
#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/globals/globals.h"
#include "chuffed/primitives/primitives.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/modelling.h"
#include "chuffed/vars/vars.h"

#include <cassert>
#include <iomanip>
#include <ostream>
#include <random>

#define SYM_BREAK 1
#define DC_TABLE 1

class BlackHole : public Problem {
public:
	static const int suits = 4;
	static const int ranks = 13;
	static const int cards = 52;
	static const int piles = 17;
	static const int layers = 3;

	int layout[piles][layers];
	int ctol[cards];
	int ctop[cards];

	vec<IntVar*> x;  // Pos of card
	vec<IntVar*> y;  // Card of pos

	BlackHole() {
		static_assert(suits * ranks == cards, "");
		static_assert(piles * layers == cards - 1, "");

		// Generate instance

		bool dealt[cards];
		for (bool& i : dealt) {
			i = false;
		}

		std::default_random_engine rnd_engine;
		std::uniform_int_distribution<int> rnd_card(1, cards);
		for (int i = 0; i < piles; i++) {
			for (int j = 0; j < layers; j++) {
				int r;
				while (dealt[r = rnd_card(rnd_engine)]) {
					;
				}
				dealt[r] = true;
				layout[i][j] = r;
				ctop[r] = i;
				ctol[r] = j;
			}
		}

		createVars(x, cards, 0, cards - 1);
		createVars(y, cards, 0, cards - 1);

		// Inverse constraint on x and y
		inverse(x, y);

		// Layer constraints on x
		for (auto& i : layout) {
			for (int j = 0; j < layers - 1; j++) {
				int_rel(x[i[j + 1]], IRT_LT, x[i[j]]);
			}
		}

		int_rel(x[0], IRT_EQ, 0);  // ace of spades in first pos
		int_rel(y[0], IRT_EQ, 0);  // first pos is Ace of spades

		if (DC_TABLE) {
			// Create two tuples for table constraint
			vec<vec<int> > neighbours(8 * cards);
			for (int i = 0; i < cards; i++) {
				for (int j = 0; j < 8; j++) {
					neighbours[i * 8 + j].push(i);
					neighbours[i * 8 + j].push((i + (j >> 1) * 13 + (j & 1) * 2 - 1 + 52) % 52);
				}
			}

			for (int i = 0; i < cards - 1; i++) {
				vec<IntVar*> w;
				w.push(y[i]);
				w.push(y[i + 1]);
				table(w, neighbours);
			}
		} else {
			for (int i = 0; i < cards - 1; i++) {
				for (int j = 0; j < 52; j++) {
					for (int k = 0; k < 52; k++) {
						if (j % 13 == (k + 1) % 13) {
							continue;
						}
						if ((j + 1) % 13 == k % 13) {
							continue;
						}
						bool_rel(BoolView(y[i]->getLit(j, LR_EQ)), BRT_R_IMPL,
										 BoolView(y[i + 1]->getLit(k, LR_NE)));
					}
				}
			}
		}

		if (SYM_BREAK) {
			int num_cond_sym_1 = 0;
			// Symmetry breaking constraints
			for (int i = 0; i < ranks; i++) {
				for (int s1 = 0; s1 < suits; s1++) {
					for (int s2 = s1 + 1; s2 < suits; s2++) {
						int o1 = s1 * ranks + i;
						int o2 = s2 * ranks + i;
						if (o1 == 0) {
							continue;
						}
						if (ctop[o1] == ctop[o2]) {
							continue;
						}
						if (ctol[o1] < ctol[o2]) {
							const int t = o1;
							o1 = o2;
							o2 = t;
						}
						num_cond_sym_1++;
						if (ctol[o2] == 0) {
							if (ctol[o1] == layers - 1) {
								int_rel(x[o1], IRT_LT, x[o2]);
							} else {
								vec<BoolView> b;
								createVars(b, 2);
								int_rel_reif(x[o2], IRT_LT, x[layout[ctop[o1]][ctol[o1] + 1]], b[0]);
								int_rel_reif(x[o1], IRT_LT, x[o2], b[1]);
								bool_clause(b);
							}
						} else {
							if (ctol[o1] == layers - 1) {
								vec<BoolView> b;
								createVars(b, 2);
								int_rel_reif(x[layout[ctop[o2]][ctol[o2] - 1]], IRT_LT, x[o1], b[0]);
								int_rel_reif(x[o1], IRT_LT, x[o2], b[1]);
								bool_clause(b);
							} else {
								vec<BoolView> b;
								createVars(b, 3);
								int_rel_reif(x[layout[ctop[o2]][ctol[o2] - 1]], IRT_LT, x[o1], b[0]);
								int_rel_reif(x[o2], IRT_LT, x[layout[ctop[o1]][ctol[o1] + 1]], b[1]);
								int_rel_reif(x[o1], IRT_LT, x[o2], b[2]);
								bool_clause(b);
							}
						}
					}
				}
			}
			//			printf("Num cond sym 1: %d\n", num_cond_sym_1);
		}

		vec<IntVar*> pref_order;
		for (int i = layers; i-- > 0;) {
			for (int j = 1; j < cards; j++) {
				if (ctol[j] == i) {
					pref_order.push(x[j]);
				}
			}
		}
		assert(pref_order.size() == cards - 1);

		branch(pref_order, VAR_MIN_MIN, VAL_MIN);
	}

	void print(std::ostream& os) override {
		const char s[5] = "SCHD";
		for (int i = 0; i < layers; i++) {
			for (auto& j : layout) {
				const int v = j[i];
				os << " " << std::setw(2) << std::setfill('0') << (v % ranks + 1) << s[v / ranks];
			}
			os << "\n";
		}
		os << "\n";

		for (int i = 0; i < cards; i++) {
			const int v = y[i]->getVal();
			os << std::setw(2) << std::setfill('0') << (v % ranks + 1) << s[v / ranks] << " ";
			if (i % ranks == ranks - 1) {
				os << "\n";
			}
		}
		os << "\n";
	}
};

int main(int argc, char** argv) {
	parseOptions(argc, argv);

	engine.solve(new BlackHole());

	return 0;
}
