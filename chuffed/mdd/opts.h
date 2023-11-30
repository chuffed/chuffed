#ifndef CHUFFED_MDDOPTS_H
#define CHUFFED_MDDOPTS_H

#include <string>

class MDDOpts {
public:
	enum ExplAlg { E_MINIMAL, E_GREEDY, E_NAIVE };
	enum ExplStrat { E_TEMP, E_KEEP };
	enum Decomp { D_PROP, D_DOMAIN, D_TSEITIN };

	MDDOpts() = default;

	MDDOpts(const MDDOpts& o) = default;

	void parse_arg(const std::string& arg) {
		if (arg == "explain_minimal") {
			expl_alg = E_MINIMAL;
		} else if (arg == "explain_greedy") {
			expl_alg = E_GREEDY;
		} else if (arg == "discard_explanations") {
			expl_strat = E_TEMP;
		} else if (arg == "store_explanations") {
			expl_strat = E_KEEP;
		}
	}
	ExplAlg expl_alg{E_GREEDY};
	ExplStrat expl_strat{E_KEEP};
	Decomp decomp{D_PROP};
};

#endif
