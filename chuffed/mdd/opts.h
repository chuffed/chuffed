#ifndef CHUFFED_MDDOPTS_H
#define CHUFFED_MDDOPTS_H

#include <string>

class MDDOpts {
public:
	enum ExplAlg { E_MINIMAL, E_GREEDY, E_NAIVE };
	enum ExplStrat { E_TEMP, E_KEEP };
	enum Decomp { D_PROP, D_DOMAIN, D_TSEITIN };

	MDDOpts() : expl_alg(E_GREEDY), expl_strat(E_KEEP), decomp(D_PROP) {}

	MDDOpts(const MDDOpts& o) : expl_alg(o.expl_alg), expl_strat(o.expl_strat), decomp(o.decomp) {}

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
	ExplAlg expl_alg;
	ExplStrat expl_strat;
	Decomp decomp;
};

#endif
