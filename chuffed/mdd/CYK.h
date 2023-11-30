#ifndef CYK_H_
#define CYK_H_
#include "chuffed/mdd/CFG.h"

#include <map>

// Conversion of a CFG to some formula type F.
typedef struct {
	CFG::Sym s;
	int start;
	int end;
} cyk_sig;

cyk_sig mk_sig(CFG::Sym s, int start, int end) {
	cyk_sig sig = {s, start, end};
	return sig;
}

struct cyk_clt {
	bool operator()(const cyk_sig a, const cyk_sig b) const {
		if (a.s != b.s) {
			return a.s < b.s;
		}

		if (a.start != b.start) {
			return a.start < b.start;
		}

		return a.end < b.end;
	}
};

// Currently assumes grammar has no nullable nonterminals.
template <class F>
class CYKParser {
	typedef std::map<cyk_sig, int, cyk_clt> CacheT;
	std::vector<F> fs;

public:
	CYKParser(F _fff, CFG::CFG& _g, std::vector<std::vector<F> >& _vars)
			: g(_g), fff(_fff), vars(_vars) {}

	F parse() {
		g.normalize();
		return part(g.startSym(), 0, vars.size());
	}

	F part(CFG::Sym s, int start, int end) {
		cyk_sig sig = mk_sig(s, start, end);

		auto cval = cache.find(sig);

		if (cval != cache.end()) {
			return fs[(*cval).second];
		}

		if (!isVar(s)) {
			if (end == start + 1 && ((unsigned int)symID(s)) < vars[start].size()) {
				return vars[start][symID(s)];
			}
			return fff;
		}

		F ret(fff);
		int vid(symID(s));
		for (auto pinf : g.prods[vid]) {
			if ((pinf.cond == nullptr) || pinf.cond->check(start, end)) {
				ret = ret | prod(pinf.rule, start, end);
			}
		}

		int rindex = fs.size();
		fs.push_back(ret);
		cache[sig] = rindex;
		return ret;
	}

	F prod(int r_id, int start, int end) {
		std::vector<F> partial;

		if (g.rules[r_id].size() == 1) {
			if ((g.rules[r_id][0].cond == nullptr) || g.rules[r_id][0].cond->check(start, end)) {
				return part(g.rules[r_id][0].sym, start, end);
			}
			return fff;
		}

		// Assumes binary.
		assert(g.rules[r_id].size() == 2);

		F ret(fff);

		for (int si = start + 1; si < end; si++) {
			CFG::RSym& r0(g.rules[r_id][0]);
			CFG::RSym& r1(g.rules[r_id][1]);
			if (((r0.cond == nullptr) || r0.cond->check(start, si)) &&
					((r1.cond == nullptr) || r1.cond->check(si, end))) {
				ret = ret | (part(r0.sym, start, si) & part(r1.sym, si, end));
			}
		}

		return ret;
	}

protected:
	CFG::CFG& g;

	F fff;  // False value.
	std::vector<std::vector<F> >& vars;

	// Cache entries
	CacheT cache;
};

template <class F>
F parseCYK(F fff, std::vector<std::vector<F> >& vars, CFG::CFG& g) {
	CYKParser<F> p(fff, g, vars);
	return p.parse();
}

#endif
