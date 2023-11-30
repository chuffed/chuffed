#ifndef CFG_H_
#define CFG_H_

#include <cassert>
#include <iostream>
#include <vector>

namespace CFG {

class ProdR {
public:
	virtual ~ProdR() = default;
	virtual bool check(int start, int end) = 0;
};

class Span : public ProdR {
public:
	Span(int _low, int _high) : low(_low), high(_high) {}

	bool check(int start, int end) override {
		const int span(end - start);
		return low <= span && span <= high;
	}

protected:
	int low;
	int high;
};

class Start : public ProdR {
public:
	Start(int _low, int _high) : low(_low), high(_high) {}

	bool check(int start, int /*end*/) override { return low <= start && start <= high; }

protected:
	int low;
	int high;
};

class SpanLB : public ProdR {
public:
	SpanLB(int _low) : low(_low) {}

	bool check(int start, int end) override {
		const int span(end - start);
		return low <= span;
	}

protected:
	int low;
};

class LB : public ProdR {
public:
	LB(int _lb) : lb(_lb) {}
	bool check(int start, int /*end*/) override { return lb <= start; }

protected:
	int lb;
};

class ProdInfo {
public:
	ProdInfo(ProdR* _cond, int _rule) : cond(_cond), rule(_rule) {}

	ProdR* cond;
	int rule;
};

struct Sym {
	int x;

	friend Sym mkTerm(int id);
	friend Sym mkVar(int id);

	bool operator==(Sym p) const { return x == p.x; }
	bool operator!=(Sym p) const { return x != p.x; }
	bool operator<(Sym p) const { return x < p.x; }
};

inline Sym mkTerm(int id) {
	Sym p;
	p.x = (id << 1);
	return p;
}
inline Sym mkVar(int id) {
	Sym p;
	p.x = (id << 1) + 1;
	return p;
}
inline int symID(Sym p) { return p.x >> 1; }
inline bool isVar(Sym p) { return (p.x & 1) != 0; }

class RSym {
public:
	RSym() : sym(mkTerm(0)), cond(nullptr) {}
	RSym(int i) : sym(mkTerm(i)), cond(nullptr) {}
	RSym(const Sym& _s) : sym(_s), cond(nullptr) {}
	RSym(int i, ProdR* _p) : sym(mkTerm(i)), cond(_p) {}
	RSym(const Sym& _s, ProdR* _p) : sym(_s), cond(_p) {}

	Sym sym;
	ProdR* cond;
};

class Cond {
public:
	Cond(ProdR* _p) : p(_p) {}

	RSym operator()(const Sym& s) { return {s, p}; }
	RSym operator()(int i) { return {i, p}; }

protected:
	ProdR* p;
};

inline std::ostream& operator<<(std::ostream& o, Sym s) {
	if (isVar(s)) {
		o << (char)('A' + symID(s));
	} else {
		o << symID(s);
	}
	return o;
}

class CFG;

class Rule {
public:
	Rule() = default;

	Rule& operator<<(RSym s) {
		syms.push_back(s);
		return *this;
	}

	Rule& operator<<(int n) {
		syms.emplace_back(mkTerm(n));
		return *this;
	}

	std::vector<RSym> syms;
};

inline Rule E() { return {}; }

class CFG {
public:
	CFG(int _alphsz) : alphsz(_alphsz), start(0) {}

	CFG(int _alphsz, int _nv) : alphsz(_alphsz) {
		for (int ii = 0; ii < _nv; ii++) {
		}
	}

	~CFG() {
		for (auto& cond : conds) {
			delete cond;
		}
	}

	static Sym term(int i) { return mkTerm(i); }
	Sym var(int i) {
		while (((int)prods.size()) <= i) {
			prods.emplace_back();
		}
		return mkVar(i);
	}
	Sym newVar() {
		const int id = prods.size();
		prods.emplace_back();
		return mkVar(id);
	}

	void setStart(Sym s) {
		assert(isVar(s));
		start = symID(s);
	}

	Sym startSym() const { return mkVar(start); }

	void prod(RSym p, const Rule& r) {
		const int r_id = rules.size();
		rules.push_back(r.syms);
		prods[symID(p.sym)].emplace_back(p.cond, r_id);
	}

	void rulePush(int id, Sym r) { rules[id].emplace_back(r); }

	void normalize() {
		for (unsigned int ii = 0; ii < rules.size(); ii++) {
			std::vector<RSym> nr(2);
			while (rules[ii].size() > 2) {
				const Sym next(newVar());
				nr[1] = rules[ii].back();
				rules[ii].pop_back();
				nr[0] = rules[ii].back();
				rules[ii].pop_back();

				rules[ii].emplace_back(next);
				rules.push_back(nr);
				prods[symID(next)].emplace_back(nullptr, rules.size() - 1);
			}
		}
	}

	void print() {
		for (unsigned int vv = 0; vv < prods.size(); vv++) {
			std::cout << (char)('A' + vv) << " -> ";

			for (unsigned int ri = 0; ri < prods[vv].size(); ri++) {
				if (ri != 0) {
					std::cout << "|";
				}
				printRule(prods[vv][ri].rule);
			}
			std::cout << '\n';
		}
	}

	void printRule(int r) {
		if (rules[r].empty()) {
			std::cout << "e";
			return;
		}

		for (auto& ii : rules[r]) {
			std::cout << ii.sym;
		}
	}

	Cond attach(ProdR* p) {
		conds.push_back(p);
		return {p};
	}

	int alphsz;
	int start;

	std::vector<std::vector<ProdInfo> > prods;  // Mapping var -> rule.
	std::vector<std::vector<RSym> > rules;      // The actual production rules.
	std::vector<ProdR*> conds;
};

}  // namespace CFG
#endif
