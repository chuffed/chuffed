#ifndef int_var_sl_h
#define int_var_sl_h

#include "chuffed/core/options.h"

// Integer variable with sparse domains.
class IntVarSL : public IntVar {
	vec<int> values;  // values that the var can take in ascending order
	IntVarEL* el;

	// Find the index value in `el` used for the value `v`, type determines return value when a hole
	// is encountered
	int find_index(int v, RoundMode type) const;

public:
	IntVarSL(const IntVar& other, vec<int>& values);

	void attach(Propagator* p, int pos, int eflags) override;

	VarType getType() override { return INT_VAR_SL; }

	// t = 0: [x != v], t = 1: [x = v], t = 2: [x >= v], t = 3: [x <= v]
	Lit getLit(int64_t v, LitRel t) override;

	Lit getMinLit() const override { return el->getMinLit(); }
	Lit getMaxLit() const override { return el->getMaxLit(); }
	Lit getValLit() const override { return el->getValLit(); }
	Lit getFMinLit(int64_t v) override {
		return so.finesse ? ~el->getLit(find_index(v, ROUND_UP), LR_GE) : el->getMinLit();
	}
	Lit getFMaxLit(int64_t v) override {
		return so.finesse ? ~el->getLit(find_index(v, ROUND_DOWN), LR_LE) : el->getMaxLit();
	}

	bool setMin(int64_t v, Reason r = nullptr, bool channel = true) override;
	bool setMax(int64_t v, Reason r = nullptr, bool channel = true) override;
	bool setVal(int64_t v, Reason r = nullptr, bool channel = true) override;
	bool remVal(int64_t v, Reason r = nullptr, bool channel = true) override;

	void channel(int val, LitRel val_type, int sign) override;
	void debug();
};

#endif
