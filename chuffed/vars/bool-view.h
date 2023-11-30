#ifndef bool_view_h
#define bool_view_h

#include "chuffed/core/sat.h"
#include "chuffed/vars/vars.h"

class Propagator;

class BoolView : public Var {
	int v;
	bool s;

public:
	BoolView() = default;
	BoolView(Lit p) : v(var(p)), s(sign(p)) {}

	friend BoolView operator~(BoolView& o) { return {o.getLit(false)}; }

	friend bool operator<(const BoolView& a, const BoolView& b) {
		return (2 * a.v + static_cast<int>(a.s) < 2 * b.v + static_cast<int>(b.s));
	}

	bool getSign() const { return s; }
	void setSign(bool sign) { s = sign; }

	void setPreferredVal(PreferredVal p) override {
		if (p == PV_MIN || p == PV_SPLIT_MIN) {
			sat.polarity[v] = ((static_cast<int>(s) ^ 1) != 0);
		}
		if (p == PV_MAX || p == PV_SPLIT_MAX) {
			sat.polarity[v] = s;
		}
	}

	void attach(Propagator* p, int pos, int eflags) const;
	void detach(Propagator* p, int pos, int eflags);

	// Read data:

	VarType getType() override { return BOOL_VAR; }

	bool isFixed() const { return sat.assigns[v] != 0; }
	bool isTrue() const { return sat.assigns[v] == 1 - 2 * static_cast<int>(s); }
	bool isFalse() const { return sat.assigns[v] == -1 + 2 * static_cast<int>(s); }
	int getVal() const {
		assert(isFixed());
		return (sat.assigns[v] + 1) / 2 ^ static_cast<int>(s);
	}

	// Lit for explanations:

	Lit getValLit() const {
		assert(isFixed());
		return Lit(v, ((sat.assigns[v] + 1) / 2) != 0);
	}
	Lit getLit(bool sign) const { return Lit(v, (sign ^ s ^ 1) != 0); }

	// For Branching:

	bool finished() override { return isFixed(); }
	double getScore(VarBranch vb) override;
	DecInfo* branch() override {
		return new DecInfo(nullptr, 2 * v + static_cast<int>((sat.polarity[v])));
	}

	// Change domains:

	bool setValNotR(bool x) const { return sat.assigns[v] != (x ^ s) * 2 - 1; }

	bool setVal(bool x, Reason r = nullptr) const {
		assert(setValNotR(x));
		sat.cEnqueue(getLit(x), r);
		return (sat.confl == nullptr);
	}

	bool setVal2(bool x, Reason r = nullptr) const {
		assert(setValNotR(x));
		sat.enqueue(getLit(x), r.pt);
		return (sat.confl == nullptr);
	}

	operator Lit() const { return getLit(true); }
	Lit operator=(bool v) const { return getLit(v); }
	bool operator==(const BoolView& o) const { return v == o.v && s == o.s; }

	void setLearnable(bool learnable) const { sat.flags[v].setLearnable(learnable); }

	void setDecidable(bool decidable) const { sat.flags[v].setDecidable(decidable); }

	void setUIPable(bool UIPable) const { sat.flags[v].setUIPable(UIPable); }
};

const BoolView bv_true(lit_True);
const BoolView bv_false(lit_False);

inline BoolView newBoolVar(int min = 0, int max = 1) {
	const int varNumber = sat.newVar();
	BoolView v(Lit(varNumber, false));
	if (min == 1) {
		v.setVal(true);
	}
	if (max == 0) {
		v.setVal(false);
	}
	return v;
}

#endif
