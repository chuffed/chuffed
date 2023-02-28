#ifndef bool_view_h
#define bool_view_h

#include <chuffed/core/sat.h>
#include <chuffed/vars/vars.h>

class Propagator;

class BoolView : public Var {
	int v;
	bool s;

public:
	BoolView() {}
	BoolView(Lit p) : v(var(p)), s(sign(p)) {}

	friend BoolView operator~(BoolView& o) { return BoolView(o.getLit(0)); }

	friend bool operator<(const BoolView& a, const BoolView& b) {
		return (2 * a.v + a.s < 2 * b.v + b.s);
	}

	bool getSign() { return s; }
	void setSign(bool sign) { s = sign; }

	void setPreferredVal(PreferredVal p) {
		if (p == PV_MIN || p == PV_SPLIT_MIN) sat.polarity[v] = s ^ 1;
		if (p == PV_MAX || p == PV_SPLIT_MAX) sat.polarity[v] = s;
	}

	void attach(Propagator* p, int pos, int eflags);
	void detach(Propagator* p, int pos, int eflags);

	// Read data:

	VarType getType() { return BOOL_VAR; }

	bool isFixed() const { return sat.assigns[v]; }
	bool isTrue() const { return sat.assigns[v] == 1 - 2 * s; }
	bool isFalse() const { return sat.assigns[v] == -1 + 2 * s; }
	int getVal() const {
		assert(isFixed());
		return (sat.assigns[v] + 1) / 2 ^ s;
	}

	// Lit for explanations:

	Lit getValLit() const {
		assert(isFixed());
		return Lit(v, (sat.assigns[v] + 1) / 2);
	}
	Lit getLit(bool sign) const { return Lit(v, sign ^ s ^ 1); }

	// For Branching:

	bool finished() { return isFixed(); }
	double getScore(VarBranch vb) { NOT_SUPPORTED; }
	DecInfo* branch() { return new DecInfo(NULL, 2 * v + (sat.polarity[v])); }

	// Change domains:

	bool setValNotR(bool x) const { return sat.assigns[v] != (x ^ s) * 2 - 1; }

	bool setVal(bool x, Reason r = NULL) {
		assert(setValNotR(x));
		sat.cEnqueue(getLit(x), r);
		return (sat.confl == NULL);
	}

	bool setVal2(bool x, Reason r = NULL) {
		assert(setValNotR(x));
		sat.enqueue(getLit(x), r.pt);
		return (sat.confl == NULL);
	}

	operator Lit() const { return getLit(true); }
	Lit operator=(bool v) const { return getLit(v); }
	bool operator==(BoolView o) const { return v == o.v && s == o.s; }

	void setLearnable(bool learnable) { sat.flags[v].setLearnable(learnable); }

	void setDecidable(bool decidable) { sat.flags[v].setDecidable(decidable); }

	void setUIPable(bool UIPable) { sat.flags[v].setUIPable(UIPable); }
};

const BoolView bv_true(lit_True);
const BoolView bv_false(lit_False);

inline BoolView newBoolVar(int min = 0, int max = 1) {
	int varNumber = sat.newVar();
	BoolView v(Lit(varNumber, 0));
	if (min == 1) v.setVal(1);
	if (max == 0) v.setVal(0);
	return v;
}

#endif
