#ifndef int_var_el_h
#define int_var_el_h

#include "chuffed/core/options.h"
#include "chuffed/core/sat-types.h"

class IntVarEL : public IntVar {
	int lit_min;
	int lit_max;
	int base_vlit;
	int base_blit;

	Lit getNELit(int v) const { return toLit(base_vlit + 2 * v); }
	Lit getEQLit(int v) const { return toLit(base_vlit + 2 * v + 1); }
	Lit getGELit(int v) const { return toLit(base_blit + 2 * v); }
	Lit getLELit(int v) const { return toLit(base_blit + 2 * v + 1); }

	void channelMin(int v);
	void channelMax(int v);
	void channelFix(int v);

#if INT_DOMAIN_LIST
	void updateMin(int v, int i);
	void updateMax(int v, int i);
#else
	void updateMin();
	void updateMax();
#endif
	void updateFixed();

public:
	int uiv_no{-1};

	IntVarEL(const IntVar& other);

	void initVLits();
	void initBLits();
	void setVLearnable(bool b = true) const;
	void setBLearnable(bool b = true) const;
	void setVDecidable(bool b) const;
	void setBDecidable(bool b) const;

	VarType getType() override { return INT_VAR_EL; }

	int getBaseVLit() const { return base_vlit; }
	int getBaseBLit() const { return base_blit; }
	Lit getEQLit2(int v) const { return toLit(base_vlit + 2 * v + 1); }

	// t = 0: [x != v], t = 1: [x = v], t = 2: [x >= v], t = 3: [x <= v]
	Lit getLit(int64_t v, LitRel t) override;

	Lit getMinLit() const override { return ~getGELit(min); }
	Lit getMaxLit() const override { return ~getLELit(max); }
	Lit getValLit() const override {
		assert(isFixed());
		return ~getEQLit(min);
	}
	Lit getFMinLit(int64_t v) override { return ~getLit(so.finesse ? v : (int)this->min, LR_GE); }
	Lit getFMaxLit(int64_t v) override { return ~getLit(so.finesse ? v : (int)this->max, LR_LE); }

	bool setMin(int64_t v, Reason r = nullptr, bool channel = true) override;
	bool setMax(int64_t v, Reason r = nullptr, bool channel = true) override;
	bool setVal(int64_t v, Reason r = nullptr, bool channel = true) override;
	bool remVal(int64_t v, Reason r = nullptr, bool channel = true) override;

	Lit createSetLit(vec<Lit>& head);
};

#endif
