#ifndef int_var_el_h
#define int_var_el_h

#include <chuffed/core/options.h>

class IntVarEL : public IntVar {
	int lit_min;
	int lit_max;
	int base_vlit;
	int base_blit;

	Lit getNELit(int v) const { return toLit(base_vlit+2*v); }
	Lit getEQLit(int v) const { return toLit(base_vlit+2*v+1); }
	Lit getGELit(int v) const { return toLit(base_blit+2*v); }
	Lit getLELit(int v) const { return toLit(base_blit+2*v+1); }

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

	int uiv_no;

	IntVarEL(const IntVar& other);

	void initVLits();
	void initBLits();
	void setVLearnable(bool b = true);
	void setBLearnable(bool b = true);
	void setVDecidable(bool t);
	void setBDecidable(bool t);

	VarType getType() { return INT_VAR_EL; }

	int getBaseVLit() { return base_vlit; }
	int getBaseBLit() { return base_blit; }
	Lit getEQLit2(int v) const { return toLit(base_vlit+2*v+1); }

	// t = 0: [x != v], t = 1: [x = v], t = 2: [x >= v], t = 3: [x <= v]
	Lit getLit(int64_t v, int t);

	Lit getMinLit() const { return ~getGELit(min); }
	Lit getMaxLit() const { return ~getLELit(max); }
	Lit getValLit() const { assert(isFixed()); return ~getEQLit(min); }
	Lit getFMinLit(int64_t v) { return ~getLit(so.finesse ? v : (int) min, 2); }
	Lit getFMaxLit(int64_t v) { return ~getLit(so.finesse ? v : (int) max, 3); }


	bool setMin(int64_t v, Reason r = NULL, bool channel = true);
	bool setMax(int64_t v, Reason r = NULL, bool channel = true);
	bool setVal(int64_t v, Reason r = NULL, bool channel = true);
	bool remVal(int64_t v, Reason r = NULL, bool channel = true);

	Lit createSetLit(vec<Lit>& head);

};

#endif
