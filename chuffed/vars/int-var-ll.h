#ifndef int_var_ll_h
#define int_var_ll_h

class IntVarLL : public IntVar {
	static const bool ll_dec = true;

	struct LitNode {
		int var, val, prev, next;
	};

	vec<LitNode> ld;
	vec<int> freelist;

	Tint li, hi;

	Lit valLit;

	std::string varLabel;

	Lit getGELit(int v);
	Lit getLELit(int v);

	void channelMin(int v, Lit p);
	void channelMax(int v, Lit p);
	void updateFixed();

public:
	IntVarLL(const IntVar& other);

	VarType getType() { return INT_VAR_LL; }

	DecInfo* branch();

	int getLitNode();
	void freeLazyVar(int val);

	// NOTE: No support for INT_VAR_LL vars yet.
	// t = 0: [x != v], t = 1: [x = v], t = 2: [x >= v], t = 3: [x <= v]
	Lit getLit(int64_t v, int t);

	Lit getMinLit() const { return Lit(ld[li].var, 0); }
	Lit getMaxLit() const { return Lit(ld[hi].var, 1); }
	Lit getValLit() const {
		assert(isFixed());
		return ~valLit;
	}
	Lit getFMinLit(int64_t v) { return getMinLit(); }
	Lit getFMaxLit(int64_t v) { return getMaxLit(); }

	bool setMin(int64_t v, Reason r = NULL, bool channel = true);
	bool setMax(int64_t v, Reason r = NULL, bool channel = true);
	bool setVal(int64_t v, Reason r = NULL, bool channel = true);
	bool remVal(int64_t v, Reason r = NULL, bool channel = true);

	Lit createLit(int v);
};

#endif
