#ifndef primitives_h
#define primitives_h


enum IntRelType {
	IRT_EQ,		// =	Equal to
	IRT_NE,		// <> 	Not equal to
	IRT_LE,		// <= 	Less than or equal to
	IRT_LT,		// < 	Less than
	IRT_GE,		// >=	Greater than or equal to
	IRT_GT		// >	Greater than
};

inline IntRelType operator!(IntRelType t) {
	switch (t) {
		case IRT_EQ: return IRT_NE;
		case IRT_NE: return IRT_EQ;
		case IRT_LE: return IRT_GT;
		case IRT_LT: return IRT_GE;
		case IRT_GE: return IRT_LT;
		case IRT_GT: return IRT_LE;
		default: NEVER;
	}
}

inline IntRelType operator-(IntRelType t) {
	switch (t) {
		case IRT_LE: return IRT_GE;
		case IRT_LT: return IRT_GT;
		case IRT_GE: return IRT_LE;
		case IRT_GT: return IRT_LT;
		default: return t;
	}
}

enum BoolRelType {
	BRT_AND     = 0x87,
	BRT_NOT     = 0x66,
	BRT_OR      = 0xe1,
	BRT_XOR     = 0x69,
	BRT_EQ      = 0x99,
	BRT_EQ_REIF = 0x96,
	BRT_NE      = 0x66,
	BRT_NE_REIF = 0x69,
	BRT_LE      = 0xdd,
	BRT_LE_REIF = 0xd2,
	BRT_LT      = 0x44,
	BRT_LT_REIF = 0x4b,
	BRT_GE      = 0xbb,
	BRT_GE_REIF = 0xb4,
	BRT_GT      = 0x22,
	BRT_GT_REIF = 0x2d,
	BRT_L_IMPL  = 0xb4,
	BRT_R_IMPL  = 0xd2
};


#include <chuffed/core/propagator.h>

// bool.c

// t(x,y,z)
void bool_rel(BoolView x, BoolRelType t, BoolView y, BoolView z = bv_true);
// \/ x_i \/ !y_i
void bool_clause(vec<BoolView>& x, vec<BoolView>& y);
// \/ x_i
void bool_clause(vec<BoolView>& x);
// \/ x_i \/ !y_i <-> z
void array_bool_or(vec<BoolView>& x, vec<BoolView>& y, BoolView z);
// \/ x_i <-> z
void array_bool_or(vec<BoolView>& x, BoolView z);
// /\ x_i /\ !y_i <-> z
void array_bool_and(vec<BoolView>& x, vec<BoolView>& y, BoolView z);
// /\ x_i <-> z
void array_bool_and(vec<BoolView>& x, BoolView z);

// binary.c

// x + y rel c
void bin_linear(IntVar* x, IntVar* y, IntRelType t, int c);
// x rel y + c
void int_rel(IntVar* x, IntRelType t, IntVar* y, int c = 0);
// x rel c
void int_rel(IntVar* x, IntRelType t, int c);
// x rel y + c <-> r
void int_rel_reif(IntVar* x, IntRelType t, IntVar* y, BoolView r, int c = 0);
// x rel y + c <- r
void int_rel_half_reif(IntVar* a, IntRelType t, IntVar* b, BoolView r, int c = 0);
// x rel c <-> r
void int_rel_reif(IntVar* a, IntRelType t, int c, BoolView r);
// x rel c <- r
void int_rel_half_reif(IntVar* a, IntRelType t, int c, BoolView r);

// linear.c

// sum a*x rel c <-> r
void int_linear(vec<int>& a, vec<IntVar*>& x, IntRelType t, int c, BoolView r = bv_true);
// sum x rel c <-> r
void int_linear(vec<IntVar*>& x, IntRelType t, int c, BoolView r = bv_true);
// sum a*x rel y <-> r
void int_linear(vec<int>& a, vec<IntVar*>& x, IntRelType t, IntVar* y, BoolView r = bv_true);
// sum x rel y <-> r
void int_linear(vec<IntVar*>& x, IntRelType t, IntVar* y, BoolView r = bv_true);
// sum a*x = c, domain consistent
void int_linear_dom(vec<int>& a, vec<IntVar*>& x, int c);

// arithmetic.c

// y = |x|
void int_abs(IntVar* x, IntVar* y);
// z = x ^ y
void int_pow(IntVar* x, IntVar* y, IntVar* z);
// z = x * y
void int_times(IntVar* x, IntVar* y, IntVar* z);
// z = floor(x / y)
void int_div(IntVar* x, IntVar* y, IntVar* z);
// z = x mod y
void int_mod(IntVar* x, IntVar* y, IntVar* z);
// z = min(x, y)
void int_min(IntVar* x, IntVar* y, IntVar* z);
// z = max(x, y)
void int_max(IntVar* x, IntVar* y, IntVar* z);
// z = x + y
void int_plus(IntVar* x, IntVar* y, IntVar* z);
// z = x - y
void int_minus(IntVar* x, IntVar* y, IntVar* z);
// y = -x
void int_negate(IntVar* x, IntVar* y);
// y = bool2int(x)
void bool2int(BoolView x, IntVar* y);

// element.c

// y = a[x-offset]
void array_bool_element(IntVar* x, vec<bool>& a, BoolView y, int offset = 0);
// y = a[x-offset]
void array_int_element(IntVar* x, vec<int>& a, IntVar* y, int offset = 0);
// y = a[x-offset]
void array_var_bool_element(IntVar* x, vec<BoolView>& a, BoolView y, int offset = 0);
// y = a[x-offset]
void array_var_int_element_bound(IntVar* x, vec<IntVar*>& a, IntVar* y, int offset = 0);
void array_var_int_element_dom(IntVar* x, vec<IntVar*>& a, IntVar* y, int offset = 0);
void array_var_int_element_bound_imp(BoolView b, IntVar* x, vec<IntVar*>& a, IntVar* y, int offset = 0);


// domain.c

// y = |ub(x) - lb(y) + 1|
void range_size(IntVar* x, IntVar* s);

#endif
