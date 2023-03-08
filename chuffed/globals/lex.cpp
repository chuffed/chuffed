#include <chuffed/core/propagator.h>

void newBinGE(IntView<> x, IntView<> y, BoolView r);
void newBinNE(IntView<> x, IntView<> y, BoolView r);

// x lex< y

// b[i] = r[i] || b[i+1]
// b[i] -> x[i] <= y[i]
// r[i] -> x[i] < y[i]

void lex(vec<IntVar*>& x, vec<IntVar*>& y, bool strict) {
	vec<BoolView> b;
	vec<BoolView> r;
	b.push(bv_true);
	for (int i = 1; i < x.size(); i++) {
		b.push(newBoolVar());
	}
	b.push(bv_false);
	for (int i = 0; i < x.size(); i++) {
		r.push(newBoolVar());
	}

	for (int i = 0; i < x.size() - 1 + static_cast<int>(strict); i++) {
		bool_rel(r[i], BRT_OR, b[i + 1], b[i]);
		newBinGE(IntView<>(y[i]), IntView<>(x[i], 1, 1), r[i]);
	}
	for (int i = 0; i < x.size(); i++) {
		newBinGE(IntView<>(y[i]), IntView<>(x[i]), b[i]);
	}
}
