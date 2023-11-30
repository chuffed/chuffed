#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/core/propagator.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/mip/mip.h"
#include "chuffed/primitives/primitives.h"
#include "chuffed/support/misc.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/bool-view.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/int-view.h"
#include "chuffed/vars/vars.h"

#include <cassert>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <utility>

// sum x_i >= c <- r
// Only use scale and minus views. Absorb offsets into c.

template <int S, int R = 0>
class LinearGE : public Propagator {
	vec<int> pos;
	vec<IntView<2 * S> > x;
	vec<IntView<2 * S + 1> > y;
	int const c;
	BoolView r;

	// persistent data
	int fix;
	int fix_x;
	int fix_y;
	int64_t fix_sum;
	vec<Lit> ps;

public:
	LinearGE(vec<int>& a, vec<IntVar*>& _x, int _c, BoolView _r = bv_true)
			: pos(_x.size()),
				c(_c),
				r(std::move(_r)),
				fix(0),
				fix_x(0),
				fix_y(0),
				fix_sum(-c),
				ps(R + _x.size()) {
		priority = 2;

		for (int i = 0; i < _x.size(); i++) {
			assert(a[i]);
			if (a[i] > 0) {
				pos[i] = x.size();
				x.push(IntView<2 * S>(_x[i], a[i]));
				_x[i]->attach(this, i, EVENT_U);
			} else {
				pos[i] = -y.size() - 1;
				y.push(IntView<2 * S + 1>(_x[i], -a[i]));
				_x[i]->attach(this, i, EVENT_L);
			}
		}
		if (R != 0) {
			r.attach(this, _x.size(), EVENT_L);
		}
	}

	void wakeup(int i, int c) override {
		if ((R == 0) || !r.isFalse()) {
			pushInQueue();
		}
	}

	bool propagate() override {
		if ((R != 0) && r.isFalse()) {
			return true;
		}

		int64_t max_sum = fix_sum;

		for (int i = fix_x; i < x.size(); i++) {
			max_sum += x[i].getMax();
		}
		for (int i = fix_y; i < y.size(); i++) {
			max_sum += y[i].getMax();
		}

		//		if (R && max_sum < 0) setDom2(r, setVal, 0, x.size()+y.size());

		if ((R != 0) && max_sum < 0) {
			int64_t v = 0;
			if (r.setValNotR(v != 0)) {
				Reason expl;
				if (so.lazy) {
					for (int j = 0; j < x.size(); j++) {
						ps[j + 1] = x[j].getMaxLit();
					}
					for (int j = 0; j < y.size(); j++) {
						ps[j + 1 + x.size()] = y[j].getMaxLit();
					}
					expl = Reason_new(ps);
				}
				if (!r.setVal(v != 0, expl)) {
					return false;
				}
			}
		}

		if ((R != 0) && !r.isTrue()) {
			return true;
		}

		//		for (int i = fix_x; i < x.size(); i++) {
		//			setDom2(x[i], setMin, x[i].getMax()-max_sum, i);
		//		}

		//		for (int i = fix_y; i < y.size(); i++) {
		//			setDom2(y[i], setMin, y[i].getMax()-max_sum, x.size()+i);
		//		}

		for (int i = fix_x; i < x.size(); i++) {
			int64_t v = x[i].getMax() - max_sum;
			if (x[i].setMinNotR(v)) {
				Reason expl;
				if (so.lazy) {
					if ((R != 0) && r.isFixed()) {
						ps[0] = r.getValLit();
					}
					for (int j = 0; j < x.size(); j++) {
						ps[j + R] = x[j].getMaxLit();
					}
					for (int j = 0; j < y.size(); j++) {
						ps[j + R + x.size()] = y[j].getMaxLit();
					}
					ps[R + i] = ps[0];
					expl = Reason_new(ps);
				}
				if (!x[i].setMin(v, expl)) {
					return false;
				}
			}
		}

		for (int i = fix_y; i < y.size(); i++) {
			int64_t v = y[i].getMax() - max_sum;
			if (y[i].setMinNotR(v)) {
				Reason expl;
				if (so.lazy) {
					if ((R != 0) && r.isFixed()) {
						ps[0] = r.getValLit();
					}
					for (int j = 0; j < x.size(); j++) {
						ps[j + R] = x[j].getMaxLit();
					}
					for (int j = 0; j < y.size(); j++) {
						ps[j + R + x.size()] = y[j].getMaxLit();
					}
					ps[R + x.size() + i] = ps[0];
					expl = Reason_new(ps);
				}
				if (!y[i].setMin(v, expl)) {
					return false;
				}
			}
		}

		return true;
	}

	Clause* explain(Lit p, int inf_id) override {
		if (inf_id == x.size() + y.size()) {
			inf_id = -1;
		}
		if ((R != 0) && r.isFixed()) {
			ps[0] = r.getValLit();
		}
		for (int i = 0; i < x.size(); i++) {
			ps[i + R] = x[i].getMaxLit();
		}
		for (int i = 0; i < y.size(); i++) {
			ps[i + R + x.size()] = y[i].getMaxLit();
		}
		ps[R + inf_id] = ps[0];
		return Reason_new(ps);
	}
};

//-----

// sum x_i != c <- r

template <int U, int V, int R = 0>
class LinearNE : public Propagator {
	int sp;
	int const sz;
	IntView<U>* x;
	IntView<V>* y;
	int const c;
	BoolView r;

	// persistent state

	Tint num_unfixed;
	Tint64_t sum_fixed;

public:
	LinearNE(vec<int>& a, vec<IntVar*>& _x, int _c, BoolView _r = bv_true)
			: sz(_x.size()), c(_c), r(std::move(_r)), num_unfixed(sz), sum_fixed(-c) {
		vec<IntView<0> > w;
		for (int i = 0; i < a.size(); i++) {
			if (a[i] >= 0) {
				w.push(IntView<0>(_x[i], a[i]));
			}
		}
		sp = w.size();
		for (int i = 0; i < a.size(); i++) {
			if (a[i] < 0) {
				w.push(IntView<0>(_x[i], -a[i]));
			}
		}
		x = (IntView<U>*)(IntView<0>*)w;
		y = (IntView<V>*)(IntView<0>*)w;
		w.release();

		for (int i = 0; i < sz; i++) {
			x[i].attach(this, i, EVENT_F);
		}
		if (R != 0) {
			r.attach(this, sz, EVENT_L);
		}
		//		printf("LinearNE: %d %d %d %d %d\n", sp, sz, U, V, R);
	}

	void wakeup(int i, int c) override {
		if (i < sz) {
			num_unfixed = num_unfixed - 1;
			if (i < sp) {
				sum_fixed = sum_fixed + x[i].getVal();
			} else {
				sum_fixed = sum_fixed + y[i].getVal();
			}
		}
		if (num_unfixed > 1) {
			return;
		}
		if ((R == 0) || r.isTrue() || (!r.isFixed() && num_unfixed == 0)) {
			pushInQueue();
		}
	}

	bool propagate() override {
		if ((R != 0) && r.isFalse()) {
			return true;
		}

		assert(num_unfixed <= 1);

		if (num_unfixed == 0) {
			if (sum_fixed == 0) {
				Clause* m_r = nullptr;
				if (so.lazy) {
					m_r = Reason_new(sz + 1);
					for (int i = 0; i < sz; i++) {
						(*m_r)[i + 1] = x[i].getValLit();
					}
				}
				return r.setVal(false, m_r);
			}
			return true;
		}

		if ((R != 0) && !r.isTrue()) {
			return true;
		}

		assert(num_unfixed == 1);

		int k = 0;
		while (x[k].isFixed()) {
			k++;
		}
		assert(k < sz);
		for (int i = k + 1; i < sz; i++) {
			assert(x[i].isFixed());
		}

		if ((k < sp && x[k].remValNotR(-sum_fixed)) || (k >= sp && y[k].remValNotR(-sum_fixed))) {
			Clause* m_r = nullptr;
			if (so.lazy) {
				m_r = Reason_new(sz + R);
				for (int i = 0; i < k; i++) {
					(*m_r)[i + 1] = x[i].getValLit();
				}
				for (int i = k + 1; i < sz; i++) {
					(*m_r)[i] = x[i].getValLit();
				}
				if (R != 0) {
					(*m_r)[sz] = r.getValLit();
				}
			}
			if (k < sp) {
				if (!x[k].remVal(-sum_fixed, m_r)) {
					return false;
				}
			} else {
				if (!y[k].remVal(-sum_fixed, m_r)) {
					return false;
				}
			}
		}

		return true;
	}
};

//-----

// sum a*x rel c

template <int S>
void int_linear(vec<int>& a, vec<IntVar*>& x, IntRelType t, int c) {
	vec<int> b;
	for (int i = 0; i < a.size(); i++) {
		b.push(-a[i]);
	}
	switch (t) {
		case IRT_EQ:
			int_linear<S>(a, x, IRT_GE, c);
			int_linear<S>(b, x, IRT_GE, -c);
			return;
		case IRT_NE:
			new LinearNE<2 * S, 2 * S + 1>(a, x, c);
			return;
		case IRT_LE:
			int_linear<S>(b, x, IRT_GE, -c);
			return;
		case IRT_LT:
			int_linear<S>(b, x, IRT_GE, -c + 1);
			return;
		case IRT_GE:
			new LinearGE<S>(a, x, c);
			break;
		case IRT_GT:
			int_linear<S>(a, x, IRT_GE, c + 1);
			return;
		default:
			NEVER;
	}

	assert(t == IRT_GE);
	mip->addConstraint(a, x, c, 1e100);
}

//-----

// sum a*x rel c <-> r

template <int S>
void int_linear_reif(vec<int>& a, vec<IntVar*>& x, IntRelType t, int c, BoolView r) {
	vec<int> b;
	for (int i = 0; i < a.size(); i++) {
		b.push(-a[i]);
	}
	switch (t) {
		case IRT_EQ:
			new LinearGE<S, 1>(a, x, c, r);
			new LinearGE<S, 1>(b, x, -c, r);
			new LinearNE<2 * S, 2 * S + 1, 1>(a, x, c, ~r);
			break;
		case IRT_NE:
			int_linear_reif<S>(a, x, IRT_EQ, c, ~r);
			break;
		case IRT_LE:
			int_linear_reif<S>(b, x, IRT_GE, -c, r);
			break;
		case IRT_LT:
			int_linear_reif<S>(b, x, IRT_GE, -c + 1, r);
			break;
		case IRT_GE:
			new LinearGE<S, 1>(a, x, c, r);
			new LinearGE<S, 1>(b, x, -c + 1, ~r);
			break;
		case IRT_GT:
			int_linear_reif<S>(a, x, IRT_GE, c + 1, r);
			break;
		default:
			NEVER;
	}
}

// sum a*x rel c <-> r

void int_linear(vec<int>& a, vec<IntVar*>& x, IntRelType t, int c, BoolView r) {
	assert(a.size() == x.size());

	bool scale = false;
	double limit = abs(c);
	for (int i = 0; i < x.size(); i++) {
		assert(a[i]);
		if (a[i] != 1 && a[i] != -1) {
			scale = true;
		}
		limit += abs(a[i]) * IntVar::max_limit + INT_MAX;
	}
	if (limit >= INT64_MAX) {
		CHUFFED_ERROR("Linear constraint may overflow, not yet supported\n");
	}

	if (x.size() == 1 && !scale) {
		if (r.isTrue()) {
			if (a[0] == 1) {
				int_rel(x[0], t, c);
			}
			if (a[0] == -1) {
				int_rel(x[0], -t, -c);
			}
		} else {
			if (a[0] == 1) {
				int_rel_reif(x[0], t, c, r);
			}
			if (a[0] == -1) {
				int_rel_reif(x[0], -t, -c, r);
			}
		}
		return;
	}

	if (x.size() == 2 && !scale) {
		if (r.isTrue()) {
			if (a[0] == -1 && a[1] == -1 && t != IRT_NE) {
				bin_linear(x[0], x[1], -t, -c);
				return;
			}
			if (a[0] == 1 && a[1] == -1) {
				int_rel(x[0], t, x[1], c);
				return;
			}
			if (a[0] == -1 && a[1] == 1) {
				int_rel(x[1], t, x[0], c);
				return;
			}
			if (a[0] == 1 && a[1] == 1 && t != IRT_NE) {
				bin_linear(x[0], x[1], t, c);
				return;
			}
		} else if (a[0] + a[1] == 0) {
			if (a[0] == 1 && a[1] == -1) {
				int_rel_reif(x[0], t, x[1], r, c);
			}
			if (a[0] == -1 && a[1] == 1) {
				int_rel_reif(x[1], t, x[0], r, c);
			}
			return;
		}
	}

	if (r.isTrue()) {
		if (scale) {
			int_linear<1>(a, x, t, c);
		} else {
			int_linear<0>(a, x, t, c);
		}
	} else {
		if (scale) {
			int_linear_reif<1>(a, x, t, c, r);
		} else {
			int_linear_reif<0>(a, x, t, c, r);
		}
	}
}

void int_linear(vec<IntVar*>& x, IntRelType t, int c, BoolView r) {
	vec<int> a(x.size(), 1);
	int_linear(a, x, t, c, r);
}

void int_linear(vec<int>& _a, vec<IntVar*>& _x, IntRelType t, IntVar* y, BoolView r) {
	vec<int> a;
	for (int i = 0; i < _a.size(); i++) {
		a.push(_a[i]);
	}
	a.push(-1);
	vec<IntVar*> x;
	for (int i = 0; i < _x.size(); i++) {
		x.push(_x[i]);
	}
	x.push(y);
	int_linear(a, x, t, 0, r);
}

void int_linear(vec<IntVar*>& x, IntRelType t, IntVar* y, BoolView r) {
	vec<int> a(x.size(), 1);
	int_linear(a, x, t, y, r);
}

void table_GAC(vec<IntVar*>& x, vec<vec<int> >& t);

// sum a*x = c, propagated to domain consistency using table propagator

void int_linear_dom(vec<int>& a, vec<IntVar*>& x, int c) {
	assert(a.size() == 3 && x.size() == 3);

	for (int i = 0; i < x.size(); i++) {
		x[i]->specialiseToEL();
	}

	vec<vec<int> > t;
	for (int i = x[0]->getMin(); i <= x[0]->getMax(); i++) {
		if (!x[0]->indomain(i)) {
			continue;
		}
		for (int j = x[1]->getMin(); j <= x[1]->getMax(); j++) {
			if (!x[1]->indomain(j)) {
				continue;
			}
			int k = c - a[0] * i + a[1] * j;
			if (k % a[2] != 0) {
				continue;
			}
			k /= a[2];
			if (!x[2]->indomain(k)) {
				continue;
			}
			t.push();
			t.last().push(i);
			t.last().push(j);
			t.last().push(k);
		}
	}

	table_GAC(x, t);
}
