#include <chuffed/core/propagator.h>

// sum x_i <= y

template <int U = 0>
class BoolLinearLE : public Propagator {
public:
	vec<BoolView> x;
	IntView<U> y;

	// Persistent state
	Tint ones;

	vec<Lit> ps;

	BoolLinearLE(vec<BoolView>& _x, IntView<U> _y) : x(_x), y(_y), ones(0) {
		for (int i = 0; i < x.size(); i++) {
			x[i].attach(this, i, EVENT_L);
		}
		y.attach(this, x.size(), EVENT_U);
	}

	void wakeup(int i, int c) override {
		if (i < x.size()) {
			ones++;
		}
		pushInQueue();
	}

	bool propagate() override {
		int y_max = y.getMax();

		if (ones > y_max) {
			ones = y_max + 1;
		}

		setDom2(y, setMin, ones, 1);

		if (ones == y_max) {
			for (int i = 0; i < x.size(); i++) {
				if (!x[i].isFixed()) {
					x[i].setVal2(false, Reason(prop_id, 0));
				}
			}
		}

		return true;
	}

	Clause* explain(Lit p, int inf_id) override {
		ps.clear();
		ps.growTo(ones + 1);
		for (int i = 0, j = 1; j <= ones; i++) {
			if (x[i].isTrue()) {
				ps[j++] = ~x[i];
			}
		}
		if (inf_id == 0) {
			ps.push(y.getMaxLit());
		}
		return Reason_new(ps);
	}
};

//-----

// sum x_i (=, <=, <, >=, >) y

void bool_linear(vec<BoolView>& x, IntRelType t, IntVar* y) {
	vec<BoolView> x2;
	for (int i = 0; i < x.size(); i++) {
		x2.push(~x[i]);
	}
	switch (t) {
		case IRT_EQ:
			// sum x_i = y <=> sum x_i <= y /\ sum (1-x_i) <= (-y+x.size())
			new BoolLinearLE<0>(x, IntView<0>(y));
			new BoolLinearLE<5>(x2, IntView<5>(y, 1, x.size()));
			break;
		case IRT_LE:
			// sum x_i <= y
			new BoolLinearLE<0>(x, IntView<0>(y));
			break;
		case IRT_LT:
			// sum x_i < y <=> sum x_i <= (y-1)
			new BoolLinearLE<4>(x, IntView<4>(y, 1, -1));
			break;
		case IRT_GE:
			// sum x_i >= y <=> sum (1-x_i) <= (-y+x.size())
			new BoolLinearLE<5>(x2, IntView<5>(y, 1, x.size()));
			break;
		case IRT_GT:
			// sum x_i > y <=> sum (1-x_i) <= (-y+x.size()-1)
			new BoolLinearLE<5>(x2, IntView<5>(y, 1, x.size() - 1));
			break;
		default:
			CHUFFED_ERROR("Unknown IntRelType %d\n", t);
	}
}
