#include "chuffed/core/propagator.h"
#include "chuffed/vars/bool-view.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/vars.h"

#include <cassert>
#include <utility>

// y = |ub(x) - lb(y) + 1|
class RangeSize : public Propagator {
public:
	IntVar* x;
	IntVar* y;

	RangeSize(IntVar* _x, IntVar* _y) : x(_x), y(_y) {
		priority = 1;
		x->attach(this, 0, EVENT_LU);
	}

	bool propagate() override {
		if (y->getMin() < 1) {
			setDom((*y), setMin, 1, y->getMinLit());
		}
		setDom((*y), setMax, x->getMax() - x->getMin() + 1, x->getMinLit(), x->getMaxLit());
		return true;
	}
};

void range_size(IntVar* x, IntVar* y) { new RangeSize(x, y); }

template <class Var, class Val>
class LastVal : public Propagator {
public:
	Var* x;
	Val* v;

	LastVal(Var* _x, Val* _v) : x(_x), v(_v) {
		priority = 0;
		x->attach(this, 0, EVENT_F);
	}

	void wakeup(int i, int c) override {
		assert(x->isFixed());
		pushInQueue();
	}

	bool propagate() override {
		(*v) = x->getVal();
		return true;
	}
};

void last_val(IntVar* x, int* v) { new LastVal<IntVar, int>(x, v); }
void last_val(BoolView* x, bool* v) { new LastVal<BoolView, bool>(x, v); }

class Complete : public Propagator {
public:
	BoolView x;
	bool* v;

	Complete(BoolView _x, bool* _v) : x(std::move(_x)), v(_v) {
		priority = 0;
		x.attach(this, 0, EVENT_F);
	}

	void wakeup(int i, int c) override {
		assert(x.isFixed());
		pushInQueue();
	}

	bool propagate() override {
		if (x.isTrue()) {
			(*v) = true;
		}
		return true;
	}
};

void mark_complete(BoolView x, bool* v) { new Complete(x, v); }
