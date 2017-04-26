#include <chuffed/core/propagator.h>

// y = |ub(x) - lb(y) + 1|
class RangeSize : public Propagator {
public:
    IntVar* x;
    IntVar* y;

    RangeSize(IntVar* _x, IntVar* _y) : x(_x), y(_y) {
        priority = 1;
        x->attach(this, 0, EVENT_LU);
    }

    bool propagate() {
        if (y->getMin() < 1)
            setDom((*y), setMin, 1, y->getMinLit());
        setDom((*y), setMax, x->getMax() - x->getMin() + 1, x->getMinLit(), x->getMaxLit());
        return true;
    }
};

void range_size(IntVar* x, IntVar* y) {
    new RangeSize(x, y);
}
