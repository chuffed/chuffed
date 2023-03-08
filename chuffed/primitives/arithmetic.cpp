#include <chuffed/core/propagator.h>

//-----
// Absolute propagator
// y = |x|

template <int U = 0, int V = 0>
class Abs : public Propagator, public Checker {
public:
	IntView<U> x;
	IntView<V> y;

	Abs(IntView<U> _x, IntView<V> _y) : x(_x), y(_y) {
		priority = 1;
		x.attach(this, 0, EVENT_LU);
		y.attach(this, 1, EVENT_U);
	}

	bool propagate() override {
		int64_t l = x.getMin();
		int64_t u = x.getMax();

		if (l >= 0) {
			setDom(y, setMin, l, x.getMinLit());
			setDom(y, setMax, u, x.getMinLit(), x.getMaxLit());
		} else if (u <= 0) {
			setDom(y, setMin, -u, x.getMaxLit());
			setDom(y, setMax, -l, x.getMaxLit(), x.getMinLit());
		} else {
			// Finesse stronger bound
			int64_t t = (-l > u ? -l : u);
			setDom(y, setMax, t, x.getMaxLit(), x.getMinLit());
			//			setDom(y, setMax, t, x.getFMaxLit(t), x.getFMinLit(-t));
			//			setDom(y, setMax, t, x.getLit(t+1, 2), x.getLit(-t-1, 3));
		}

		setDom(x, setMax, y.getMax(), y.getMaxLit());
		setDom(x, setMin, -y.getMax(), y.getMaxLit());

		/*
				if (x.isFixed()) {
					if (x.getVal() < 0) {
						setDom(y, setMin, -x.getVal(), x.getMaxLit());
						setDom(y, setMax, -x.getVal(), x.getMinLit());
					} else if (x.getVal() > 0) {
						setDom(y, setMin, x.getVal(), x.getMinLit());
						setDom(y, setMax, x.getVal(), x.getMaxLit());
					} else {
						setDom(y, setVal, 0, x.getMinLit(), x.getMaxLit());
					}
				}
		*/

		return true;
	}

	bool check() override {
		return ((x.getShadowVal() == y.getShadowVal()) || (x.getShadowVal() == -y.getShadowVal()));
	}
};

// y = |x|

void int_abs(IntVar* x, IntVar* y) {
	int_rel(y, IRT_GE, 0);
	new Abs<>(IntView<>(x), IntView<>(y));
}

//-----
// Integer Power propagator
// z = x ^ y

int64_t my_pow(const int64_t base, const int64_t exponent) {
	assert(exponent >= 0);
	if (exponent == 0) {
		return 1;
	}
	if (base == 0) {
		return 0;
	}
	int64_t z = base;
	for (int i = 1; i < exponent; i++) {
		z *= base;
	}
	return z;
}

template <int X = 0, int Y = 0, int Z = 0>
class PowerPos : public Propagator {
public:
	IntView<X> x;
	IntView<Y> y;
	IntView<Z> z;

	PowerPos(IntView<X> _x, IntView<Y> _y, IntView<Z> _z) : x(_x), y(_y), z(_z) {
		priority = 1;
		assert(x.getMin() >= 0);
		assert(y.getMin() > 0);
		x.attach(this, 0, EVENT_LU);
		y.attach(this, 1, EVENT_LU);
		z.attach(this, 2, EVENT_LU);
	}

	bool propagate() override {
		// Check for case 0
		if (!propagate_case_zero()) {
			return false;
		}
		// Check for case 1
		if (!propagate_case_one()) {
			return false;
		}
		// Propagation on z
		if (!propagate_z()) {
			return false;
		}
		// Propagation on x
		if (!propagate_x()) {
			return false;
		}
		// Propagation on y
		if (!propagate_y()) {
			return false;
		}

		return true;
	}

	// If x = 0 then z = 0. If z = 0 then x = 0.
	bool propagate_case_zero() {
		// x -> z
		if (x.getMax() == 0) {
			setDom(z, setMax, 0, x.getMaxLit());
		}
		// z -> x
		if (z.getMax() == 0) {
			setDom(x, setMax, 0, z.getMaxLit());
		}
		return true;
	}

	// If x = 1 then z = 1. If z = 1 then x = 1.
	bool propagate_case_one() {
		// x -> z
		if (x.getMin() == 1 && x.getMax() == 1) {
			setDom(z, setMax, 1, x.getMinLit(), x.getMaxLit());
			setDom(z, setMin, 1, x.getMinLit(), x.getMaxLit());
		}
		// z -> x
		if (z.getMin() == 1 && z.getMax() == 1) {
			setDom(x, setMax, 1, z.getMinLit(), z.getMaxLit());
			setDom(x, setMin, 1, z.getMinLit(), z.getMaxLit());
		}
		return true;
	}

	// Propagation on z
	bool propagate_z() {
		// Propagation on the lower bound
		double z_min_new = pow(x.getMin(), y.getMin());
		if (z_min_new > (double)IntVar::min_limit) {
			setDom(z, setMin, z_min_new, x.getMinLit(), y.getMinLit());
		}
		// Propagation on the upper bound
		double z_max_new = pow(x.getMax(), y.getMax());
		if (z_max_new < (double)IntVar::max_limit) {
			setDom(z, setMax, z_max_new, x.getMaxLit(), y.getMaxLit());
		}
		return true;
	}

	// Propagation on x
	bool propagate_x() {
		// Propagation on the lower bound
		double pow_res;
		pow_res = pow(z.getMin(), 1 / (double)y.getMax());
		int64_t x_min_new = ceil(pow_res);
		if (x_min_new > x.getMin()) {
			// Check for numerical errors and correct them
			if (z.getMin() <= my_pow(x_min_new - 1, y.getMax())) {
				x_min_new--;
			}
			setDom(x, setMin, x_min_new, z.getMinLit(), y.getMaxLit());
		}
		// Propagation on the upper bound
		pow_res = pow(z.getMax(), 1 / (double)y.getMin());
		int64_t x_max_new = floor(pow_res);
		if (x_max_new < x.getMax()) {
			// Check for numerical errors and correct them
			if (z.getMax() >= my_pow(x_max_new + 1, y.getMin())) {
				x_max_new++;
			}
			setDom(x, setMax, x_max_new, z.getMaxLit(), y.getMinLit());
		}
		return true;
	}

	// Propagation on y
	bool propagate_y() {
		double log_res;
		// Propagation on the lower bound
		if (z.getMin() > 0 && x.getMax() > 1) {
			log_res = log2(z.getMin()) / log2(x.getMax());
			int64_t y_min_new = ceil(log_res);
			if (y_min_new > y.getMin()) {
				// Check for numerical errors and correct them
				if (z.getMin() <= my_pow(x.getMax(), y_min_new - 1)) {
					y_min_new--;
				}
				setDom(y, setMin, y_min_new, z.getMinLit(), x.getMaxLit());
			}
		}
		// Propagation on the upper bound
		if (x.getMin() > 1) {
			log_res = log2(z.getMax()) / log2(x.getMin());
			int64_t y_max_new = floor(log_res);
			if (y_max_new < y.getMax()) {
				// Check for numerical errors and correct them
				if (z.getMax() <= my_pow(x.getMin(), y_max_new + 1)) {
					y_max_new++;
				}
				setDom(x, setMax, y_max_new, z.getMaxLit(), x.getMinLit());
			}
		}
		return true;
	}
};

void int_pow(IntVar* x, IntVar* y, IntVar* z) {
	// Since we are dealing with integer the exponent 'y' must be at least -1
	// int_rel(y, IRT_GE, -1);
	if (0 <= x->getMin() && 0 < y->getMin()) {
		int_rel(z, IRT_GE, 0);
		new PowerPos<0, 0, 0>(IntView<>(x), IntView<>(y), IntView<>(z));
	} else {
		CHUFFED_ERROR(
				"The constraint int_pow is not yet supported for non-negative base and exponent integer!");
	}
}

//-----
// Times propagator with no assumptions on the variables' bounds

// x * y = z

template <int X = 0, int Y = 0, int Z = 0>
class TimesAll : public Propagator {
public:
	IntView<X> x;
	IntView<Y> y;
	IntView<Z> z;

	TimesAll(IntView<X> _x, IntView<Y> _y, IntView<Z> _z) : x(_x), y(_y), z(_z) {
		priority = 1;
		x.attach(this, 0, EVENT_LU);
		y.attach(this, 1, EVENT_LU);
		z.attach(this, 2, EVENT_LU);
	}

	bool propagate() override {
		const int64_t x_min = x.getMin();
		const int64_t x_max = x.getMax();
		const int64_t y_min = y.getMin();
		const int64_t y_max = y.getMax();

		// Propagating the bounds on z
		if (!propagate_z(x_min, x_max, y_min, y_max)) {
			return false;
		}

		const int64_t z_min = z.getMin();
		const int64_t z_max = z.getMax();

		// Propagating the bounds on x
		if (!propagate_xy(x, y, y_min, y_max, z_min, z_max)) {
			return false;
		}

		// Propagating the bounds on y
		if (!propagate_xy(y, x, x_min, x_max, z_min, z_max)) {
			return false;
		}

		return true;
	}

	// Propagation on the bounds of z
	bool propagate_z(const int64_t x_min, const int64_t x_max, const int64_t y_min,
									 const int64_t y_max) {
		// Computing all possible extreme points of x * y
		int64_t prod_min_min = x_min * y_min;
		int64_t prod_min_max = x_min * y_max;
		int64_t prod_max_min = x_max * y_min;
		int64_t prod_max_max = x_max * y_max;

		// New lower bound on z
		int64_t z_min_new = std::min(prod_min_min, prod_min_max);
		z_min_new = std::min(z_min_new, prod_max_min);
		z_min_new = std::min(z_min_new, prod_max_max);

		if (z_min_new > IntVar::min_limit) {
			// TODO Better explanation
			Clause* reason = nullptr;
			if (so.lazy) {
				reason = Reason_new(5);
				(*reason)[1] = x.getMinLit();
				(*reason)[2] = x.getMaxLit();
				(*reason)[3] = y.getMinLit();
				(*reason)[4] = y.getMaxLit();
			}
			setDom(z, setMin, z_min_new, reason);
		}

		// New upper bound on z
		int64_t z_max_new = std::max(prod_min_min, prod_min_max);
		z_max_new = std::max(z_max_new, prod_max_min);
		z_max_new = std::max(z_max_new, prod_max_max);

		if (z_max_new < IntVar::max_limit) {
			// TODO Better explanation
			Clause* reason = nullptr;
			if (so.lazy) {
				reason = Reason_new(5);
				(*reason)[1] = x.getMinLit();
				(*reason)[2] = x.getMaxLit();
				(*reason)[3] = y.getMinLit();
				(*reason)[4] = y.getMaxLit();
			}
			setDom(z, setMax, z_max_new, reason);
		}

		return true;
	}

	template <int U, int V>
	bool propagate_xy(IntView<U> u, IntView<V> v, const int64_t v_min, const int64_t v_max,
										const int64_t z_min, const int64_t z_max) {
		if (z_min == 0 && z_max == 0) {
			// The product z equals to 0. Then x must equal to 0 too if y cannot be 0.
			if (v_min > 0 || v_max < 0) {
				// TODO Better explanation
				Clause* reason = nullptr;
				if (so.lazy) {
					reason = Reason_new(5);
					(*reason)[1] = v.getMinLit();
					(*reason)[2] = v.getMaxLit();
					(*reason)[3] = z.getMinLit();
					(*reason)[4] = z.getMaxLit();
				}
				setDom(u, setMin, 0, reason);
				setDom(u, setMax, 0, reason);
			}
		} else if (z_min > 0) {
			if (v_min == 0) {
				// TODO Better explanation
				Clause* reason = nullptr;
				if (so.lazy) {
					reason = Reason_new(3);
					(*reason)[1] = z.getMinLit();
					(*reason)[2] = v.getMinLit();
				}
				setDom(v, setMin, 1, reason);
			} else if (v_max == 0) {
				// TODO Better explanation
				Clause* reason = nullptr;
				if (so.lazy) {
					reason = Reason_new(3);
					(*reason)[1] = z.getMinLit();
					(*reason)[2] = v.getMaxLit();
				}
				setDom(v, setMax, -1, reason);
			} else {
				if (!propagate_xy_min(u, v, v_min, v_max, z_min, z_max)) {
					return false;
				}
				if (!propagate_xy_max(u, v, v_min, v_max, z_min, z_max)) {
					return false;
				}
			}
		} else if (z_max < 0) {
			if (v_min == 0) {
				// TODO Better explanation
				Clause* reason = nullptr;
				if (so.lazy) {
					reason = Reason_new(3);
					(*reason)[1] = z.getMaxLit();
					(*reason)[2] = v.getMinLit();
				}
				setDom(v, setMin, 1, reason);
			} else if (v_max == 0) {
				// TODO Better explanation
				Clause* reason = nullptr;
				if (so.lazy) {
					reason = Reason_new(3);
					(*reason)[1] = z.getMaxLit();
					(*reason)[2] = v.getMaxLit();
				}
				setDom(v, setMax, -1, reason);
			} else {
				if (!propagate_xy_min(u, v, v_min, v_max, z_min, z_max)) {
					return false;
				}
				if (!propagate_xy_max(u, v, v_min, v_max, z_min, z_max)) {
					return false;
				}
			}
		}
		return true;
	}

	template <int U, int V>
	bool propagate_xy_min(IntView<U> u, IntView<V> v, const int64_t v_min, const int64_t v_max,
												const int64_t z_min, const int64_t z_max) {
		assert(z_min > 0 || z_max < 0);
		assert(v_min != 0 && v_max != 0);
		// The product z cannot be 0. Then x and y cannot be 0, too.
		// x >= ceil(z / y)
		int64_t u_min_new = 0;
		if (v_max < 0) {
			// Integer variable v is negative
			if (z_min > 0) {
				// Integer variable z is positive
				u_min_new = (z_max - v_max - 1) / v_max;
			} else {
				// Integer variable z is negative
				u_min_new = (-z_max - v_min - 1) / -v_min;
			}
		} else if (v_min > 0) {
			// Integer variable is positive
			if (z_min > 0) {
				// Integer variable z is positive
				u_min_new = (z_min + v_max - 1) / v_max;
			} else {
				// Integer variable z is negative
				u_min_new = (-z_min + v_min - 1) / -v_min;
			}
		} else {
			// The domain of integer variable v contains -1 and 1
			u_min_new = std::min(-1 * z_min, z_min);
			u_min_new = std::min(u_min_new, z_max);
			u_min_new = std::min(u_min_new, -1 * z_max);
		}

		if (u_min_new > u.getMin()) {
			// TODO Better explanation
			Clause* reason = nullptr;
			if (so.lazy) {
				reason = Reason_new(5);
				(*reason)[1] = v.getMinLit();
				(*reason)[2] = v.getMaxLit();
				(*reason)[3] = z.getMinLit();
				(*reason)[4] = z.getMaxLit();
			}
			setDom(u, setMin, (u_min_new == 0 ? 1 : u_min_new), reason);
		}

		return true;
	}

	template <int U, int V>
	bool propagate_xy_max(IntView<U> u, IntView<V> v, const int64_t v_min, const int64_t v_max,
												const int64_t z_min, const int64_t z_max) {
		assert(z_min > 0 || z_max < 0);
		assert(v_min != 0 && v_max != 0);
		// The product z cannot be 0. Then x and y cannot be 0, too.
		// u <= floor(z / v)
		int64_t u_max_new = 0;
		if (v_min < 0 && v_max > 0) {
			// The domain of integer variable v contains -1 and 1
			u_max_new = std::max(-1 * z_min, z_min);
			u_max_new = std::max(u_max_new, z_max);
			u_max_new = std::max(u_max_new, -1 * z_max);
		} else {
			u_max_new = (v_max < 0 ? z_min : z_max) / (z_min > 0 ? v_min : v_max);
		}

		if (u_max_new < u.getMax()) {
			// TODO Better explanation
			Clause* reason = nullptr;
			if (so.lazy) {
				reason = Reason_new(5);
				(*reason)[1] = v.getMinLit();
				(*reason)[2] = v.getMaxLit();
				(*reason)[3] = z.getMinLit();
				(*reason)[4] = z.getMaxLit();
			}
			setDom(u, setMax, (u_max_new == 0 ? -1 : u_max_new), reason);
		}

		return true;
	}
};

//-----

// x * y = z     x, y, z >= 0

template <int U = 0, int V = 0, int W = 0>
class Times : public Propagator, public Checker {
public:
	IntView<U> x;
	IntView<V> y;
	IntView<W> z;

	Times(IntView<U> _x, IntView<V> _y, IntView<W> _z) : x(_x), y(_y), z(_z) {
		priority = 1;
		assert(x.getMin() >= 0 && y.getMin() >= 0 && z.getMin() >= 0);
		x.attach(this, 0, EVENT_LU);
		y.attach(this, 1, EVENT_LU);
		z.attach(this, 2, EVENT_LU);
	}

	bool propagate() override {
		int64_t x_min = x.getMin();
		int64_t x_max = x.getMax();
		int64_t y_min = y.getMin();
		int64_t y_max = y.getMax();
		int64_t z_min = z.getMin();
		int64_t z_max = z.getMax();

		// z >= x.min * y.min
		setDom(z, setMin, x_min * y_min, x.getMinLit(), y.getMinLit());
		// z <= x.max * y.max
		if (x_max * y_max < IntVar::max_limit) {
			setDom(z, setMax, x_max * y_max, x.getMaxLit(), y.getMaxLit());
		}

		// x >= ceil(z.min / y.max)
		if (y_max >= 1) {
			setDom(x, setMin, (z_min + y_max - 1) / y_max, y.getMaxLit(), z.getMinLit());
		}

		// x <= floor(z.max / y.min)
		if (y_min >= 1) {
			setDom(x, setMax, z_max / y_min, y.getMinLit(), z.getMaxLit());
		}

		// y >= ceil(z.min / x.max)
		if (x_max >= 1) {
			setDom(y, setMin, (z_min + x_max - 1) / x_max, x.getMaxLit(), z.getMinLit());
		}

		// y <= floor(z.max / x.min)
		if (x_min >= 1) {
			setDom(y, setMax, z_max / x_min, x.getMinLit(), z.getMaxLit());
		}

		return true;
	}

	bool check() override { return (x.getShadowVal() * y.getShadowVal() == z.getShadowVal()); }
};

int get_sign(IntVar* x) {
	if (x->getMin() >= 0) {
		return 1;
	}
	if (x->getMax() <= 0) {
		return -1;
	}
	return 0;
}

// z = x * y

void int_times(IntVar* x, IntVar* y, IntVar* z) {
	if ((get_sign(x) == 0) || (get_sign(y) == 0) || (get_sign(z) == 0)) {
		new TimesAll<0, 0, 0>(IntView<>(x), IntView<>(y), IntView<>(z));
	} else {
		bool x_flip = (get_sign(x) == -1);
		bool y_flip = (get_sign(y) == -1);
		bool z_flip = (get_sign(z) == -1);

		if (!x_flip && !y_flip && !z_flip) {
			new Times<0, 0, 0>(IntView<>(x), IntView<>(y), IntView<>(z));
		} else if (!x_flip && y_flip && z_flip) {
			new Times<0, 1, 1>(IntView<>(x), IntView<>(y), IntView<>(z));
		} else if (x_flip && !y_flip && z_flip) {
			new Times<1, 0, 1>(IntView<>(x), IntView<>(y), IntView<>(z));
		} else if (x_flip && y_flip && !z_flip) {
			new Times<1, 1, 0>(IntView<>(x), IntView<>(y), IntView<>(z));
		} else {
			// as: This case is an inconsistency in the model!
			CHUFFED_ERROR("Cannot handle this case\n");
		}
	}
}

//-----

// ceil(x / y) = z     x, y, z >= 0

// x / y <= z
// x / y > z - 1

// floor(x / y) = z  <=>  ceil(x+1 / y) = z+1

template <int U = 0, int V = 0, int W = 0>
class Divide : public Propagator, public Checker {
public:
	IntView<U> x;
	IntView<V> y;
	IntView<W> z;

	Divide(IntView<U> _x, IntView<V> _y, IntView<W> _z) : x(_x), y(_y), z(_z) {
		priority = 1;
		assert(x.getMin() >= 0 && y.getMin() >= 1 && z.getMin() >= 0);
		x.attach(this, 0, EVENT_LU);
		y.attach(this, 1, EVENT_LU);
		z.attach(this, 2, EVENT_LU);
	}

	bool propagate() override {
		int64_t x_min = x.getMin();
		int64_t x_max = x.getMax();
		int64_t y_min = y.getMin();
		int64_t y_max = y.getMax();
		int64_t z_min = z.getMin();
		int64_t z_max = z.getMax();

		// z >= ceil(x.min / y.max)
		setDom(z, setMin, (x_min + y_max - 1) / y_max, x.getMinLit(), y.getMaxLit());
		// z <= ceil(x.max / y.min)
		setDom(z, setMax, (x_max + y_min - 1) / y_min, x.getMaxLit(), y.getMinLit());

		// x >= y.min * (z.min - 1) + 1
		setDom(x, setMin, y_min * (z_min - 1) + 1, y.getMinLit(), z.getMinLit());
		// x <= y.max * z.max
		setDom(x, setMax, y_max * z_max, y.getMaxLit(), z.getMaxLit());

		// y >= ceil(x.min / z.max)
		if (z_max >= 1) {
			setDom(y, setMin, (x_min + z_max - 1) / z_max, x.getMinLit(), z.getMaxLit());
		}

		// y <= ceil(x.max / z.min-1) - 1
		if (z_min >= 2) {
			setDom(y, setMax, (x_max + z_min - 2) / (z_min - 1) - 1, x.getMaxLit(), z.getMinLit());
		}

		return true;
	}

	bool check() override {
		auto ceil_div = [](int64_t x, int64_t y) { return (x + (y - 1)) / y; };
		return ceil_div(x.getShadowVal(), y.getShadowVal()) == z.getShadowVal();
	}
};

// z = floor(x / y)

void int_div(IntVar* x, IntVar* y, IntVar* z) {
	if ((get_sign(x) == 0) || (get_sign(y) == 0) || (get_sign(z) == 0)) {
		CHUFFED_ERROR("Cannot handle non-sign-fixed vars\n");
	}
	bool x_flip = (get_sign(x) == -1);
	bool y_flip = (get_sign(y) == -1);
	bool z_flip = (get_sign(z) == -1);

	if (!x_flip && !y_flip && !z_flip) {
		// ceil(x+1 / y) = z+1
		new Divide<4, 0, 4>(IntView<>(x, 1, 1), IntView<>(y), IntView<>(z, 1, 1));
	} else if (!x_flip && y_flip && z_flip) {
		// ceil(x / -y) = -z
		new Divide<0, 1, 1>(IntView<>(x), IntView<>(y), IntView<>(z));
	} else if (x_flip && !y_flip && z_flip) {
		// ceil(-x / y) = -z
		new Divide<1, 0, 1>(IntView<>(x), IntView<>(y), IntView<>(z));
	} else if (x_flip && y_flip && !z_flip) {
		// ceil(-x+1 / -y) = z+1
		new Divide<5, 1, 4>(IntView<>(x, 1, 1), IntView<>(y), IntView<>(z, 1, 1));
	} else {
		CHUFFED_ERROR("Cannot handle this case\n");
	}
}

void int_mod(IntVar* x, IntVar* y, IntVar* z) { CHUFFED_ERROR("Not yet supported\n"); }

// z = min(x, y)

template <int U>
class Min2 : public Propagator, public Checker {
public:
	IntView<U> x, y, z;

	Min2(IntView<U> _x, IntView<U> _y, IntView<U> _z) : x(_x), y(_y), z(_z) {
		priority = 1;
		x.attach(this, 0, EVENT_LU);
		y.attach(this, 1, EVENT_LU);
		z.attach(this, 2, EVENT_L);
	}

	bool propagate() override {
		// make a less than or equal to min(max(b_i))

		setDom(z, setMax, x.getMax(), x.getMaxLit());
		setDom(z, setMax, y.getMax(), y.getMaxLit());

		int64_t m = (x.getMin() < y.getMin() ? x.getMin() : y.getMin());
		setDom(z, setMin, m, x.getFMinLit(m), y.getFMinLit(m));

		setDom(x, setMin, z.getMin(), z.getMinLit());
		setDom(y, setMin, z.getMin(), z.getMinLit());

		if (z.getMin() == x.getMax() || z.getMin() == y.getMax()) {
			satisfied = true;
		}

		return true;
	}

	bool check() override {
		return ((int)std::min(x.getShadowVal(), y.getShadowVal()) == z.getShadowVal());
	}

	int checkSatisfied() override {
		if (satisfied) {
			return 1;
		}
		if (z.getMin() == x.getMax() || z.getMin() == y.getMax()) {
			satisfied = true;
		}
		return 3;
	}
};

void int_min(IntVar* x, IntVar* y, IntVar* z) {
	new Min2<0>(IntView<0>(x), IntView<0>(y), IntView<0>(z));
}

void int_max(IntVar* x, IntVar* y, IntVar* z) {
	new Min2<1>(IntView<1>(x), IntView<1>(y), IntView<1>(z));
}

//-----

// z = x + y

void int_plus(IntVar* x, IntVar* y, IntVar* z) {
	vec<int> coeffs;
	vec<IntVar*> w;
	coeffs.push(1);
	w.push(x);
	coeffs.push(1);
	w.push(y);
	coeffs.push(-1);
	w.push(z);
	int_linear(coeffs, w, IRT_EQ, 0);
}

//-----

// z = x - y

void int_minus(IntVar* x, IntVar* y, IntVar* z) { int_plus(y, z, x); }

//-----

// y = -x

void int_negate(IntVar* x, IntVar* y) { bin_linear(x, y, IRT_EQ, 0); }

//-----

// y = bool2int(x)

void bool2int(BoolView x, IntVar* y) {
	int_rel(y, IRT_GE, 0);
	int_rel(y, IRT_LE, 1);
	y->specialiseToEL();
	bool_rel(x, BRT_EQ, BoolView(y->getLit(1, 2)));
}
