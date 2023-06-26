#include <chuffed/core/propagator.h>

#include <algorithm>
#include <climits>
#include <unordered_set>

// Propagator for the value_precede constraint.
class value_precede : public Propagator {
	// The only propagation which occurs is:
	struct tag_t {
		tag_t() : si(0), ti(0), flag(0) {}
		tag_t(int _si, int _ti, bool _flag) : flag(_flag), si(_si), ti(_ti) {}

		unsigned flag : 1;
		unsigned si : 15;
		unsigned ti : 16;
	};
	static tag_t s_tag(int si, int ti) { return tag_t(si, ti, false); }
	static tag_t t_tag(int ti) { return tag_t(0, ti, true); }

	Clause* ex_s(int si, int ti) {
		Clause* r(Reason_new(ti + 1));
		int jj = 1;
		for (int ii = 0; ii < si; ++ii, ++jj) {
			(*r)[jj] = xs[ii]->getLit(s, LR_EQ);
		}
		for (int ii = si + 1; ii < ti; ++ii, ++jj) {
			(*r)[jj] = xs[ii]->getLit(s, LR_EQ);
		}
		(*r)[jj++] = xs[ti]->getLit(t, LR_NE);
		assert(jj == ti + 1);
		return r;
	}

	Clause* ex_t(int ti) {
		Clause* r(Reason_new(ti + 1));
		int jj = 1;
		for (int ii = 0; ii < ti; ++ii, ++jj) {
			assert(!xs[ii]->indomain(s));
			(*r)[jj] = xs[ii]->getLit(s, LR_EQ);
		}
		return r;
	}

public:
	value_precede(int _s, int _t, vec<IntVar*>& vs) : s(_s), t(_t), satisfied(0) {
		// Find the first possible occurrence of s.
		int ii = 0;
		// Can't do remVal before initialization.
		for (; ii < vs.size(); ii++) {
			if (vs[ii]->indomain(t)) {
				int_rel(vs[ii], IRT_NE, t);
			}
			if (vs[ii]->indomain(s)) {
				break;
			}
		}

		// Now copy the remaining values.
		bool t_seen = false;
		first_s = 0;
		for (; ii < vs.size(); ii++) {
			IntVar* x(vs[ii]);
			if (x->isFixed() && x->getVal() == s) {
				break;
			}

			if (!x->indomain(s) && !x->indomain(t)) {
				continue;
			}
			xs.push(x);

			if (x->isFixed() && x->getVal() == t) {
				t_seen = true;
				break;
			}
		}

		if (xs.size() <= 1) {
			satisfied = 1;
			return;
		}

		for (int ii = 0; ii < xs.size(); ii++) {
			IntVar* x(xs[ii]);
			x->specialiseToEL();
			if (x->indomain(s)) {
				x->attach(this, ii << 1, EVENT_C);
			}
			if (x->indomain(t)) {
				x->attach(this, (ii << 1) | 1, EVENT_F);
			}
		}

		first_t = xs.size() - static_cast<int>(t_seen);

		int si = 1;
		for (; si < xs.size(); ++si) {
			if (xs[si]->indomain(s)) {
				break;
			}
		}
		second_s = si;
		if (first_t <= second_s) {
			if (!xs[first_s]->setVal(s)) {
				TL_FAIL();
			}
			satisfied = 1;
		}
	}

	Clause* explain(Lit p, int inf_id) override {
		tag_t t(conv<tag_t, int>(inf_id));
		return t.flag ? ex_t(t.ti) : ex_s(t.si, t.ti);
	}

	bool propagate() override {
		if (satisfied != 0) {
			return true;
		}

		int sz = xs.size();
		int si = first_s;
		// Update the first occurrence
		for (; si < first_t; ++si) {
			if (xs[si]->remValNotR(t)) {
				if (!xs[si]->remVal(t, Reason(prop_id, conv<int, tag_t>(t_tag(si))))) {
					return false;
				}
			}
			if (xs[si]->indomain(s)) {
				break;
			}
		}
		if (si == sz) {
			// Reached the end.
			satisfied = 1;
			return true;
		}
		if (si >= first_t) {
			if (so.lazy) {
				Clause* r(ex_t(first_t));
				(*r)[0] = xs[first_t]->getLit(t, LR_NE);
				sat.confl = r;
			}
			return false;
		}
		if (si > first_s) {
			first_s = si;
		}
		// If there's no t, stop.
		if (first_t >= sz) {
			return true;
		}
		// Now find the second occurrence
		++si;
		if (si < second_s) {
			si = second_s;
		}
		for (; si < first_t; ++si) {
			if (xs[si]->indomain(s)) {
				second_s = si;
				goto val_prec_finished;
			}
		}
		// At this point, there's only one candidate.
		if (xs[first_s]->setValNotR(s)) {
			if (!xs[first_s]->setVal(s, Reason(prop_id, conv<int, tag_t>(s_tag(first_s, first_t))))) {
				return false;
			}
		}
		satisfied = 1;
	val_prec_finished:
		return true;
	}

	void wakeup(int ii, int c) override {
		if (satisfied != 0) {
			return;
		}
		int vi = ii >> 1;
		if ((ii & 1) != 0) {
			if (vi < first_t && xs[vi]->getVal() == t) {
				first_t = vi;
				pushInQueue();
			}
		} else {
			pushInQueue();
		}
	}

	int s;
	int t;
	vec<IntVar*> xs;

	Tint first_s;
	Tint second_s;
	Tint first_t;

	Tchar satisfied;
};

// Propagator for the seq_precede_chain constraint.
class seq_precede_chain : public Propagator {
	Clause* ex_ub(int xi, int k) {
		Clause* r = Reason_new(xi + 1);

		// One of the predecessors must be (at least) k.
		for (int ii = 0; ii < xi; ++ii) {
			(*r)[ii + 1] = xs[ii]->getLit(k, LR_GE);
		}
		return r;
	}

	// Need to construct a chain.
	Clause* ex_lb(int xi, int k) {
		vec<Lit> r;
		r.push();
		// Three components.
		// Why can't the frontier already be above k?
		for (int ii = 0; ii < xi; ii++) {
			r.push(xs[ii]->getLit(k, LR_GE));
		}
		// Why can't the frontier get higher afterwards?
		int l = k;
		int ii = xi + 1;
		for (; xs[ii]->getMin() <= l; ++ii) {
			if (xs[ii]->indomain(l)) {
				++l;
			} else {
				r.push(~xs[ii]->getLit(l, LR_EQ));
			}
		}
		r.push(~(xs[ii]->getLit(l, LR_LE)));
		return Reason_new(r);
	}

	struct tag_t {
		tag_t() : flag(0), x(0), k(0) {}
		tag_t(bool _flag, int _x, int _k) : flag(_flag), x(_x), k(_k) {}

		unsigned flag : 1;
		unsigned x : 15;
		unsigned k : 16;
	};
	static int lb_tag(int x, int k) { return conv<int, tag_t>(tag_t(false, x, k)); }
	static int ub_tag(int x, int k) { return conv<int, tag_t>(tag_t(true, x, k)); }

	Clause* explain(Lit p, int inf_id) override {
		tag_t t(conv<tag_t, int>(inf_id));
		if (t.flag) {
			// Upper bound
			return ex_ub(t.x, t.k);
		}  // Lower bound
		return ex_lb(t.x, t.k);
	}

public:
	void wakeup(int ii, int c) override {
		if ((c & EVENT_L) != 0) {
			// Update limit values.
			int l = xs[ii]->getMin();
			while ((l != 0) && limit[l] > ii) {
				limit[l] = ii;
				--l;
			}
		}
		pushInQueue();
	}

	seq_precede_chain(vec<IntVar*>& _xs) : xs(_xs), vmax(0), limit(xs.size(), xs.size()) {
		int sz = xs.size();
		priority = 3;
		int M = 0;
		int low_f = 0;
		for (int ii = 0; ii < sz; ii++) {
			xs[ii]->attach(this, ii, EVENT_C);
			if (xs[ii]->getMax() > M) {
				M = xs[ii]->getMax();
			}
			if (xs[ii]->getMin() > low_f) {
				// Iniitalize limits.
				int m = xs[ii]->getMin();
				for (; m > low_f; ++low_f) {
					limit.push(ii);
				}
			}
		}

		vmax = M;
		first.push(0);
		for (int ii = 1; ii <= vmax; ++ii) {
			first.push(ii - 1);
		}
	}

	bool propagate() override {
		// Forward pass; tighten upper bounds.
		int sz = xs.size();
		int ii = 0;
		int fval = 1;
		for (; ii < sz; ++ii) {
			if (xs[ii]->setMaxNotR(fval)) {
				if (!xs[ii]->setMax(fval, Reason(prop_id, ub_tag(ii, fval)))) {
					return false;
				}
			}
			if (xs[ii]->indomain(fval)) {
				first[fval] = ii;
				++fval;
				if (fval == vmax) {
					goto forward_done;
				}
			}
		}
		// At this point, we can reduce vmax, to cut-off earlier.
		vmax = fval;

	forward_done:
		// Limit values are kept consistent by wakeup. Now we work
		// backwards, to identify the latest feasible frontier.
		// Anywhere the two frontiers coincide becomes fixed.
		int lval = vmax;
		// Skip unconstrained values
		for (; lval > 0 && limit[lval] >= sz; --lval) {
		}
		if (lval == 0) {
			return true;
		}

		// Now, just walk back through the remaining values.
		for (int ii = limit[lval]; ii >= 0; --ii) {
			if (xs[ii]->indomain(lval - 1)) {
				assert(first[lval - 1] <= ii);
				if (first[lval - 1] == ii) {
					assert(lval <= 1 || xs[ii]->getMax() == lval - 1);
					if (xs[ii]->setMinNotR(lval - 1)) {
						if (!xs[ii]->setMin(lval - 1, Reason(prop_id, lb_tag(ii, lval - 1)))) {
							return false;
						}
					}
				}
				--lval;
			} else {
				if (xs[ii]->getMin() > lval) {
					lval = xs[ii]->getMin();
				}
			}
		}
		return true;
	}

	// Parameters
	vec<IntVar*> xs;

	// Persistent state.
	Tint vmax;

	// Transient state
	vec<int> first;   // First occurrence of each ordered value
	vec<Tint> limit;  // The latest point at which we must have achieved k.
};

// Incremental version of the seq_precede_chain propagator.
class seq_precede_inc : public Propagator {
	Clause* ex_ub(int xi, int k) {
		Clause* r = Reason_new(xi + 1);

		// One of the predecessors must be (at least) k.
		for (int ii = 0; ii < xi; ++ii) {
			(*r)[ii + 1] = xs[ii]->getLit(k, LR_GE);
		}
		return r;
	}

	// Need to construct a chain.
	Clause* ex_lb(int xi, int k) {
		vec<Lit> r;
		r.push();
		// Three components.
		// Why can't the frontier already be above k?
		for (int ii = 0; ii < xi; ii++) {
			r.push(xs[ii]->getLit(k, LR_GE));
		}
		// Why can't the frontier get higher afterwards?
		int l = k;
		int ii = xi + 1;
		for (; xs[ii]->getMin() <= l; ++ii) {
			if (xs[ii]->indomain(l)) {
				++l;
			} else {
				r.push(~xs[ii]->getLit(l, LR_EQ));
			}
		}
		r.push(~(xs[ii]->getLit(l, LR_LE)));
		return Reason_new(r);
	}

	struct tag_t {
		tag_t() : flag(0), x(0), k(0) {}
		tag_t(bool _flag, int _x, int _k) : flag(_flag), x(_x), k(_k) {}

		unsigned flag : 1;
		unsigned x : 15;
		unsigned k : 16;
	};
	static int lb_tag(int x, int k) { return conv<int, tag_t>(tag_t(false, x, k)); }
	static int ub_tag(int x, int k) { return conv<int, tag_t>(tag_t(true, x, k)); }

	Clause* explain(Lit p, int inf_id) override {
		tag_t t(conv<tag_t, int>(inf_id));
		if (t.flag) {
			// Upper bound
			return ex_ub(t.x, t.k);
		}  // Lower bound
		return ex_lb(t.x, t.k);
	}

public:
	inline bool is_first(int ii) { return first[first_val[ii]] == ii; }
	inline bool is_limit(int ii) { return limit[limit_val[ii]] == ii; }

	void wakeup(int ii, int c) override {
		// How do we know when to wake up?
		if (is_first(ii) && xs[ii]->getMax() < first_val[ii]) {
			first_change.push(first_val[ii]);
			pushInQueue();
		}
		int m = xs[ii]->getMin();
		// Can probably actually relax this to m > 1.
		if (m > 0 && ii < limit[m]) {
			if (max_def < m) {
				max_def = m;
			}
			limit_change.push(m);
			limit[m] = ii;
			limit_val[ii] = m;
			pushInQueue();
		}
		if (is_limit(ii) && !xs[ii]->indomain(limit_val[ii])) {
			limit_change.push(limit_val[ii]);
			pushInQueue();
		}
	}

	void clearPropState() override {
		in_queue = false;
		first_change.clear();
		limit_change.clear();
	}

	void log_state() {
		fprintf(stderr, "LB: [");
		if (xs.size() > 0) {
			fprintf(stderr, "%d", xs[0]->getMin());
			for (int ii = 1; ii < xs.size(); ii++) {
				fprintf(stderr, ", %d", xs[ii]->getMin());
			}
		}
		fprintf(stderr, "]\n");
		fprintf(stderr, "UB: [");
		if (xs.size() > 0) {
			fprintf(stderr, "%d", xs[0]->getMax());
			for (int ii = 1; ii < xs.size(); ii++) {
				fprintf(stderr, ", %d", xs[ii]->getMax());
			}
		}
		fprintf(stderr, "]\n");

		fprintf(stderr, "FS: [");
		if (first.size() > 0) {
			fprintf(stderr, "%d", first[0].v);
			for (int ii = 1; ii < first.size(); ii++) {
				fprintf(stderr, ", %d", first[ii].v);
			}
		}
		fprintf(stderr, "]\n");

		fprintf(stderr, "LM: [");
		if (limit.size() > 0) {
			fprintf(stderr, "%d", limit[0].v);
			for (int ii = 1; ii < limit.size(); ii++) {
				fprintf(stderr, ", %d", limit[ii].v);
			}
		}
		fprintf(stderr, "]\n");

		fprintf(stderr, "FV: [");
		if (first_val.size() > 0) {
			fprintf(stderr, "%d", first_val[0].v);
			for (int ii = 1; ii < first_val.size(); ii++) {
				fprintf(stderr, ", %d", first_val[ii].v);
			}
		}
		fprintf(stderr, "]\n");

		fprintf(stderr, "LV: [");
		if (limit_val.size() > 0) {
			fprintf(stderr, "%d", limit_val[0].v);
			for (int ii = 1; ii < limit_val.size(); ii++) {
				fprintf(stderr, ", %d", limit_val[ii].v);
			}
		}
		fprintf(stderr, "]\n");
	}

	void check_firsts() {
		for (int ii = 1; ii < first.size(); ii++) {
			for (int jj = 0; jj < first[ii]; ++jj) {
				assert(xs[jj]->getMax() < ii);
			}
		}
	}

	bool propagate() override {
		// fprintf(stderr, "Running value-precede-chain.\n");
		// fprintf(stderr, "BEFORE value-precede-chain:\n");
		// log_state();
		// fprintf(stderr, "Queues: [%d, %d].\n", first_change.size(), limit_change.size());
		for (int fi = 0; fi < first_change.size(); fi++) {
			if (!repair_upper(first_change[fi])) {
				return false;
			}
		}
		first_change.clear();

		for (int li = 0; li < limit_change.size(); li++) {
			if (!repair_limit(limit_change[li])) {
				return false;
			}
		}
		limit_change.clear();

		return true;
	}

	seq_precede_inc(vec<IntVar*>& _xs)
			: xs(_xs),
				max_def(0),
				max_val(xs.size()),
				first(xs.size() + 1, 0),
				limit(xs.size() + 1, xs.size()),
				first_val(xs.size(), 0),
				limit_val(xs.size(), xs.size()) {
		int sz = xs.size();
		priority = 3;

		// Set unused zero value out of range
		first[0] = -1;
		limit[0] = xs.size() + 1;

		int M = 1;
		// Initialize firsts.
		for (int ii = 0; ii < sz; ii++) {
			if (xs[ii]->setMaxNotR(M)) {
				if (!xs[ii]->setMax(M)) {
					TL_FAIL();
				}
			}
			if (xs[ii]->indomain(M)) {
				first[M] = ii;
				first_val[ii] = M;
				++M;
			}
			xs[ii]->attach(this, ii, EVENT_C);
		}
		max_val = M - 1;

		// check_firsts();

		// Initialize lasts.
		int m = 0;
		int k = 0;
		for (int ii = sz - 1; ii >= 0; --ii) {
			int mx = xs[ii]->getMin();
			if (mx > k) {
				k = mx;
				if (mx > m) {
					m = mx;
				}
			}
			if ((k != 0) && xs[ii]->indomain(k)) {
				limit[k] = ii;
				limit_val[ii] = k;
				// Definite occurrence
				if (first[k] == ii && xs[ii]->setMinNotR(k)) {
					if (!xs[ii]->setMin(k)) {
						TL_FAIL();
					}
				}
				--k;
			}
		}
		max_def = m;
	}

	bool repair_upper(int k) {
		if (k >= max_val) {
			return true;
		}
		unsigned int ii = first[k];
		unsigned int lim = limit[k + 1];
		for (; ii < lim; ++ii) {
			if (xs[ii]->setMaxNotR(k)) {
				if (!xs[ii]->setMax(k, Reason(prop_id, ub_tag(ii, k)))) {
					return false;
				}
			}
			if (xs[ii]->indomain(k)) {
				// Found the earliest occurrence of k; update.
				first[k] = ii;
				first_val[ii] = k;

				// Check if we need to continue with k+1
				++k;
				// ++ii;
				if (k == max_val || ii < first[k]) {
					return true;
				}
				lim = limit[k + 1];
			}
		}
		// We've either tightened the maximum value, or
		// the first occurrence of k is too late.
		if (ii < xs.size()) {
			// Failure: no occurrence of
			if (so.lazy) {
				vec<Lit> ex;
				for (int xi = 0; xi < ii; ++xi) {
					assert(xs[xi]->getMax() < k);
					ex.push(xs[xi]->getLit(k, LR_GE));
				}
				for (; xs[ii]->getMin() <= k; ++ii) {
					if (xs[ii]->indomain(k)) {
						++k;
					} else {
						ex.push(xs[ii]->getLit(k, LR_EQ));
					}
				}
				ex.push(xs[ii]->getLit(k, LR_LE));
				sat.confl = Reason_new(ex);
			}
			return false;
		}
		// No supports for k.
		assert(k < max_val);
		max_val = k;
		return true;
	}

	// Always repair limit after upper bounds,
	// so we detect infeasibility the easy way.
	bool repair_limit(int k) {
		int ii = limit[k];
		for (; ii >= 0; --ii) {
			// No change
			if (k < 1 || limit[k] < ii) {
				return true;
			}
			assert(ii >= first[k]);
			if (xs[ii]->indomain(k)) {
				limit[k] = ii;
				limit_val[ii] = k;
				if (ii == first[k]) {
					// First and last occurrences coincide.
					if (xs[ii]->setMinNotR(k)) {
						if (!xs[ii]->setMin(k, Reason(prop_id, lb_tag(ii, k)))) {
							return false;
						}
					}
				}
				k--;
			}
		}
		return true;
	}

	// Parameters
	vec<IntVar*> xs;

	// Persistent state
	vec<Tint> first;  // First occurrence of each ordered value
	vec<Tint> limit;  // The latest point at which we must have achieved k.

	vec<Tint> first_val;  // If this variable is a first, what is the value value?
	vec<Tint> limit_val;  // Similarly, if this is a limit, to what value?

	Tint max_val;  // Largest value which could occur
	Tint max_def;  // Largest value which definitely occurs

	// Transient state
	vec<int> first_change;
	vec<int> limit_change;
};

void value_precede_seq(vec<IntVar*>& xs) {
	vec<IntVar*> nxs;
	std::unordered_set<IntVar*> set;
	for (size_t i = 0; i < xs.size(); ++i) {
		if (set.find(xs[i]) != set.end()) {
			continue;  // Same variable appears earlier in the same chain
		}
		nxs.push(xs[i]);
		set.insert(xs[i]);
	}
	// new seq_precede_chain(xs);
	new seq_precede_inc(nxs);
}

void value_precede_int(int s, int t, vec<IntVar*>& xs) { new value_precede(s, t, xs); }
