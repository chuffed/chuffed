#include <map>
#include <chuffed/core/propagator.h>

// y = a[x-offset]

void array_bool_element(IntVar* _x, vec<bool>& a, BoolView y, int offset)	{
	_x->specialiseToEL();
	IntView<4> x(_x, 1, -offset);
	for (int i = 0; i < a.size(); i++) {
		sat.addClause(y = a[i], x != i);
	}
	// Add clause [y != x[i]] \/ [x = i_1] \/ ... \/ [x = i_m]
	vec<Lit> ps1;
	vec<Lit> ps2;
	ps1.push(y);
	ps2.push(~y);
	for (int i = 0; i < a.size(); i++) {
		if (a[i]) ps2.push(x = i);
		else      ps1.push(x = i);
	}
	sat.addClause(ps1);
	sat.addClause(ps2);
}

//-----

// y = a[x-offset]

void array_int_element(IntVar* _x, vec<int>& a, IntVar* _y, int offset) {
 	TL_SET(_x, setMin, offset);
	TL_SET(_x, setMax, a.size()-1+offset);

	vec<int> z;
	for (int i = _x->getMin()-offset; i <= _x->getMax()-offset; i++) {
		if (!_x->indomain(i+offset)) continue;
		if (!_y->indomain(a[i])) continue;
		z.push(a[i]);
	}

	_y->specialiseToSL(z);
	_x->specialiseToEL();

	IntView<0> y(_y);
	IntView<4> x(_x, 1, -offset);

	for (int i = 0; i < a.size(); i++) {
		sat.addClause(y = a[i], x != i);
	}

	std::map<int,int> val_to_pss;

	// Add clause [y != a[i]] \/ [x = i_1] \/ ... \/ [x = i_m]
	vec<vec<Lit> > pss;
	for (int i = 0; i < a.size(); i++) {
		if (!y.indomain(a[i])) continue;
		int index = -1;
		std::map<int,int>::iterator it = val_to_pss.find(a[i]);
		if (it != val_to_pss.end()) {
			index = it->second;
		} else {
			index = pss.size();
			pss.push();
			pss[index].push(y != a[i]);
			val_to_pss.insert(std::pair<int,int>(a[i], index));
		}
		if (x.indomain(i)) pss[index].push(x = i);
	}
	for (int i = 0; i < pss.size(); i++) {
		sat.addClause(pss[i]);
	}
}


//-----

// y = a[x-offset]

void array_var_bool_element(IntVar* _x, vec<BoolView>& a, BoolView y, int offset) {
	_x->specialiseToEL();
	IntView<4> x(_x, 1, -offset);
	vec<Lit> ps1(a.size()+1);
	vec<Lit> ps2(a.size()+1);
	// Add clause !y \/ c_1 \/ ... \/ c_n
	// Add clause y \/ d_1 \/ ... \/ d_n
	ps1[0] = ~y;
	ps2[0] = y;
	for (int i = 0; i < a.size(); i++) {
		BoolView c_i(Lit(sat.newVar(),1));
		BoolView d_i(Lit(sat.newVar(),1));
		sat.addClause(~c_i, x = i);
		sat.addClause(~c_i, a[i]);
		sat.addClause(~d_i, x = i);
		sat.addClause(~d_i, ~a[i]);
		vec<Lit> ps3(3), ps4(3);
		ps3[0] = y; ps3[1] = ~a[i]; ps3[2] = (x != i);
		sat.addClause(ps3);
		ps4[0] = ~y; ps4[1] = a[i]; ps4[2] = (x != i);
		sat.addClause(ps4);
		ps1[i+1] = c_i;
		ps2[i+1] = d_i;
	}
	sat.addClause(ps1);
	sat.addClause(ps2);
}

//-----

// y = a[x]

template <int U = 0, int V = 0, int W = 0>
class IntElemBoundsImp : public Propagator {
  BoolView b;
	IntView<U> const y;
	IntView<V> const x;
	vec<IntView<W> > a;

	// persistent state

  Tchar is_fixed;
	Tint min_support;
	Tint max_support;
	Tint fixed_index;

	// intermediate state

	bool no_min_support;
	bool no_max_support;

public:

	IntElemBoundsImp(BoolView _b, IntView<U> _y, IntView<V> _x, vec<IntView<W> >& _a) :
		b(_b), y(_y), x(_x), a(_a), is_fixed(false), min_support(-1), max_support(-1), fixed_index(-1),
		no_min_support(false), no_max_support(false) {
		for (int i = 0; i < a.size(); i++) a[i].attach(this, i, EVENT_LU);
		y.attach(this, a.size(), EVENT_LU);
		x.attach(this, a.size()+1, EVENT_C);
    b.attach(this, a.size()+2, EVENT_F);
	}

	void wakeup(int i, int c) {
    if (i == a.size()+2 && (c & EVENT_F)) {
      if (!b.getVal()) {
        return;
      }
    }
		if (i == a.size()+1 && (c & EVENT_F)) {
      is_fixed = true;
			fixed_index = x.getVal();
			no_min_support = no_max_support = false;
			pushInQueue();
		} else if (is_fixed) {
			if (i == a.size() || i == fixed_index) pushInQueue();
		} else {
			if (i < a.size()) {
				if (i == min_support && a[i].getMin() > y.getMin()) no_min_support = true;
				if (i == max_support && a[i].getMax() < y.getMax()) no_max_support = true;
				pushInQueue();
			} else if (i == a.size()+1) {
				if (!x.indomain(min_support)) { no_min_support = true; pushInQueue(); }
				if (!x.indomain(max_support)) { no_max_support = true; pushInQueue(); }
			} else pushInQueue();
		}
	}

	bool propagate() {
    if (b.isFixed() && b.isFalse()) {
      satisfied = true;
      return true;
    }

    // x is out of bounds
    if (is_fixed && (fixed_index < 0 || fixed_index >= a.size())) {
      return b.setVal(false, x.getValLit());
    }

		// y = a[fixed_index]
		if (is_fixed) {
			assert(x.getVal() == fixed_index);
			IntView<W>& f = a[fixed_index];
      if (b.isFixed()) {
        setDom(y, setMin, f.getMin(), Reason_new({b.getValLit(), f.getMinLit(), x.getValLit()}));
        setDom(f, setMin, y.getMin(), Reason_new({b.getValLit(), y.getMinLit(), x.getValLit()}));
        setDom(y, setMax, f.getMax(), Reason_new({b.getValLit(), f.getMaxLit(), x.getValLit()}));
        setDom(f, setMax, y.getMax(), Reason_new({b.getValLit(), y.getMaxLit(), x.getValLit()}));
        if (y.isFixed() && f.isFixed()) satisfied = true;
      } else if (f.getMin() > y.getMax()) {
        Clause* r = Reason_new({x.getValLit(), f.getMinLit(), y.getMaxLit()});
        return b.setVal(false, r);
      } else if (f.getMax() < y.getMin()) {
        Clause* r = Reason_new({x.getValLit(), f.getMaxLit(), y.getMinLit()});
        return b.setVal(false, r);
      }
      return true;
		}

    if (b.isFixed()) {
      for (int i = 0; i < a.size(); i++) {
        if (!x.indomain(i)) continue;
        if (y.getMax() < a[i].getMin()) {
          Clause* r = Reason_new({b.getValLit(), a[i].getMinLit(), y.getMaxLit()});
          setDom(x, remVal, i, r);
        }
        if (y.getMin() > a[i].getMax()) {
          Clause* r = Reason_new({b.getValLit(), a[i].getMaxLit(), y.getMinLit()});
          setDom(x, remVal, i, r);
        }
      }
    } else {
      std::vector<Lit> expl;
      bool push_min = false;
      bool push_max = false;
      int i = 0;
      while (i <= a.size()) {
        if (!x.indomain(i)) {
          expl.push_back(x.getLit(i, 1));
        } else if (y.getMax() < a[i].getMin()) {
          if (!push_max) {
            expl.push_back(y.getMaxLit());
            push_max = true;
          }
          expl.push_back(a[i].getMinLit());
        } else if (y.getMin() > a[i].getMax()) {
          if (!push_min) {
            expl.push_back(y.getMinLit());
            push_min = true;
          }
          expl.push_back(a[i].getMaxLit());
        } else {
          break;
        }
        i++;
      }
      if (i > x.getMax()) {
        Clause* r = Reason_new(expl);
        return b.setVal(false, r);
      }
    }

		if (no_min_support) {
			int64_t old_m = y.getMin();
			int64_t new_m = INT64_MAX;
			int best = -1;
			for (int i = 0; i < a.size(); i++) {
				if (!x.indomain(i)) continue;
				int64_t cur_m = a[i].getMin();
				if (cur_m < new_m) {
					best = i;
					new_m = cur_m;
					if (cur_m <= old_m) break;
				}
			}
			min_support = best;
			if (y.setMinNotR(new_m)) {
        auto reason = [&] {
          Clause *r = NULL;
          if (so.lazy) {
            r = Reason_new(a.size()+2);
            // Finesse lower bounds
            for (int i = 0; i < a.size(); i++) {
              (*r)[i+2] = x.indomain(i) ? a[i].getFMinLit(new_m) : x.getLit(i, 1);
            }
          }
          return r;
        };
        if (b.isFixed()) {
          Clause* r = reason();
          (*r)[1] = b.getValLit();
          if (!y.setMin(new_m, r)) {
            return false;
          }
        } else if (y.getMax() < new_m) {
          Clause* r = reason();
          (*r)[1] = y.getMaxLit();
          return b.setVal(false, r);
        }
			}
			no_min_support = false;
		}

		if (no_max_support) {
			int64_t old_m = y.getMax();
			int64_t new_m = INT_MIN;
			int best = -1;
			for (int i = 0; i < a.size(); i++) {
				if (!x.indomain(i)) continue;
				int64_t cur_m = a[i].getMax();
				if (cur_m > new_m) {
					best = i;
					new_m = cur_m;
					if (cur_m >= old_m) break;
				}
			}
			max_support = best;
			if (y.setMaxNotR(new_m)) {
        auto reason = [&] {
          Clause *r = NULL;
          if (so.lazy) {
            r = Reason_new(a.size()+2);
            // Finesse upper bounds
            for (int i = 0; i < a.size(); i++) {
              (*r)[i+2] = x.indomain(i) ? a[i].getFMaxLit(new_m) : x.getLit(i, 1);
            }
          }
          return r;
        };
        if (b.isFixed()) {
          Clause* r = reason();
          (*r)[1] = b.getValLit();
          if (!y.setMax(new_m, r)) {
            return false;
          }
        } else if (y.getMin() > new_m) {
          Clause* r = reason();
          (*r)[1] = y.getMinLit();
          return b.setVal(false, r);
        }
			}
			no_max_support = false;
		}

		return true;
	}

	void clearPropState() {
		in_queue = false;
		no_min_support = false;
		no_max_support = false;
  }

	int checkSatisfied() {
		if (satisfied) return 1;
    if (b.isFixed() && !b.getVal()) {
			satisfied = true;
    } else if (b.isFixed() && x.isFixed() && y.isFixed() && a[static_cast<int>(x.getVal())].isFixed()) {
			satisfied = true;
		}
		return 3;
	}

};

template <int U = 0, int V = 0, int W = 0>
class IntElemBounds : public Propagator {
	IntView<U> const y;
	IntView<V> const x;
	vec<IntView<W> > a;

	// persistent state

	Tint min_support;
	Tint max_support;
	Tint fixed_index;

	// intermediate state

	bool no_min_support;
	bool no_max_support;

public:

	IntElemBounds(IntView<U> _y, IntView<V> _x, vec<IntView<W> >& _a) :
		y(_y), x(_x), a(_a), min_support(-1), max_support(-1), fixed_index(-1),
		no_min_support(false), no_max_support(false) {
		for (int i = 0; i < a.size(); i++) a[i].attach(this, i, EVENT_LU);
		y.attach(this, a.size(), EVENT_LU);
		x.attach(this, a.size()+1, EVENT_C);
	}

	void wakeup(int i, int c) {
		if (i == a.size()+1 && (c & EVENT_F)) {
			fixed_index = x.getVal();
			no_min_support = no_max_support = false;
			pushInQueue();
		}
		if (fixed_index >= 0) {
			if (i == a.size() || i == fixed_index) pushInQueue();
		} else {
			if (i < a.size()) {
				if (i == min_support && a[i].getMin() > y.getMin()) no_min_support = true;
				if (i == max_support && a[i].getMax() < y.getMax()) no_max_support = true;
				pushInQueue();
			} else if (i == a.size()+1) {
				if (!x.indomain(min_support)) { no_min_support = true; pushInQueue(); }
				if (!x.indomain(max_support)) { no_max_support = true; pushInQueue(); }
			} else pushInQueue();
		}
	}

	bool propagate() {

		// y = a[fixed_index]
		if (fixed_index >= 0) {
			assert(x.getVal() == fixed_index);
			IntView<W>& f = a[fixed_index];
			setDom(y, setMin, f.getMin(), f.getMinLit(), x.getValLit());
			setDom(f, setMin, y.getMin(), y.getMinLit(), x.getValLit());
			setDom(y, setMax, f.getMax(), f.getMaxLit(), x.getValLit());
			setDom(f, setMax, y.getMax(), y.getMaxLit(), x.getValLit());
			if (y.isFixed() && f.isFixed()) satisfied = true;
			return true;
		}

		for (int i = 0; i < a.size(); i++) {
			if (!x.indomain(i)) continue;
			if (y.getMax() < a[i].getMin()) setDom(x, remVal, i, y.getMaxLit(), a[i].getMinLit());
			if (y.getMin() > a[i].getMax()) setDom(x, remVal, i, y.getMinLit(), a[i].getMaxLit());
		}

		if (no_min_support) {
			int64_t old_m = y.getMin();
			int64_t new_m = INT64_MAX;
			int best = -1;
			for (int i = 0; i < a.size(); i++) {
				if (!x.indomain(i)) continue;
				int64_t cur_m = a[i].getMin();
				if (cur_m < new_m) {
					best = i;
					new_m = cur_m;
					if (cur_m <= old_m) break;
				}
			}
			min_support = best;
			if (y.setMinNotR(new_m)) {
				Clause *r = NULL;
				if (so.lazy) {
					r = Reason_new(a.size()+1);
					// Finesse lower bounds
					for (int i = 0; i < a.size(); i++) {
						(*r)[i+1] = x.indomain(i) ? a[i].getFMinLit(new_m) : x.getLit(i, 1);
					}
				}
				if (!y.setMin(new_m, r)) return false;
			}
			no_min_support = false;
		}

		if (no_max_support) {
			int64_t old_m = y.getMax();
			int64_t new_m = INT_MIN;
			int best = -1;
			for (int i = 0; i < a.size(); i++) {
				if (!x.indomain(i)) continue;
				int64_t cur_m = a[i].getMax();
				if (cur_m > new_m) {
					best = i;
					new_m = cur_m;
					if (cur_m >= old_m) break;
				}
			}
			max_support = best;
			if (y.setMaxNotR(new_m)) {
				Clause *r = NULL;
				if (so.lazy) {
					r = Reason_new(a.size()+1);
					// Finesse upper bounds
					for (int i = 0; i < a.size(); i++) {
						(*r)[i+1] = x.indomain(i) ? a[i].getFMaxLit(new_m) : x.getLit(i, 1);
					}
				}
				if (!y.setMax(new_m, r)) return false;
			}
			no_max_support = false;
		}

		return true;
	}

	void clearPropState() {
		in_queue = false;
		no_min_support = false;
		no_max_support = false;
	}

	int checkSatisfied() {
		if (satisfied) return 1;
		if (x.isFixed() && y.isFixed() && a[static_cast<int>(x.getVal())].isFixed()) {
			satisfied = true;
		}
		return 3;
	}

};


template <int U = 0, int V = 0, int W = 0>
class IntElemDomain : public Propagator {
	IntView<U> const y;
	IntView<V> const x;
	vec<IntView<W> > a;

	// persistent state

	Tint *num_support;
	int **support;

	// intermediate state

	int *temp_sup;

public:

	IntElemDomain(IntView<U> _y, IntView<V> _x, vec<IntView<W> >& _a) :
		y(_y), x(_x), a(_a) {
		num_support = new Tint[y.getMax()-y.getMin()+1] - y.getMin();
		support = new int*[y.getMax()-y.getMin()+1] - y.getMin();
		temp_sup = new int[x.getMax()-x.getMin()+1];

		vec<int> temp;
		for (int v = y.getMin(); v <= y.getMax(); v++) {
			temp.clear();
			if (y.indomain(v)) {
				for (int i = x.getMin(); i <= x.getMax(); i++) {
					if (x.indomain(i) && a[i].indomain(v)) temp.push(i);
				}
			}
			num_support[v] = temp.size();
			support[v] = new int[temp.size()];
			for (int i = 0; i < temp.size(); i++) {
				support[v][i] = temp[i];
			}
		}

		for (int i = 0; i < a.size(); i++) a[i].attach(this, i, EVENT_C);
		y.attach(this, a.size(), EVENT_C);
		x.attach(this, a.size()+1, EVENT_C);
	}


	bool propagate() {

		// propagate holes in y
		for (int v = y.getMin(); v <= y.getMax(); v++) {
			if (!y.indomain(v)) continue;
			int *s = support[v];
			int f = 0;
			if (num_support[v] > 0) {
				if (x.indomain(s[0]) && a[s[0]].indomain(v)) continue;
				while (!(x.indomain(s[f]) && a[s[f]].indomain(v)) && ++f < num_support[v]);
			}
			if (f == num_support[v]) {
				// v has no support, remove from y
				Clause* r = NULL;
				if (so.lazy) {
					r = Reason_new(x.getMax() + 4 - x.getMin());
					(*r)[1] = x.getMinLit();
					(*r)[2] = x.getMaxLit();
					for (int i = x.getMin(); i <= x.getMax(); i++) {
						//(*r)[3 + i - x.getMin()] = x.indomain(i) ? ~a[i].getLit(v, 0) : ~x.getLit(i, 0);
						int reasonIndex = 3 + i - x.getMin();
						if(x.indomain(i))
						{
							Lit l = ~a[i].getLit(v, 0);
							(*r)[reasonIndex] = l;
						}
						else
						{
							Lit l = ~x.getLit(i, 0);
						 	(*r)[reasonIndex] = l;
						}
					}
				}
				if (!y.remVal(v, r)) return false;
			} else {
				// shift bad supports to back
				for (int i = 0; i < f; i++) temp_sup[i] = s[i];
				for (int i = f; i < num_support[v]; i++) {
					s[i-f] = s[i];
				}
				s += num_support[v] - f;
				for (int i = 0; i < f; i++) s[i] = temp_sup[i];
				num_support[v] -= f;
			}
		}

		// propagate holes in x
		// just ignore

		// propagate holes in a_i
		if (x.isFixed()) {
			int v = x.getVal();
			IntView<W>& f = a[v];
			setDom(y, setMin, f.getMin(), f.getMinLit(), x.getValLit());
			setDom(f, setMin, y.getMin(), y.getMinLit(), x.getValLit());
			setDom(y, setMax, f.getMax(), f.getMaxLit(), x.getValLit());
			setDom(f, setMax, y.getMax(), y.getMaxLit(), x.getValLit());
			for (typename IntView<W>::iterator i = a[v].begin(); i != a[v].end(); ) {
				int w = *i++;
				if (!y.indomain(w) && !a[v].remVal(w, so.lazy ? Reason(~y.getLit(w, 0), ~x.getLit(v, 1)) : Reason()))
					return false;
			}
		}

		return true;
	}

};


// y = a[x-offset]
// bounds consistent version

void array_var_int_element_bound(IntVar* x, vec<IntVar*>& a, IntVar* y, int offset) {
	x->specialiseToEL();
	vec<IntView<> > w;
	for (int i = 0; i < a.size(); i++) w.push(IntView<>(a[i]));
	if (offset) new IntElemBounds<0,4,0>(IntView<>(y), IntView<4>(x,1,-offset), w);
	else        new IntElemBounds<0,0,0>(IntView<>(y), IntView<>(x), w);
}

void array_var_int_element_bound_imp(BoolView b, IntVar* x, vec<IntVar*>& a, IntVar* y, int offset) {
	x->specialiseToEL();
	vec<IntView<> > w;
	for (int i = 0; i < a.size(); i++) w.push(IntView<>(a[i]));
	if (offset) new IntElemBoundsImp<0,4,0>(b, IntView<>(y), IntView<4>(x,1,-offset), w);
	else        new IntElemBoundsImp<0,0,0>(b, IntView<>(y), IntView<>(x), w);
}

// domain consistent version

void array_var_int_element_dom(IntVar* x, vec<IntVar*>& a, IntVar* y, int offset) {
	x->initVals();
	y->initVals();
	vec<IntView<> > w;
	for (int i = 0; i < a.size(); i++) {
		a[i]->initVals();
		w.push(IntView<>(a[i]));
	}
	if (offset) new IntElemDomain<0,4,0>(IntView<>(y), IntView<4>(x,1,-offset), w);
	else        new IntElemDomain<0,0,0>(IntView<>(y), IntView<>(x), w);
}
