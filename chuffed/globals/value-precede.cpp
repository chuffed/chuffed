#include <algorithm>
#include <climits>
#include <chuffed/core/propagator.h>

// Propagator for the value_precede constraint.
class value_precede : public Propagator {
  // The only propagation which occurs is:
  struct tag_t {
    tag_t(void) : si(0), ti(0), flag(0) { }
    tag_t(int _si, int _ti, bool _flag) : flag(_flag), si(_si), ti(_ti) { }

    unsigned flag : 1;
    unsigned si : 15;
    unsigned ti : 16;
  };
  tag_t s_tag(int si, int ti) { return tag_t(si, ti, 0); }
  tag_t t_tag(int ti) { return tag_t(0, ti, 1); }

  Clause* ex_s(int si, int ti) {
    Clause* r(Reason_new(ti+1));
    Lit* p(&((*r)[1]));
    for(int ii = 0; ii < si; ++ii, ++p)
      (*p) = xs[ii]->getLit(s, LR_EQ);
    for(int ii = si+1; ii < ti; ++ii, ++p)
      (*p) = xs[ii]->getLit(s, LR_EQ);
    (*p) = xs[ti]->getLit(t, LR_NE);
    return r;
  }

  Clause* ex_t(int ti) {
    Clause* r(Reason_new(ti+1));
    for(int ii = 0; ii < ti; ++ii) {
      assert(!xs[ii]->indomain(s));
      (*r)[ii+1] = xs[ii]->getLit(s, LR_EQ);
    }
    return r;
  }
public: 
  value_precede(int _s, int _t, vec<IntVar*>& vs)
    : s(_s), t(_t), satisfied(0) {
    // Find the first possible occurrence of s.
    int ii = 0;
    /*
    for(; ii < vs.size(); ii++) {
      if(vs[ii]->remValNotR(t)) {
        if(!vs[ii]->remVal(t)) TL_FAIL();
      }
      if(vs[ii]->indomain(s))
        break;
    }
    */

    // Now copy the remaining values.
    first_s = xs.size()+1;
    for(; ii < vs.size(); ii++) {
      IntVar* x(vs[ii]);
      if(x->isFixed() && x->getVal() == s)
        break;

      if(!x->indomain(s) && !x->indomain(t))
        continue;
      x->specialiseToEL();
      BoolView b(x->getLit(s, LR_EQ));
      // b.attach(this, (xs.size()<<1), EVENT_U);
      x->attach(this, (xs.size()<<1), EVENT_C);
      x->attach(this, (xs.size()<<1)|1, EVENT_F);
      xs.push(x);

      if(x->isFixed() && x->getVal() == t) {
        first_t = xs.size()-1;
        break;
      }
    }
    if(xs.size() < first_t) first_t = xs.size()+1;

    int si = 1;
    for(; si < vs.size(); ++si) {
      if(xs[si]->indomain(s))
        break;
    }
    second_s = si;
    if(first_t <= second_s) {
      if(!xs[first_s]->setVal(s))
        TL_FAIL();
      satisfied = true;
    }
  }

  Clause* explain(Lit p, int inf_id) {
    tag_t t(conv<tag_t, int>(inf_id));
    return t.flag ? ex_t(t.ti) : ex_s(t.si, t.ti);
  }

  bool propagate(void) {
    if(satisfied)
      return true;

    int sz = xs.size();
    int si = first_s;
    // Update the first occurrence
    for(; si < sz; ++si) {
      if(xs[si]->remValNotR(t)) {
        if(!xs[si]->remVal(t, Reason(prop_id, conv<int, tag_t>(t_tag(si)))))
          return false;
      }
      if(xs[si]->indomain(s))
        break;
    }
    if(si >= first_t) {
      Clause* r(ex_t(first_t));
      (*r)[0] = xs[first_t]->getLit(t, LR_NE);
      sat.confl = r;
      return false;
    }
    if(si > first_s) first_s = si;
    // If there's no t, stop.
    if(first_t >= sz) return true;
    // Now find the second occurrence
    ++si;
    if(si < second_s) si = second_s;
    for(; si < first_t; ++si) {
      if(xs[si]->indomain(s)) {
        second_s = si;
        goto val_prec_finished;
      }
    }
    // At this point, there's only one candidate.
    if(xs[first_s]->setValNotR(s)) {
      if(!xs[first_s]->setVal(s, Reason(prop_id, conv<int, tag_t>(s_tag(first_s, first_t)))))
        return false;
    }
    satisfied = true;
val_prec_finished:
    return true;
  }

	void wakeup(int ii, int c) {
    if(satisfied)
      return;
    int vi = ii>>1;
    if(ii&1) {
      if(vi < first_t && xs[vi]->getVal() == t) {
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
    Clause* r = Reason_new(xi+1); 
    
    // One of the predecessors must be (at least) k.
    for(int ii = 0; ii < xi; ++ii) {
      (*r)[ii+1] = xs[ii]->getLit(k, LR_GE);
    }
    return r;
  }

  // Need to construct a chain.
  Clause* ex_lb(int xi, int k) {
    vec<Lit> r; r.push();
    // Three components.
    // Why can't the frontier already be above k?
    for(int ii = 0; ii < xi; ii++) {
      r.push(xs[ii]->getLit(k, LR_GE));
    }
    // Why can't the frontier get higher afterwards?
    int l = k;
    int ii = xi+1;
    for(; xs[ii]->getMin() <= l; ++ii) {
      if(xs[ii]->indomain(l)) {
        ++l;
      } else {
        r.push(~xs[ii]->getLit(l, LR_EQ));
      }
    }
    r.push(~(xs[ii]->getLit(l, LR_LE)));
    return Reason_new(r);
  }

  struct tag_t {
    tag_t(void) : flag(0), x(0), k(0) { }
    tag_t(bool _flag, int _x, int _k)
      : flag(_flag), x(_x), k(_k) { }

	  unsigned flag : 1 ;
	  unsigned x : 15;
	  unsigned k : 16;
  };
  int lb_tag(int x, int k) {
    return conv<int, tag_t>(tag_t(0, x, k));
  }
  int ub_tag(int x, int k) {
    return conv<int, tag_t>(tag_t(1, x, k));
  }

  Clause* explain(Lit p, int inf_id) {
    tag_t t(conv<tag_t, int>(inf_id));
    if(t.flag) {
      // Upper bound  
      return ex_ub(t.x, t.k);
    } else {
      // Lower bound
      return ex_lb(t.x, t.k);
    }
  }
  
public:
	void wakeup(int ii, int c) {
    if(c & EVENT_L) {
      // Update limit values.
      int l = xs[ii]->getMin();
      while(l && limit[l] > ii) {
        limit[l] = ii;
        --l;
      }
    }
    pushInQueue();
  }

  seq_precede_chain(vec<IntVar*>& _xs)
    : xs(_xs), vmax(0), limit(xs.size(), xs.size()) {
    int sz = xs.size();
    priority = 3;
    int M = 0;
    int low_f = 0;
		for (int ii = 0; ii < sz; ii++) {
      xs[ii]->attach(this, ii, EVENT_C);
      if(xs[ii]->getMax() > M) M = xs[ii]->getMax();
      if(xs[ii]->getMin() > low_f) {
        // Iniitalize limits.
        int m = xs[ii]->getMin();
        for(; m > low_f; ++low_f) {
          limit.push(ii);
        }
      }
    }

    vmax = M;
    first.push(0);
    for(int ii = 1; ii <= vmax; ++ii) first.push(ii-1);
  }

  bool propagate(void) {
    // Forward pass; tighten upper bounds.
    int sz = xs.size();
    int ii = 0;
    int fval = 1;
    for(; ii < sz; ++ii) {
      if(xs[ii]->setMaxNotR(fval)) {
        if(!xs[ii]->setMax(fval, Reason(prop_id, ub_tag(ii, fval)))) {
          return false;
        }
      }
      if(xs[ii]->indomain(fval)) {
        first[fval] = ii;   
        ++fval;
        if(fval == vmax)
          goto forward_done;
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
    for(; lval > 0 && limit[lval] >= sz; --lval) continue;
    if(!lval) return true;

    // Now, just walk back through the remaining values.
    for(int ii = limit[lval]; ii >= 0; --ii) {
      if(xs[ii]->indomain(lval-1)) {
        assert(first[lval-1] <= ii);
        if(first[lval-1] == ii) {
            if(xs[ii]->setMinNotR(lval-1)) {
            if(!xs[ii]->setMin(lval-1, Reason(prop_id, lb_tag(ii, lval-1))))
              return false;
            }
        }
        --lval;
      } else {
        if(xs[ii]->getMin() > lval)
          lval = xs[ii]->getMin();
      }
    }
    return true;
  }

	// Parameters
  vec<IntVar*> xs;

  // Persistent state.
  Tint vmax;

  // Transient state
  vec<int> first; // First occurrence of each ordered value
  vec<Tint> limit; // The latest point at which we must have achieved k.
};

void value_precede_seq(vec<IntVar*>& xs) {
  new seq_precede_chain(xs);
}

void value_precede_int(int s, int t, vec<IntVar*>& xs) {
  new value_precede(s, t, xs);
}
