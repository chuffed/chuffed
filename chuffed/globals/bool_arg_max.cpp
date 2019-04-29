#include <chuffed/core/propagator.h>

#include <iostream>

class BoolArgMax : public Propagator {
public:
  int const sz;
  BoolView * const x;
  IntView<> const y;
  int offset;
  BoolArgMax(vec<BoolView> _x, int _offset, IntView<> _y)  :
    sz(_x.size()), x(_x.release()), y(_y), offset(_offset) {
    priority = 1;
    for (int i = 0; i < sz; i++) x[i].attach(this, i, EVENT_LU);
    y.attach(this, sz, EVENT_C);
  }

  bool propagate() {
    // l = index of first x that can be true
    // y >= l because not x[i] forall i<l
    // u = index of first x that must be true
    // y <= u because x[u]
    
    int ol = y.getMin();
    for (int i=0; i<ol-offset; i++) {
      if (x[i].setValNotR(false)) {
        Clause *r = NULL;
        if (so.lazy) {
          r = Reason_new(2);
          (*r)[1] = y.getFMinLit(ol);
        }
        if (!x[i].setVal(false,r)) return false;
      }
    }
    
    if (y.isFixed()) {
      int yl = y.getVal()-offset;
      if (x[yl].setValNotR(true)) {
        Clause *r = NULL;
        if (so.lazy) {
          r = Reason_new(2);
          (*r)[1] = y.getValLit();
        }
        if (!x[yl].setVal(true,r)) return false;
      }
    }
    
    int l = sz;
    int u = 0;
    
    vec<int> toFix;
    for (typename IntView<>::iterator yi = y.begin(); yi != y.end(); ++yi) {
      int i = *yi - offset;
      if (l==sz && (!x[i].isFixed() || x[i].isTrue())) {
        l = i;
      }
      if (x[i].isFixed() && x[i].isFalse()) {
        if (y.remValNotR(i+offset)) {
          toFix.push(i);
        }
      }
      u = i;
      if (x[i].isFixed() && x[i].isTrue()) {
        break;
      }
    }
    for (int i=0; i<toFix.size(); i++) {
      Clause *r = NULL;
      if (so.lazy) {
        r = Reason_new(2);
        (*r)[1] = x[toFix[i]];
      }
      if (!y.remVal(toFix[i]+offset, r)) return false;
    }
    
    if (y.setMinNotR(l+offset)) {
      Clause *r = NULL;
      if (so.lazy) {
        r = Reason_new(l+1);
        for (int i = 0; i < l; i++) (*r)[i+1] = x[i];
      }
      if (!y.setMin(l+offset, r)) return false;
    }
    if (y.setMaxNotR(u+offset)) {
      Clause *r = NULL;
      if (so.lazy) {
        r = Reason_new(2);
        (*r)[1] = ~x[u];
      }
      if (!y.setMax(u+offset, r)) return false;
    }
  
    if (y.isFixed()) {
      int yl = y.getVal()-offset;
      if (x[yl].setValNotR(true)) {
        Clause *r = NULL;
        if (so.lazy) {
          r = Reason_new(2);
          (*r)[1] = y.getValLit();
        }
        if (!x[yl].setVal(true,r)) return false;
      }
    }
    int nl = y.getMin();
    for (int i=ol-offset; i<nl-offset; i++) {
      if (x[i].setValNotR(false)) {
        Clause *r = NULL;
        if (so.lazy) {
          r = Reason_new(2);
          (*r)[1] = y.getFMinLit(nl);
        }
        if (!x[i].setVal(false,r)) return false;
      }
    }
    
    
    return true;
  }

};

void bool_arg_max(vec<BoolView>& x, int offset, IntVar* y) {
  vec<BoolView> w;
  for (int i = 0; i < x.size(); i++) w.push(BoolView(x[i]));
  new BoolArgMax(w, offset, IntView<>(y));
}
