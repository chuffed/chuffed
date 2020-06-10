#ifndef int_view_h
#define int_view_h

#include <cassert>
#include <chuffed/core/sat-types.h>
#include <chuffed/core/sat.h>

// y = (-1)a*x + b

// affine: type = 1*minus + 2*scale + 4*offset

template <int type = 0>
class IntView {
public:
	IntVar *var;
	int a;
	int b;

	IntView(IntVar *v = NULL, int _a = 1, int _b = 0) : var(v), a(_a), b(_b) {}

	template<int type2>
	IntView(const IntView<type2>& o) : var(o.var), a(o.a), b(o.b) {}

	void attach(Propagator *p, int pos, int eflags) const {
		var->attach(p, pos, getEvent(eflags));
	}

	int getType() {
		int t = 0;
		if (a < 0) { a = -a; t |= 1; }
		if (a > 1) t |= 2;
		if (b) t |= 4;
		return t;
	}

	IntVar* getVar() const { return var; }
	int getEvent(int e) const {
		return (type & 1) ? (e&9) + ((e&2)<<1) + ((e&4)>>1) : e;
	}

	bool isFixed() const { return var->isFixed(); }
	int64_t getMin() const {
		int64_t v = (type & 1) ? -var->getMax() : var->getMin();
		if (type & 2) v *= a;	if (type & 4) v += b;
		return v;
	}
	int64_t getMax() const {
		int64_t v = (type & 1) ? -var->getMin() : var->getMax();
		if (type & 2) v *= a;	if (type & 4) v += b;
		return v;
	}		
	int64_t getVal() const {
		int64_t v = (type & 1) ? -var->getVal() : var->getVal();
		if (type & 2) v *= a;	if (type & 4) v += b;
		return v;
	}
	int64_t getShadowVal() const {
		int64_t v = (type & 1) ? -var->getShadowVal() : var->getShadowVal();
		if (type & 2) v *= a; if (type & 4) v += b;
		return v;
	}
	bool indomain(int64_t v) const {	
		if (type & 4) v -= b;
		if (type & 2) {
			if (v%a) return false;
			v = v/a;
		}
		if (type & 1) v = -v;
		return var->indomain(v);
	}

	class iterator {
		const IntView* view;
		IntVar::iterator forward;
	public:
		iterator() {}
		iterator(const IntView* _view, IntVar::iterator _forward) : view(_view), forward(_forward) {}
		int operator *() const {
			int v;
			if (type & 1) {
				IntVar::iterator temp = forward;
				v = -*--temp;
			}
			else
				v = *forward;
			if (type & 2)
				v *= view->a;
			if (type & 4)
				v += view->b;
			return v;
		}
		iterator& operator ++() {
			if (type & 1)
				--forward;
			else
				++forward;
			return *this;
		}
		iterator operator ++(int dummy) {
			iterator temp = *this;
			++*this;
			return temp;
		}
		iterator& operator --() {
			if (type & 1)
				++forward;
			else
				--forward;
			return *this;
		}
		iterator operator --(int dummy) {
			iterator temp = *this;
			--*this;
			return temp;
		}
		bool operator ==(const iterator& rhs) const {
			assert(view == rhs.view);
			return (forward == rhs.forward);
		}
		bool operator !=(const iterator& rhs) const {
			assert(view == rhs.view);
			return (forward != rhs.forward);
		}
	};
	typedef iterator const_iterator;
	iterator begin() const { return iterator(this, (type & 1) ? var->end() : var->begin()); }
	iterator end() const { return iterator(this, (type & 1) ? var->begin() : var->end()); }

	class reverse_iterator {
		iterator forward;
	public:
		reverse_iterator() {}
		reverse_iterator(iterator _forward) : forward(_forward) {}
		int operator *() const {
			iterator temp = forward;
			return *--temp;
		}
		reverse_iterator& operator ++() {
			--forward;
			return *this;
		}
		reverse_iterator operator ++(int dummy) {
			reverse_iterator temp = *this;
			++*this;
			return temp;
		}
		reverse_iterator& operator --() {
			++forward;
			return *this;
		}
		reverse_iterator operator --(int dummy) {
			reverse_iterator temp = *this;
			--*this;
			return temp;
		}
		iterator base() const {
			return forward;
		}
		bool operator ==(const reverse_iterator& rhs) const {
			return (forward == rhs.forward);
		}
		bool operator !=(const reverse_iterator& rhs) const {
			return (forward != rhs.forward);
		}
	};
	typedef reverse_iterator const_reverse_iterator;
	reverse_iterator rbegin() const { return reverse_iterator(end()); }
	reverse_iterator rend() const { return reverse_iterator(begin()); }

	int size() const { return var->size(); }

	bool setMinNotR(int64_t m) const { return m > getMin(); }
	bool setMaxNotR(int64_t m) const { return m < getMax(); }
	bool setValNotR(int64_t v) const { return !isFixed() || v != getVal(); }
	bool remValNotR(int64_t v) const {	return indomain(v); }

	Lit getMinLit() const {
		return (type & 1) ? var->getMaxLit() : var->getMinLit();
	}
	Lit getMaxLit() const {
		return (type & 1) ? var->getMinLit() : var->getMaxLit();
	}
	Lit getValLit() const { return var->getValLit(); }

	Lit getFMinLit(int64_t v) const {
		if (type & 4) v -= b;
		if (type & 2) v = v/a - (v%a < 0);
		if (type & 1) return var->getFMaxLit(-v);
		else          return var->getFMinLit(v);
	}

	Lit getFMaxLit(int64_t v) const {
		if (type & 4) v -= b;
		if (type & 2) v = v/a + (v%a > 0);
		if (type & 1) return var->getFMinLit(-v);
		else          return var->getFMaxLit(v);
	}

	// y = 2*x
	// [y <= 3] = [x <= 1]
	// [y <= -5] = [x <= -3]
	// y = -2*x
	// [y <= 3] = [x >= -1] = ![x <= -2]
	// [y <= -5] = [x >= 3] = ![x <= 2]
	Lit getLit(int64_t v, int t) const {
		if (type & 4) v -= b;
		if (type & 2) {
			int k = v%a;
			v = v/a;
			if (k) {
				if (t == 0) NEVER;
				if (t == 1) return lit_False;
				if (t == 2 && k > 0) v++;
				if (t == 3 && k < 0) v--;
			}
		}
		if (type & 1) {
			v = -v;
			if (t >= 2) return var->getLit(v, 5-t);
		}
		return var->getLit(v, t);
	}


	// Set ![y <= m-1]
	// y = 2*x
	// [y >= 4] = ![y <= 3] = ![x <= 1] = [x >= 2]
	// [y >= 3] = ![y <= 2] = ![x <= 1] = [x >= 2]
	// y = -2*x
	// [y >= 4] = ![y <= 3] = ![x >= -1] = [x <= -2]
	// [y >= 3] = ![y <= 2] = ![x >= -1] = [x <= -2]
	// [y >= -4] = ![y <= -5] = ![x >= 3] = [x <= 2]
	bool setMin(int64_t v, Reason r = NULL, bool channel = true) const {
		v--;
		if (type & 4) v -= b;
		if (type & 2) v = v/a - (v%a < 0);
		if (type & 1) return var->setMax(-v-1, r, channel);
		else          return var->setMin(v+1, r, channel);
	}
	// Set [y <= m]
	// y = 2*x
	// [y <= 4] = [x <= 2]
	// [y <= 3] = [x <= 1]
	// y = -2*x
	// [y <= 3] = [x >= -1]
	// [y <= -4] = [x >= 2]
	// [y <= -5] = [x >= 3]
	bool setMax(int64_t v, Reason r = NULL, bool channel = true) const {
		if (type & 4) v -= b;
		if (type & 2) v = v/a - (v%a < 0);
		if (type & 1) return var->setMin(-v, r, channel);
		else          return var->setMax(v, r, channel);
	}
	bool setVal(int64_t v, Reason r = NULL, bool channel = true) const {
		if (type & 4) v -= b;
		if (type & 2) {
			if (v%a) { sat.cEnqueue(lit_False, r); return false; }
			v = v/a;
		}
		if (type & 1) v = -v;
		return var->setVal(v, r, channel);
	}
	bool remVal(int64_t v, Reason r = NULL, bool channel = true) const {
		if (type & 4) v -= b;
		if (type & 2) {
			if (v%a) return true;
			v = v/a;
		}
		if (type & 1) v = -v;
		return var->remVal(v, r, channel);
	}

	Lit operator =  (int val) const { return getLit(val, 1); }
	Lit operator != (int val) const { return getLit(val, 0); }

};

const IntView<> iv_null;

#endif
