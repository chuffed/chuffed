//#include <stdio.h>
#include <chuffed/core/propagator.h>

// AllDiff for mapping n vars to n values
// x[i] != x[j] for all i, j

template <int U = 0>
class AllDiffValue : public Propagator, public Checker {
public:
	int const sz;
	IntView<U> * const x;
	int const range;

	// Intermediate state
	vec<int> new_fixed;

	AllDiffValue(vec<IntView<U> > _x, int _range) : sz(_x.size()), x(_x.release()), range(_range)
	{
		priority = 2; 
		new_fixed.reserve(sz);
		for (int i = 0; i < sz; i++) x[i].attach(this, i, EVENT_F);
		if (range < sz) TL_FAIL();
		if (range == sz && so.alldiff_cheat) {
			for (int i = 0; i < sz; i++) x[i].getVar()->specialiseToEL();
			// Add clauses [a_1 = i] \/ [a_2 = i] \/ ... \/ [a_n = i]
			for (int i = 0; i < range; i++) {
				vec<Lit> ps(sz);
				for (int j = 0; j < sz; j++) ps[j] = x[j].getLit(i, 1);
				sat.addClause(ps);
			}
		}
	}

	void wakeup(int i, int c) {		assert(x[i].isFixed());
		new_fixed.push(i);
		pushInQueue();
	}

	bool propagate() {
 //fprintf(stderr, "AllDiffValue::propagate()\n");
		for (int i = 0; i < new_fixed.size(); i++) {
			int a = new_fixed[i];
			int b = x[a].getVal();
 //fprintf(stderr, "var %d == %d:\n", a, b);
			Clause* r = NULL;
			if (so.lazy) {
				r = Reason_new(2);
				(*r)[1] = x[a].getValLit();
			}
			for (int j = 0; j < sz; j++) {
				if (j == a) continue;
				if (x[j].remValNotR(b)) {
 //fprintf(stderr, "  var %d != %d\n", j, b);
					if (!x[j].remVal(b, r)) {
 //fprintf(stderr, "  failure\n");
						return false;
					}
				}
			}
		}

		return true;
	}

	void clearPropState() {
		in_queue = false;
		new_fixed.clear();
	}

	bool check() {
	  if (sz == 0) return true;
	  bool* taken = new bool[sz];
	  //		bool taken[sz];
		for (int i = 0; i < sz; i++) taken[i] = false;
		for (int i = 0; i < sz; i++) {
		  if (taken[x[i].getShadowVal()]) { delete[] taken; return false; }
			taken[x[i].getShadowVal()] = true;
		}
	  delete[] taken;
		return true;
	}

};

struct interval {
	int next;		// for explanations, record contents of bucket
	int min, max;		// start, end of interval
	int minrank, maxrank;	// rank of min & max in bounds[] of an adcsp
};

void pathset(int *t, int start, int end, int to)
{
	int k, l;
	for (l=start; (k=l) != end; t[k]=to)
		l = t[k];
}

int pathmin(int *t, int i)
{
	for (; t[i] < i; i=t[i])
		;
	return i;
}

int pathmax(int *t, int i)
{
	for (; t[i] > i; i=t[i])
		;
	return i;
}

template <int U = 0>
class AllDiffBounds : public Propagator, public Checker {
public:
	int const sz;
	IntView<U> * const x;
	int const range;

	interval *iv;
	int *minsorted;
	int *maxsorted;

	int nb;
	int *bounds;
	int *t;
	int *d;
	int *h;
	int *bucket;

	AllDiffBounds(vec<IntView<U> > _x, int _range) : sz(_x.size()), x(_x.release()), range(_range) {
		priority = 4;
		iv = new interval[sz];
		minsorted = new int[sz];
		maxsorted = new int[sz];
		for (int i = 0; i < sz; i++) {
			minsorted[i] = i;
			maxsorted[i] = i;
			x[i].attach(this, i, EVENT_LU);
		}
		int n = 2 * sz + 2;
		bounds = new int[n];
		t = new int[n];
		d = new int[n];
		h = new int[n];
		bucket = new int[n];
	}

	void sortit()
	{
		int i,j,min,max,last;

		for (int i = sz - 1; i >= 0; --i) {
			int t = minsorted[i];
			iv[t].min = x[t].getMin();
			int j;
			for (j = i; j < sz - 1; ++j) {
				if (iv[t].min < iv[minsorted[j + 1]].min)
					break;
				minsorted[j] = minsorted[j + 1];
			}
			minsorted[j] = t;
		}
		for (int i = sz - 1; i >= 0; --i) {
			int t = maxsorted[i];
			iv[t].max = x[t].getMax() + 1;
			int j;
			for (j = i; j < sz - 1; ++j) {
				if (iv[t].max < iv[maxsorted[j + 1]].max)
					break;
				maxsorted[j] = maxsorted[j + 1];
			}
			maxsorted[j] = t;
		}

		min = iv[minsorted[0]].min;
		max = iv[maxsorted[0]].max;
		bounds[0] = last = min-2;
	
		for (i=j=nb=0;;) { // merge minsorted[] and maxsorted[] into bounds[]
			if (i<sz && min<=max) {	// make sure minsorted exhausted first
				if (min != last)
					bounds[++nb] = last = min;
				iv[minsorted[i]].minrank = nb;
				if (++i < sz)
					min = iv[minsorted[i]].min;
			} else {
				if (max != last)
					 bounds[++nb] = last = max;
				iv[maxsorted[j]].maxrank = nb;
				if (++j == sz) break;
				max = iv[maxsorted[j]].max;
			}
		}
		bounds[nb+1] = bounds[nb] + 2;
	}

	bool filterlower()
	{
		int i,j,w,z;

 //fprintf(stderr, "AllDiffBounds::filterlower()\n");
		for (i=1; i<=nb+1; i++) {
			d[i] = bounds[i] - bounds[t[i]=h[i]=i-1];
			bucket[i] = -1; // this could perhaps be avoided
		}
		for (i=0; i<sz; i++) { // visit intervals in increasing max order
			int minrank = iv[maxsorted[i]].minrank;
			int maxrank = iv[maxsorted[i]].maxrank;
 //fprintf(stderr, "var %d [%d, %d)\n", maxsorted[i], bounds[minrank], bounds[maxrank]);
			j = t[z = pathmax(t, minrank+1)];
			iv[maxsorted[i]].next = bucket[z];
			bucket[z] = maxsorted[i];
			if (--d[z] == 0)
				t[z = pathmax(t, t[z]=z+1)] = j;
			pathset(t, minrank+1, z, z); // path compression
			//if (d[z] < bounds[z]-bounds[maxrank]) return false; // no solution
			if (h[minrank] > minrank) {
				Clause* r = NULL;
				int hall_max = bounds[w = pathmax(h, h[minrank])];
				if (so.lazy) {
					int hall_min = bounds[minrank];
					// here both k and hall_min are decreasing, stop when k catches up
					for (int k = w; bounds[k] > hall_min; --k)
						for (int l = bucket[k]; l >= 0; l = iv[l].next)
							hall_min = std::min(hall_min, iv[l].min);
 //fprintf(stderr, "  in hall [%d, %d):\n", hall_min, hall_max);
					r = Reason_new(2 + (hall_max - hall_min) * 2);
					(*r)[1] = ~x[maxsorted[i]].getLit(hall_min, 2);
					int m = 2;
					for (int k = w; bounds[k] > hall_min; --k)
						for (int l = bucket[k]; l >= 0; l = iv[l].next) {
 //fprintf(stderr, "    var %d [%d, %d)\n", l, iv[l].min, iv[l].max);
							(*r)[m++] = ~x[l].getLit(hall_min, 2);
							(*r)[m++] = ~x[l].getLit(hall_max - 1, 3);
					}
					assert(m == 2 + (hall_max - hall_min) * 2);
				}
				if (!x[maxsorted[i]].setMin(hall_max, r)) {
 //fprintf(stderr, "  failure\n");
					return false;
				}
				iv[maxsorted[i]].min = hall_max;
				if (x[maxsorted[i]].getMin() > hall_max) {
 //fprintf(stderr, "  hole, var %d [%d, %d)\n", maxsorted[i], static_cast<int>(x[maxsorted[i]].getMin()), iv[maxsorted[i]].max);
					pushInQueue(); // hole in domain
				}
				pathset(h, minrank, w, w); // path compression

			}
			if (d[z] == bounds[z]-bounds[maxrank]) {
 //fprintf(stderr, "  new hall [%d, %d)\n", bounds[j], bounds[maxrank]);
				pathset(h, h[maxrank], j-1, maxrank); // mark hall interval
				h[maxrank] = j-1;
			}
		}
		return true;
	}

	int filterupper()
	{
		int i,j,w,z;

 //fprintf(stderr, "AllDiffBounds::filterupper()\n");
		for (i=0; i<=nb; i++) {
			d[i] = bounds[t[i]=h[i]=i+1] - bounds[i];
			bucket[i] = -1; // this could perhaps be avoided
		}
		for (i=sz; --i>=0; ) { // visit intervals in decreasing min order
			int maxrank = iv[minsorted[i]].maxrank;
			int minrank = iv[minsorted[i]].minrank;
 //fprintf(stderr, "var %d [%d, %d)\n", minsorted[i], bounds[minrank], bounds[maxrank]);
			j = t[z = pathmin(t, maxrank-1)];
			--d[z];
			iv[minsorted[i]].next = bucket[z];
			bucket[z] = minsorted[i];
			if (d[z] == 0)
				t[z = pathmin(t, t[z]=z-1)] = j;
			pathset(t, maxrank-1, z, z);
			//if (d[z] < bounds[minrank]-bounds[z]) return false; // no solution
			if (h[maxrank] < maxrank) {
				Clause* r = NULL;
				int hall_min = bounds[w = pathmin(h, h[maxrank])];
			if (so.lazy) {
					int hall_max = bounds[maxrank];
					// here both k and hall_max are increasing, stop when k catches up
					for (int k = w; bounds[k] < hall_max; ++k)
						for (int l = bucket[k]; l >= 0; l = iv[l].next)
							hall_max = std::max(hall_max, iv[l].max);
 //fprintf(stderr, "  in hall [%d, %d):\n", hall_min, hall_max);
					r = Reason_new(2 + (hall_max - hall_min) * 2);
					(*r)[1] = ~x[minsorted[i]].getLit(hall_max - 1, 3);
					int m = 2;
					for (int k = w; bounds[k] < hall_max; ++k)
						for (int l = bucket[k]; l >= 0; l = iv[l].next) {
 //fprintf(stderr, "    var %d [%d, %d)\n", l, iv[l].min, iv[l].max);
							(*r)[m++] = ~x[l].getLit(hall_min, 2);
							(*r)[m++] = ~x[l].getLit(hall_max - 1, 3);
					}
					assert(m == 2 + (hall_max - hall_min) * 2);
				}
				if (!x[minsorted[i]].setMax(hall_min - 1, r)) {
 //fprintf(stderr, "  failure\n");
					return false;
				}
				iv[minsorted[i]].max = hall_min;
				if (x[minsorted[i]].getMax() < hall_min - 1) {
 //fprintf(stderr, "  hole, var %d [%d, %d)\n", minsorted[i], iv[minsorted[i]].min, static_cast<int>(x[minsorted[i]].getMax()) + 1);
					pushInQueue(); // hole in domain
                                }
				pathset(h, maxrank, w, w); // path compression
			}
			if (d[z] == bounds[minrank]-bounds[z]) {
 //fprintf(stderr, "  new hall [%d, %d)\n", bounds[minrank], bounds[j]);
				pathset(h, h[minrank], j+1, minrank);
				h[minrank] = j+1;
			}
		}
		return true;
	}

	bool propagate() {
 //fprintf(stderr, "AllDiffBounds::propagate()\n");
		sortit();
		return filterlower() && filterupper();
	}

	bool check() {
	  if (sz == 0) return true;
	  bool* taken = new bool[sz];
	  //		bool taken[sz];
		for (int i = 0; i < sz; i++) taken[i] = false;
		for (int i = 0; i < sz; i++) {
		  if (taken[x[i].getShadowVal()]) {
		    delete[] taken;
		    return false;
		  }
			taken[x[i].getShadowVal()] = true;
		}
	  delete[] taken;
		return true;
	}

};

struct Node {
	// for Edmonds-Karp var nodes, BFS queue link, to var node, <0 end
	// for Edmonds-Karp val nodes, back link in augmenting path, to var
	// (isn't needed for var nodes as only possible back link is match)
	// for Tarjan, stack link, <0 end, <sz var, otherwise sz+val
	int next;

	// current assignment, reciprocal pointer to other type of node
	Tint match; // <0 none

	// for Tarjan
	int index;

	// extension to Tarjan for Hall set detection
	int scc; // root of SCC, <0 stacked, <sz var, otherwise sz+val
	bool leak;

	// for Edmonds-Karp, protects BFS, for Tarjan, protects DFS
	bool mark;
};

template <int U = 0>
class AllDiffDomain : public Propagator, public Checker {
public:
	int const sz;
	IntView<U> * const x;
	int const range;

	// Persistent state
	Node *var_nodes;
	Node *val_nodes;

	// Edmonds-Karp
	int queue;
	int *queue_tail;

	// Tarjan
	int index;
	int stack; // top of stack, <0 end, <sz var, otherwise sz+val

	// extension to Tarjan for Hall set detection
	bool *scoreboard;

	AllDiffDomain(vec<IntView<U> > _x, int _range) : sz(_x.size()), x(_x.release()), range(_range)
	{
		var_nodes = new Node[sz + range];
		val_nodes = var_nodes + sz;
		for (int i = 0; i < sz + range; ++i) {
			var_nodes[i].match.v = -1;
		}

		priority = 5; 
		for (int i = 0; i < sz; i++) x[i].attach(this, i, EVENT_C);

		scoreboard = new bool[range];
		memset(scoreboard, 0, range);
	}

	void wakeup(int i, int c) {
		int j = var_nodes[i].match;
		if (j >= 0 && !x[i].indomain(j)) {
			var_nodes[i].match = -1;
			val_nodes[j].match = -1;
		}
		pushInQueue();
	}

	bool propagate() {
 //fprintf(stderr, "AllDiffDomain::propagate()\n");
		// Edmonds-Karp, loop to find and augment a path
		while (1) {
			int var;
			int val;

			// visit source
			queue_tail = &queue;
			for (int i = 0; i < sz; ++i)
				if (var_nodes[i].match < 0) {
					*queue_tail = i;
					queue_tail = &var_nodes[i].next;
				}
			*queue_tail = -1;
			for (int i = 0; i < range; ++i)
				val_nodes[i].mark = false;

			// visit vars, also subsume visit of vals
			while (queue >= 0) {
				queue_tail = &queue;
				for (var = queue; var >= 0; var = var_nodes[var].next)
					for (typename IntView<U>::iterator i = x[var].begin(); i != x[var].end(); ++i) {
						val = *i;
						if (!val_nodes[val].mark) {
							assert(val != var_nodes[var].match);
							int next_var = val_nodes[val].match;
							if (next_var < 0)
								goto augment;

							val_nodes[val].mark = true;
							val_nodes[val].next = var;
							*queue_tail = next_var;
							queue_tail = &var_nodes[next_var].next;
						}
					}
				*queue_tail = -1;
			}

			// no more augmenting paths
			break;

		augment:
			// found an augmenting path
			while (1) {
				int parent_val = var_nodes[var].match;
				val_nodes[val].match = var;
				var_nodes[var].match = val;
				if (parent_val < 0)
					break;
				val = parent_val;
				var = val_nodes[val].next;
			}
		}
 //fprintf(stderr, "match");
 //for (int i = 0; i < sz; ++i)
 // fprintf(stderr, " %d", var_nodes[i].match);
 //fprintf(stderr, "\n");

		index = 0;
		stack = -1;
		for (int i = 0; i < sz + range; ++i)
			var_nodes[i].mark = false;
		for (int i = 0; i < sz; ++i)
			if (!var_nodes[i].mark && !tarjan(i))
				return false;

		return true;
	}

	bool prune(int node, int i) {
 //fprintf(stderr, "prune var %d val %d\n", node, i);
		Clause* r = NULL;
		if (so.lazy) {
			int vars = 0;
			int vals = 0;
			int min_val = INT_MAX;
			int max_val = INT_MIN;
			int scc = val_nodes[i].scc;
			for (int j = scc; j >= 0; j = var_nodes[j].next)
				if (j < sz)
					++vars;
				else {
					++vals;
					min_val = std::min(min_val, j - sz);
					max_val = std::max(max_val, j - sz);
					scoreboard[j - sz] = true;
				}
			assert(vars == vals);
			if (vals == 1) {
				r = Reason_new(2);
				(*r)[1] = x[(scc < sz) ? scc : var_nodes[scc].next].getValLit();
			}
			else {
				r = Reason_new(1 + vars * (2 + (max_val + 1 - min_val) - vals));
				int k = 1;
				for (int j = scc; j >= 0; j = var_nodes[j].next)
					if (j < sz) {
						(*r)[k++] = ~x[j].getLit(min_val, 2);
						for (int v = min_val + 1; v < max_val; ++v)
							if (!scoreboard[v])
								(*r)[k++] = ~x[j].getLit(v, 0);
						(*r)[k++] = ~x[j].getLit(max_val, 3);
					}
				assert(k == 1 + vars * (2 + (max_val + 1 - min_val) - vals));
			}
			memset(scoreboard + min_val, 0, max_val + 1 - min_val);
		}
		return x[node].remVal(i, r);
	}

	bool tarjan(int node) {
		var_nodes[node].mark = true;

		int index_save = index++;
		var_nodes[node].index = index_save;

		var_nodes[node].next = stack;
		stack = node;
		var_nodes[node].scc = -1; // means stacked

		var_nodes[node].leak = false;
		if (node < sz)
			// visiting var node
			for (typename IntView<U>::iterator i = x[node].begin(); i != x[node].end(); ) {
				int val = *i++;
				if (!val_nodes[val].mark && !tarjan(sz + val))
					return false;
				if (val_nodes[val].scc < 0)
					var_nodes[node].index = std::min(var_nodes[node].index, val_nodes[val].index);
				else if (!val_nodes[val].leak && !prune(node, val))
					return false;
				var_nodes[node].leak |= val_nodes[val].leak;
			}
		else {
			// visiting val node
			int var = var_nodes[node].match;
			if (var < 0)
				var_nodes[node].leak = true; // unassigned value
			else {
				if (!var_nodes[var].mark && !tarjan(var))
					return false;
				if (var_nodes[var].scc < 0)
					var_nodes[node].index = std::min(var_nodes[node].index, var_nodes[var].index);
				var_nodes[node].leak |= var_nodes[var].leak;
			}
		}				

		if (var_nodes[node].index >= index_save) { // node is SCC-root
			int leak = var_nodes[node].leak;
			int scc = stack;
			stack = var_nodes[node].next;
			var_nodes[node].next = -1;

 //fprintf(stderr, "leak %d\n", leak);
			for (int i = scc; i >= 0; i = var_nodes[i].next) {
				assert(var_nodes[i].mark);
				var_nodes[i].leak = leak; // propagate through SCC
				var_nodes[i].scc = scc; // propagate through SCC
 //if (i < sz)
 // fprintf(stderr, "  var %d\n", i);
 //else
 // fprintf(stderr, "  val %d\n", i - sz);
			}
		}
		return true;
	}

	bool check() {
	  if (sz == 0) return true;
	  bool* taken = new bool[sz];
	  //		bool taken[sz];
		for (int i = 0; i < sz; i++) taken[i] = false;
		for (int i = 0; i < sz; i++) {
		  if (taken[x[i].getShadowVal()]) { delete[] taken; return false;}
			taken[x[i].getShadowVal()] = true;
		}
	  delete[] taken;
		return true;
	}

};

template <int U = 0>
class AllDiffBoundsImp : public Propagator {
public:
  BoolView b;
	int const sz;
	IntView<U> * const x;
	int const range;

	interval *iv;
	int *minsorted;
	int *maxsorted;

	int nb;
	int *bounds;
	int *t;
	int *d;
	int *h;
	int *bucket;

	AllDiffBoundsImp(BoolView _b, vec<IntView<U> > _x, int _range) : b(_b), sz(_x.size()), x(_x.release()), range(_range) {
		priority = 4;
		iv = new interval[sz];
		minsorted = new int[sz];
		maxsorted = new int[sz];
		for (int i = 0; i < sz; i++) {
			minsorted[i] = i;
			maxsorted[i] = i;
			x[i].attach(this, i, EVENT_LU);
		}
    b.attach(this, -1, EVENT_LU);
		int n = 2 * sz + 2;
		bounds = new int[n];
		t = new int[n];
		d = new int[n];
		h = new int[n];
		bucket = new int[n];
	}

	void sortit()
	{
		int i,j,min,max,last;

		for (int i = sz - 1; i >= 0; --i) {
			int t = minsorted[i];
			iv[t].min = x[t].getMin();
			int j;
			for (j = i; j < sz - 1; ++j) {
				if (iv[t].min < iv[minsorted[j + 1]].min)
					break;
				minsorted[j] = minsorted[j + 1];
			}
			minsorted[j] = t;
		}
		for (int i = sz - 1; i >= 0; --i) {
			int t = maxsorted[i];
			iv[t].max = x[t].getMax() + 1;
			int j;
			for (j = i; j < sz - 1; ++j) {
				if (iv[t].max < iv[maxsorted[j + 1]].max)
					break;
				maxsorted[j] = maxsorted[j + 1];
			}
			maxsorted[j] = t;
		}

		min = iv[minsorted[0]].min;
		max = iv[maxsorted[0]].max;
		bounds[0] = last = min-2;
	
		for (i=j=nb=0;;) { // merge minsorted[] and maxsorted[] into bounds[]
			if (i<sz && min<=max) {	// make sure minsorted exhausted first
				if (min != last)
					bounds[++nb] = last = min;
				iv[minsorted[i]].minrank = nb;
				if (++i < sz)
					min = iv[minsorted[i]].min;
			} else {
				if (max != last)
					 bounds[++nb] = last = max;
				iv[maxsorted[j]].maxrank = nb;
				if (++j == sz) break;
				max = iv[maxsorted[j]].max;
			}
		}
		bounds[nb+1] = bounds[nb] + 2;
	}

	bool filterlower()
	{
		int i,j,w,z;

 //fprintf(stderr, "AllDiffBounds::filterlower()\n");
		for (i=1; i<=nb+1; i++) {
			d[i] = bounds[i] - bounds[t[i]=h[i]=i-1];
			bucket[i] = -1; // this could perhaps be avoided
		}
		for (i=0; i<sz; i++) { // visit intervals in increasing max order
			int minrank = iv[maxsorted[i]].minrank;
			int maxrank = iv[maxsorted[i]].maxrank;
 //fprintf(stderr, "var %d [%d, %d)\n", maxsorted[i], bounds[minrank], bounds[maxrank]);
			j = t[z = pathmax(t, minrank+1)];
			iv[maxsorted[i]].next = bucket[z];
			bucket[z] = maxsorted[i];
			if (--d[z] == 0)
				t[z = pathmax(t, t[z]=z+1)] = j;
			pathset(t, minrank+1, z, z); // path compression
			//if (d[z] < bounds[z]-bounds[maxrank]) return false; // no solution
			if (h[minrank] > minrank) {
				Clause* r = NULL;
				int hall_max = bounds[w = pathmax(h, h[minrank])];
				if (so.lazy) {
					int hall_min = bounds[minrank];
					// here both k and hall_min are decreasing, stop when k catches up
					for (int k = w; bounds[k] > hall_min; --k)
						for (int l = bucket[k]; l >= 0; l = iv[l].next)
							hall_min = std::min(hall_min, iv[l].min);
 //fprintf(stderr, "  in hall [%d, %d):\n", hall_min, hall_max);
					r = Reason_new(3 + (hall_max - hall_min) * 2);
					(*r)[1] = ~x[maxsorted[i]].getLit(hall_min, 2);
					int m = 3;
					for (int k = w; bounds[k] > hall_min; --k)
						for (int l = bucket[k]; l >= 0; l = iv[l].next) {
 //fprintf(stderr, "    var %d [%d, %d)\n", l, iv[l].min, iv[l].max);
							(*r)[m++] = ~x[l].getLit(hall_min, 2);
							(*r)[m++] = ~x[l].getLit(hall_max - 1, 3);
					}
					assert(m == 3 + (hall_max - hall_min) * 2);
				}
				if (b.isFixed()) {
          assert(b.isTrue());
          (*r)[2] = b.getValLit();
          if (!x[maxsorted[i]].setMin(hall_max, r)) {
            //fprintf(stderr, "  failure\n");
            return false;
          }
          iv[maxsorted[i]].min = hall_max;
          if (x[maxsorted[i]].getMin() > hall_max) {
            //fprintf(stderr, "  hole, var %d [%d, %d)\n", maxsorted[i], static_cast<int>(x[maxsorted[i]].getMin()), iv[maxsorted[i]].max);
            pushInQueue(); // hole in domain
          }
          pathset(h, minrank, w, w); // path compression
				} else {
          if (x[maxsorted[i]].getMax() < hall_max) {
            (*r)[2] = x[maxsorted[i]].getLit(hall_max, 2);
            return b.setVal(false, r);
          }
				}
			}
			if (d[z] == bounds[z]-bounds[maxrank]) {
 //fprintf(stderr, "  new hall [%d, %d)\n", bounds[j], bounds[maxrank]);
				pathset(h, h[maxrank], j-1, maxrank); // mark hall interval
				h[maxrank] = j-1;
			}
		}
		return true;
	}

	int filterupper()
	{
		int i,j,w,z;

 //fprintf(stderr, "AllDiffBounds::filterupper()\n");
		for (i=0; i<=nb; i++) {
			d[i] = bounds[t[i]=h[i]=i+1] - bounds[i];
			bucket[i] = -1; // this could perhaps be avoided
		}
		for (i=sz; --i>=0; ) { // visit intervals in decreasing min order
			int maxrank = iv[minsorted[i]].maxrank;
			int minrank = iv[minsorted[i]].minrank;
 //fprintf(stderr, "var %d [%d, %d)\n", minsorted[i], bounds[minrank], bounds[maxrank]);
			j = t[z = pathmin(t, maxrank-1)];
			--d[z];
			iv[minsorted[i]].next = bucket[z];
			bucket[z] = minsorted[i];
			if (d[z] == 0)
				t[z = pathmin(t, t[z]=z-1)] = j;
			pathset(t, maxrank-1, z, z);
			//if (d[z] < bounds[minrank]-bounds[z]) return false; // no solution
			if (h[maxrank] < maxrank) {
				Clause* r = NULL;
				int hall_min = bounds[w = pathmin(h, h[maxrank])];
        if (so.lazy) {
          int hall_max = bounds[maxrank];
					// here both k and hall_max are increasing, stop when k catches up
					for (int k = w; bounds[k] < hall_max; ++k)
						for (int l = bucket[k]; l >= 0; l = iv[l].next)
							hall_max = std::max(hall_max, iv[l].max);
 //fprintf(stderr, "  in hall [%d, %d):\n", hall_min, hall_max);
					r = Reason_new(3 + (hall_max - hall_min) * 2);
					(*r)[1] = ~x[minsorted[i]].getLit(hall_max - 1, 3);
					int m = 3;
					for (int k = w; bounds[k] < hall_max; ++k)
						for (int l = bucket[k]; l >= 0; l = iv[l].next) {
 //fprintf(stderr, "    var %d [%d, %d)\n", l, iv[l].min, iv[l].max);
							(*r)[m++] = ~x[l].getLit(hall_min, 2);
							(*r)[m++] = ~x[l].getLit(hall_max - 1, 3);
					}
					assert(m == 3 + (hall_max - hall_min) * 2);
				}
        if (b.isFixed()) {
          assert(b.isTrue());
          (*r)[2] = b.getValLit();
          if (!x[minsorted[i]].setMax(hall_min - 1, r)) {
  //fprintf(stderr, "  failure\n");
            return false;
          }
          iv[minsorted[i]].max = hall_min;
          if (x[minsorted[i]].getMax() < hall_min - 1) {
  //fprintf(stderr, "  hole, var %d [%d, %d)\n", minsorted[i], iv[minsorted[i]].min, static_cast<int>(x[minsorted[i]].getMax()) + 1);
            pushInQueue(); // hole in domain
          }
          pathset(h, maxrank, w, w); // path compression
        } else {
          if (x[maxsorted[i]].getMin() > hall_min + 1) {
            (*r)[2] = x[maxsorted[i]].getLit(hall_min + 1, 3);
            return b.setVal(false, r);
          }
        }
			}
			if (d[z] == bounds[minrank]-bounds[z]) {
 //fprintf(stderr, "  new hall [%d, %d)\n", bounds[minrank], bounds[j]);
				pathset(h, h[minrank], j+1, minrank);
				h[minrank] = j+1;
			}
		}
		return true;
	}

	bool propagate() {
    if (b.isFixed() && b.isFalse()) {
      return true;
    }
		sortit();
    if (!filterlower()) {
      return false;
    }
    if (b.isFixed() && b.isFalse()) {
      return true;
    }
		return filterupper();
	}

};

void all_different_imp(BoolView b, vec<IntVar*>& x, ConLevel cl) {
    int min = INT_MAX, max = INT_MIN;
    for (int i = 0; i < x.size(); i++) {
      if (x[i]->getMin() < min){
        min = x[i]->getMin();
      }
      if (x[i]->getMax() > max) {
        max = x[i]->getMax();
      }
    }
    int range = max + 1 - min;
    if (!(cl == CL_BND || cl == CL_DEF)) {
        NOT_SUPPORTED;
    }
    vec<IntView<> > u;
    for (int i = 0; i < x.size(); i++) {
      u.push(IntView<>(x[i],1,-min));
    }
    if (min == 0) new AllDiffBoundsImp<0>(b, u, range);
    else          new AllDiffBoundsImp<4>(b, u, range);
}

void all_different(vec<IntVar*>& x, ConLevel cl) {
	int min = INT_MAX, max = INT_MIN;
	for (int i = 0; i < x.size(); i++) {
		if (x[i]->getMin() < min) min = x[i]->getMin();
		if (x[i]->getMax() > max) max = x[i]->getMax();
	}
	int range = max + 1 - min;
	if (cl == CL_BND) {
		vec<IntView<> > u;
		for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i],1,-min));
		if (min == 0) new AllDiffBounds<0>(u, range);
		else          new AllDiffBounds<4>(u, range);
		if (!so.alldiff_stage)
			return;
	}
	else if (cl == CL_DOM) {
		vec<IntView<> > u;
		for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i],1,-min));
		if (min == 0) new AllDiffDomain<0>(u, range);
		else          new AllDiffDomain<4>(u, range);
		if (!so.alldiff_stage)
			return;
	}
	vec<IntView<> > u;
	for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i],1,-min));
	if (min == 0) new AllDiffValue<0>(u, range);
	else          new AllDiffValue<4>(u, range);
}

void all_different_offset(vec<int>& a, vec<IntVar*>& x, ConLevel cl) {
	int min = INT_MAX, max = INT_MIN;
	for (int i = 0; i < x.size(); i++) {
		if (a[i]+x[i]->getMin() < min) min = a[i]+x[i]->getMin();
		if (a[i]+x[i]->getMax() > max) max = a[i]+x[i]->getMax();
	}
	int range = max + 1 - min;
	if (cl == CL_BND) {
		vec<IntView<> > u;
		for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i],1,a[i]-min));
		new AllDiffBounds<4>(u, range);
		if (!so.alldiff_stage)
			return;
	}
	else if (cl == CL_DOM) {
		vec<IntView<> > u;
		for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i],1,a[i]-min));
		new AllDiffDomain<4>(u, range);
		if (!so.alldiff_stage)
			return;
	}
	vec<IntView<> > u;
	for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i],1,a[i]-min));
	new AllDiffValue<4>(u, range);
}

//-----

// Inverse constraint: a[i] = j <=> b[j] = i

void inverse(vec<IntVar*>& x, vec<IntVar*>& y, int o1, int o2, ConLevel cl) {
	assert(x.size() == y.size());
	for (int i = 0; i < x.size(); i++) {
		TL_SET(x[i], setMin, o1);
		TL_SET(x[i], setMax, o1 + x.size() - 1);
		TL_SET(y[i], setMin, o2);
		TL_SET(y[i], setMax, o2 + x.size() - 1);
	}
	if (cl == CL_BND) {
		vec<IntView<> > u;
		for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i],1,-o1));
		if (o1 == 0) new AllDiffBounds<0>(u, x.size());
		else         new AllDiffBounds<4>(u, x.size());
	}
	else if (cl == CL_DOM) {
 		vec<IntView<> > u;
		for (int i = 0; i < x.size(); i++) u.push(IntView<>(x[i],1,-o1));
		if (o1 == 0) new AllDiffDomain<0>(u, x.size());
		else         new AllDiffDomain<4>(u, x.size());
	}
	for (int i = 0; i < x.size(); i++) x[i]->specialiseToEL();
	for (int i = 0; i < y.size(); i++) y[i]->specialiseToEL();
	for (int i = 0; i < x.size(); i++) {
		for (int j = 0; j < y.size(); j++) {
			sat.addClause(x[i]->getLit(o1 + j, 0), y[j]->getLit(o2 + i, 1));
			sat.addClause(x[i]->getLit(o1 + j, 1), y[j]->getLit(o2 + i, 0));
		}
	}
}
