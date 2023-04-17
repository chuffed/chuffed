#ifndef INC_PROP_H_
#define INC_PROP_H_

#include <chuffed/core/propagator.h>
#include <chuffed/mdd/MDD.h>
#include <chuffed/mdd/opts.h>
#include <chuffed/support/misc.h>
#include <chuffed/support/sparse_set.h>
#include <chuffed/vars/int-view.h>

#include <climits>
#include <utility>

#ifdef FULLPROP
#undef USE_WATCHES
#endif

#ifdef USE_WATCHES
// #define VAL_DEAD(val)       (val_entries[(val)].count == 0 ||
// edges[val_edges[val_entries[(val)].first_off]].kill_flags)
#define VAL_DEAD(val) (edges[val_edges[val_entries[(val)].first_off]].kill_flags)
#else
#define VAL_DEAD(val) (val_entries[(val)].supp_count == 0)
#endif

typedef int Value;

typedef struct i_edge {
	Value val;
	unsigned int kill_flags;
	char watch_flags;
	int begin;
	int end;
} inc_edge;

typedef struct {
	int var;

	int in_start;
	int num_in;
	int out_start;
	int num_out;
#ifndef USE_WATCHES
	int count_in;
	int count_out;
#endif

	unsigned char stat_flag;
	unsigned int kill_flag;
} inc_node;

typedef struct {
	int var;
	int val;
	int first_off;
	int count;
	int val_lim;
#ifndef USE_WATCHES
	int supp_count;
#endif
	//    unsigned char stat_flag;
	signed char stat_flag;
	int* search_cache;
} val_entry;

class MDDTemplate {
public:
	MDDTemplate(MDDTable& tab, MDDNodeInt root, vec<int>& domain_sizes);

	vec<int>& getDoms() { return _doms; }

	// Instrumentation
	uint64_t explncount;
	uint64_t nodecount;

	// MDD hack stuff
	vec<int> _doms;
	vec<val_entry> _val_entries;
	vec<inc_node> _mdd_nodes;

	vec<int> _val_edges;
	vec<int> _node_edges;
	vec<inc_edge> _edges;
};

template <int U = 0>
class MDDProp : public Propagator {
public:
	MDDProp(MDDTemplate* /*_templ*/, vec<IntView<U> >& _intvars, const MDDOpts& opts);

	bool fullProp();
	unsigned char fullPropRec(int node, int timestamp);

	void genReason(vec<int>& out, Value value);

	void shrinkReason(vec<int>& reason, Value value, int threshold = 2);

	void incConstructReason(unsigned int lim, vec<int>& out, Value val, int threshold = 2);
	//    void incConstructReason(unsigned int lim, vec<int>& out, Value val, int threshold =
	//    INT_MAX);

	void fullConstructReason(int lim, vec<int>& out, Value val);
	unsigned char mark_frontier(int node_id, int var, Value val, int lim);
	unsigned char mark_frontier_total(int var, Value val, int lim);
	//    void retrieveReason(vec<int>& out,int var, int val, int lim, int threshold = INT_MAX);
	void retrieveReason(vec<int>& out, int var, int val, int lim, int threshold = 2);

	void static_inference(vec<int>& inferences);
	void static_inference(vec<Lit>& inferences);

	inline int numNodes() { return nodes.size(); }

	void debugStateTikz(unsigned int lim, bool debug = true);
	void verify();

	// Wake up only parts relevant to this event
	void wakeup(int i, int c) override {
		assert(boolvars[i].isFixed());
		if (boolvars[i].getVal() != 0) {
			assert(0);
		} else {
			if (fixedvars.elem(i)) {
				return;
			}
			clear_queue.push(i);
			val_entries[i].val_lim = fixedvars.size();
			fixedvars.insert(i);
			pushInQueue();
		}
	}

	// Propagate woken up parts
	bool propagate() override;

	inline Lit get_val_lit(int v) {
#ifndef WEAKNOGOOD
		return intvars[val_entries[v].var].getLit(val_entries[v].val, LR_EQ);
#else
		int eval = v < 0 ? -1 * (v + 2) : v;
		return intvars[val_entries[eval].var].getLit(val_entries[eval].val, v < 0 ? 0 : 1);
#endif
	}

	Clause* explain(Lit p, int inf) override {
		vec<int> expl;
		genReason(expl, inf);

		if (opts.expl_strat == MDDOpts::E_KEEP) {
			vec<Lit> ps(expl.size());
			for (int k = 1; k < expl.size(); k++) {
				ps[k] = get_val_lit(expl[k]);
			}
			ps[0] = p;

			Clause* c = Clause_new(ps, true);
			c->learnt = true;
			sat.addClause(*c);
			return c;
		}
		Clause* r = Reason_new(expl.size());
		for (int k = 1; k < expl.size(); k++) {
			(*r)[k] = get_val_lit(expl[k]);
		}
		return r;
	}

	// Clear intermediate states
	void clearPropState() override {
		clear_queue.clear();
		in_queue = false;
	}

private:
	void clear_val(Value v);
	void kill_dom(unsigned int /*lim*/, inc_edge* e, vec<int>& kfa, vec<int>& kfb);

	// Parameters
	MDDOpts opts;

	// Data
	vec<IntView<U> > intvars;
	vec<BoolView> boolvars;

	vec<val_entry> val_entries;
	vec<inc_node> nodes;

	vec<int> val_edges;
	vec<int> node_edges;

	vec<inc_edge> edges;

	double act_decay;
	double act_inc;
	vec<double> activity;
	void bumpActivity(int val) { activity[val] += act_inc; }
	void decayActivity() { act_inc *= act_decay; }

	bool simple;

	TrailedSet fixedvars;
	// Intermediate state
	vec<int> clear_queue;
};

template <int U>
MDDProp<U>* MDDProp_new(MDDTemplate* /*_templ*/, vec<IntView<U> >& vars);

void mdd_decomp_dc(vec<IntVar*> xs, MDDTable& t, MDDNodeInt root);
#endif
