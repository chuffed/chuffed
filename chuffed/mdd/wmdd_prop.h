#ifndef EVMDD_PROP_H_
#define EVMDD_PROP_H_
// Propagator for weighted (edge-valued) MDDs.
#include "chuffed/core/propagator.h"
#include "chuffed/mdd/opts.h"
#include "chuffed/mdd/weighted_dfa.h"
#include "chuffed/support/BVec.h"
#include "chuffed/support/misc.h"
#include "chuffed/support/sparse_set.h"
#include "chuffed/vars/int-view.h"

#include <climits>
#include <utility>

using EdgeID = int;

struct Edge {
	// Permanent properties
	int val;
	int weight;
	int begin;
	int end;

	// Transient info
	unsigned int kill_flags;
	unsigned int watch_flags;
};

// A disjunction of edges.
struct Disj {
	int sz;
	int curr_sz;
	EdgeID edges[1];
};

// Separation of the watch from the clause.
// Seems to add complexity without any real benefit.
using DisjRef = Disj*;

struct Val {
	int var;
	int val;
	DisjRef edges;

	// Transient info
	unsigned int status;
	//  unsigned int val_lim;
};

struct Node {
	// Basic properties
	int var;
	DisjRef in;
	DisjRef out;

	// Trailed state
	int in_pathC;
	int out_pathC;

	// Temporary state
	int in_value;
	int out_value;
	int status;
};

class WMDDProp : public Propagator {
	// ====================================
	// Structures for explanation rewinding
	// ====================================
	/*
	struct Pinfo {
		BTPos btpos;                      // backtrack point
		// which thing is changed (some leaf, or cost)
		// Tag format: [----leaf---|0] or [----ub----|1]
		int tag;
		// May need to add an additional field here for the bound.
		Pinfo(BTPos p, int t) : btpos(p), tag(t) {}
	};
	bool trailed_pinfo_sz;
	vec<Pinfo> p_info;
	*/

	// ====================================
	// Useful enums & structures
	// ====================================
	enum ValFlags { VAL_UNSUPP = 1 };
	enum KillCause { K_BELOW, K_ABOVE, K_VAL, K_COST };

	class VarInfo {
	public:
		VarInfo(int _min, int _offset, int _dom) : min(_min), offset(_offset), dom(_dom) {}
		int min;
		int offset;
		int dom;
	};

public:
	WMDDProp(vec<IntView<> >& _vs, IntView<> _c, vec<int>& _levels, vec<Edge>& _edges,
					 const MDDOpts& opts);

	bool fullProp();
	bool incProp();

	void incPropDown(vec<int>& clear_queue, int maxC, vec<int>& valQ);
	void incPropUp(vec<int>& clear_queue, int maxC, vec<int>& valQ);

	inline int numNodes() { return nodes.size(); }

	void debugStateTikz(unsigned int lim, bool debug = true);
	void verify();

	// Wake up only parts relevant to this event
	void wakeup(int i, int c) override {
		if (i == boolvars.size()) {
			// Cost has changed.
			assert(c & EVENT_U);
			cost_changed = true;
			pushInQueue();
		} else {
			assert(boolvars[i].isFixed());
			assert(!boolvars[i].getVal());
			if (fixedvars.elem(i)) {
				return;
			}
			clear_queue.push(i);
			//      vals[i].val_lim = fixedvars.size();
			fixedvars.insert(i);
			pushInQueue();
		}
	}

	inline bool edge_dead(int eid) { return dead_edges.elem(eid); }

	inline int edge_pathC(int eid) {
		Edge& e(edges[eid]);
		return nodes[e.begin].in_pathC + e.weight + nodes[e.end].out_pathC;
	}

	inline void kill_edge(int eid, KillCause cause) {
		assert(!dead_edges.elem(eid));
		edges[eid].kill_flags = cause;
		dead_edges.insert(eid);
	}

	// Propagate woken up parts
	bool propagate() override;
	Clause* explain(Lit p, int inf) override;
	Clause* explainConflict();

	// Clear intermediate states
	void clearPropState() override {
		clear_queue.clear();
		cost_changed = false;
		in_queue = false;
	}

protected:
	// ===========================
	// Rewinding methods
	// ===========================
	// Create a Reason for a lazily explained bounds change
	Reason createReason(int leaf) {
		/*
		if (!trailed_pinfo_sz) {
			engine.trail.last().push(TrailElem(&p_info._size(), 4));
			trailed_pinfo_sz = true;
		}
		p_info.push(Pinfo(engine.getBTPos(), leaf));
		return Reason(prop_id, p_info.size()-1);
		*/
		return {prop_id, leaf};
	}
	/*
	Reason createReason(BTPos pos, int leaf) {
		if (!trailed_pinfo_sz) {
			engine.trail.last().push(TrailElem(&p_info._size(), 4));
			trailed_pinfo_sz = true;
		}
		p_info.push(Pinfo(pos, leaf));
		return Reason(prop_id, p_info.size()-1);
	}
	*/

	// ===========================
	// Explanation support methods
	// ===========================
	// Compute the lowest smallest value of ub(c)
	// that makes a given state satisfiable.
	int compute_minC(int var, int val);
	// Same as compute_minC, but using only vals with non-zero
	// status.
	int late_minC(int var, int val);

	// Compute the shortest distance n -> T.
	int mark_frontier(int var, int val);

	// Given that mark_frontier has just been called, compute
	// a minimal subset of the current assignment which maintains
	// unsatisfiability.
	void minimize_expln(int var, int val, int maxC);
	void collect_lits(vec<Lit>& expln);

	// Incrementally explain a given inference.
	Clause* incExplain(Lit p, int var, int val);
	void incExplainUp(vec<int>& upQ, vec<Lit>& expln);
	void incExplainDown(vec<int>& downQ, vec<Lit>& expln);

	// Shrink the constraint according
	// to the current partial assignment.
	void compact();

	// Debug printout of the propagator state.
	void debugStateDot();
	void checkIncProp();

	// Data
	vec<IntView<> > intvars;
	vec<VarInfo> varinfo;

	vec<BoolView> boolvars;

	IntView<> cost;

	vec<Val> vals;
	vec<Node> nodes;

	// The base cost to & from each node.
	vec<int> in_base;
	vec<int> out_base;

	// FIXME: Not yet initialized
	int root{1};
	int T{0};

	vec<Edge> edges;
	TBitVec dead_edges;

	TrailedSet fixedvars;
	// Intermediate state
	vec<int> clear_queue;
	bool cost_changed;

	// Keeping track of which nodes have
	// some path through x=v when doing
	// explanation.
	SparseSet<> expl_care;

	// Used for the incremental algorithm,
	// to restore the propagator state to
	// the correct point in time.
	/* NOT USED AT PRESENT: We simply trail all path changes.
	vec<int> history;
	int hist_end;
	 */
	MDDOpts opts;
};

// Maybe should move this to a separate module.
WMDDProp* evgraph_to_wmdd(vec<IntVar*> vs, IntVar* cost, EVLayerGraph& g,
													EVLayerGraph::NodeID rootID, const MDDOpts& opts);

#endif
