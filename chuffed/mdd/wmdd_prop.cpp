#include "chuffed/mdd/wmdd_prop.h"

#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/core/propagator.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/core/sat.h"
#include "chuffed/mdd/opts.h"
#include "chuffed/mdd/weighted_dfa.h"
#include "chuffed/support/misc.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/int-view.h"
#include "chuffed/vars/vars.h"

#include <algorithm>
#include <cassert>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <utility>

// #define FULL_PROP

// #define DEBUG_INFER
// #define DEBUG_EXPLN
#define INC_EXPLAIN
// #define WEAKNOGOOD

#define RELAX_UBC_LATER
#define EARLY_CUTOFF

DisjRef mkDisjRef(vec<EdgeID>& es) {
	int mem_size = sizeof(Disj) + (es.size() - 1) * sizeof(EdgeID);
	void* mem = malloc(mem_size);
	Disj* disj = new (mem) Disj;

	for (int ei = 0; ei < es.size(); ei++) {
		disj->edges[ei] = es[ei];
	}
	disj->sz = es.size();
	disj->curr_sz = disj->sz;
	return disj;
}

enum WatchFlag { W_ABOVE = 1, W_BELOW = 2, W_VAL = 4, W_ANY = 7 };
#define SET_WATCH(eid, flag) edges[(eid)].watch_flags |= (flag)
#define CLEAR_WATCH(eid, flag) edges[(eid)].watch_flags &= (~(flag))
#define CHECK_WATCH(eid, flag) (edges[(eid)].watch_flags & (flag))

#ifdef DEBUG_GRAPH
static int __count = 0;
#endif

// Flag used to indicate that an edge
// needs to be processed.
#define EDGE_PROC 8

#ifdef DEBUG_EXPLN
#include <iostream>
std::ostream& operator<<(std::ostream& out, Lit l) {
	if (!sign(l)) out << "~";
	out << var(l);
	return out;
}

template <class T>
std::ostream& operator<<(std::ostream& out, vec<T>& v) {
	out << "[";
	if (v.size() > 0) out << v[0];
	for (int ii = 1; ii < v.size(); ii++) out << ", " << v[ii];
	out << "]";
	return out;
}
#endif

WMDDProp::WMDDProp(vec<IntView<> >& _vs, IntView<> _c, vec<int>& _levels, vec<Edge>& _edges,
									 const MDDOpts& _opts)
		: intvars(_vs),
			cost(_c),

			root(1),
			T(0),
			edges(_edges),
			dead_edges(_edges.size()),
			fixedvars(0),  // Do we want to use this, or backtrack timestamps?
			expl_care(0),
			opts(_opts) {
	// Attach variables
	// Literals for each assignment [| x != i |]
	vec<vec<int> > val_edges;
	for (int i = 0; i < intvars.size(); i++) {
		int min = intvars[i].getMin();
		int max = intvars[i].getMax();
		int dom = max - min + 1;
		int offset = boolvars.size();
		VarInfo info(min, offset, dom);
		varinfo.push(info);

		for (int j = min; j <= max; j++) {
			boolvars.push(intvars[i].getLit(j, LR_EQ));  // v[i] \eq j
			boolvars.last().attach(this, boolvars.size() - 1, EVENT_U);
			val_edges.push();
		}
	}
	fixedvars.growTo(val_edges.size());

	// Assumptions:
	// ============
	// Node 0 is T.
	// Node 1 is the root.
	// There are no long edges.
	vec<vec<int> > in_vec;
	vec<vec<int> > out_vec;
	for (int ni = 0; ni < _levels.size(); ni++) {
		in_vec.push();
		out_vec.push();
	}

	for (int ei = 0; ei < edges.size(); ei++) {
		Edge& e(edges[ei]);
		e.kill_flags = 0;
		e.watch_flags = 0;
		in_vec[e.end].push(ei);
		out_vec[e.begin].push(ei);

		VarInfo vinfo(varinfo[_levels[e.begin]]);
		int vidx = vinfo.offset + (e.val - vinfo.min);
		val_edges[vidx].push(ei);
		// Rename the edge value to be the unique (var,val) index.
		e.val = vidx;
	}

	for (int ni = 0; ni < _levels.size(); ni++) {
		// Construct each node.
		DisjRef in_edges(mkDisjRef(in_vec[ni]));
		if (in_edges->sz > 0) {
			SET_WATCH(in_edges->edges[0], W_BELOW);
		} else {
			// Only the root node has no parents.
			assert(ni == 1);
		}

		DisjRef out_edges(mkDisjRef(out_vec[ni]));
		if (out_edges->sz > 0) {
			SET_WATCH(out_edges->edges[0], W_ABOVE);
		} else {
			// Similarly, only the T node has no children.
			assert(ni == 0);
		}

		Node curr = {// Basic properties
								 _levels[ni], in_edges, out_edges};
		nodes.push(curr);

		in_base.push(0);
		out_base.push(0);
	}
	expl_care.growTo(nodes.size());

	for (int vv = 0; vv < intvars.size(); vv++) {
		VarInfo vinfo(varinfo[vv]);
		int vidx = vinfo.offset;
		int val = vinfo.min;
		int end = vinfo.min + vinfo.dom;
		for (; val < end; val++, vidx++) {
			// Create the array of supports.
			DisjRef disj(mkDisjRef(val_edges[vidx]));
			Val vref = {vv, val, disj};
			vals.push(vref);

			// Set up the watches.
			if (disj->sz > 0) {
				SET_WATCH(disj->edges[0], W_VAL);
			} else {
				if (intvars[vv].remValNotR(val)) {
					intvars[vv].remVal(val);
				}
			}
		}
	}

	// Also need to wake up if the maximum cost drops.
	cost.attach(this, boolvars.size(), EVENT_U);

	// Ensure all the paths are initialized.
	bool okay = fullProp();
	if (!okay) {
		TL_FAIL();
	}

	for (int nID = 0; nID < nodes.size(); nID++) {
		int inV = nodes[nID].in_value;
		int outV = nodes[nID].out_value;
		nodes[nID].in_pathC = inV;
		nodes[nID].out_pathC = outV;

		in_base[nID] = inV;
		out_base[nID] = outV;
	}

#ifdef DEBUG_GRAPH
	if (__count == 0) debugStateDot();
	__count++;
#endif
}

// Shrink the constraint by eliminating any infeasible
// edges/nodes.
// Makes the assumption that in_value and out_value are up
// to date for all reachable nodes.
// FIXME: Currently doesn't update the watches.
void WMDDProp::compact() {
#ifdef FULL_PROP
	int maxC = cost.getMax();
#endif
	for (int nID = 0; nID < nodes.size(); nID++) {
		Node& node(nodes[nID]);
#ifndef FULL_PROP
		in_base[nID] = node.in_pathC;
		out_base[nID] = node.out_pathC;
#else
		in_base[nID] = node.in_value;
		out_base[nID] = node.out_value;
#endif

		int jj = 0;
		for (int ei = 0; ei < node.out->sz; ei++) {
			int eid = node.out->edges[ei];
#ifdef FULL_PROP
			Edge& edge(edges[eid]);
			if (boolvars[edge.val].isFalse() || nodes[edge.end].out_value == INT_MAX ||
					node.in_value + edge.weight + nodes[edge.end].out_value > maxC)
				continue;
#else
			if (dead_edges.elem(eid)) {
				continue;
			}
#endif
			node.out->edges[jj++] = eid;
		}
		node.out->sz = jj;
		node.out->curr_sz = jj;

		jj = 0;
		for (int ei = 0; ei < node.in->sz; ei++) {
			int eid = node.in->edges[ei];
#ifdef FULL_PROP
			Edge& edge(edges[eid]);
			if (boolvars[edge.val].isFalse() || node.out_value == INT_MAX ||
					nodes[edge.begin].in_value + edge.weight + node.out_value > maxC)
				continue;
#else
			if (dead_edges.elem(eid)) {
				continue;
			}
#endif
			node.in->edges[jj++] = eid;
		}
		node.in->sz = jj;
		node.in->curr_sz = jj;
	}
#ifndef FULL_PROP
	for (int vv = 0; vv < vals.size(); vv++) {
		Val& vinfo(vals[vv]);
		int jj = 0;
		for (int ii = 0; ii < vinfo.edges->sz; ii++) {
			if (dead_edges.elem(vinfo.edges->edges[ii])) {
				continue;
			}
			vinfo.edges->edges[jj++] = vinfo.edges->edges[ii];
		}
		vinfo.edges->sz = jj;
		vinfo.edges->curr_sz = jj;
		if (jj > 0) {
			int eid = vinfo.edges->edges[0];
			if (!CHECK_WATCH(eid, W_VAL)) {
				SET_WATCH(eid, W_VAL);
			}
		}
	}
#endif
}

bool WMDDProp::propagate() {
#ifdef FULL_PROP
	bool ret = fullProp();
#else
	nodes[T].status = 0;
	nodes[root].status = 0;
	bool ret = incProp();
#endif

	if (sat.decisionLevel() == 0 && ret) {
		compact();
	}

	return ret;
}

// Full propagation algorithm.
bool WMDDProp::fullProp() {
	//  for(int nID = 1; nID < nodes.size(); nID++)
	//    assert(nodes[nID].status == 0);
	for (int vv = 0; vv < vals.size(); vv++) {
		if (!boolvars[vv].isFalse()) {
			vals[vv].status = VAL_UNSUPP;
		}
	}

	clear_queue.clear();

	// Ensure T is never enqueued.
	nodes[T].status = 1;
	nodes[T].in_value = INT_MAX;
	nodes[T].out_value = 0;

	// Walk forward, propagating the shortest path from r.
	vec<int> stateQ;
	stateQ.push(root);
	int qidx = 0;

	while (qidx < stateQ.size()) {
		int nID = stateQ[qidx];
		Node& node(nodes[nID]);

		//    for(int ei = 0; ei < node.out->sz; ei++)
		for (int ei = 0; ei < node.out->curr_sz; ei++) {
			int eid = node.out->edges[ei];
			Edge& e(edges[eid]);

			//      if(fixedvars.elem(e.val))
			if (boolvars[e.val].isFalse()) {
				continue;
			}

			Node& dest(nodes[e.end]);
			if (dest.status == 0) {
				// Not yet touched.
				dest.status = 1;
				dest.in_value = node.in_value + e.weight;
				stateQ.push(e.end);
			} else {
				dest.in_value = std::min(dest.in_value, node.in_value + e.weight);
			}
		}
		qidx++;
	}

	int minC = nodes[T].in_value;
	int maxC = cost.getMax();
	// Check feasibility.
	if (minC > maxC) {
		// Clear the status flags.
		for (qidx = 0; qidx < stateQ.size(); qidx++) {
			nodes[stateQ[qidx]].status = 0;
		}

		if (so.lazy) {
			// Generate an explanation.
			for (int vv = 0; vv < vals.size(); vv++) {
				vals[vv].status = 0;
			}

			Clause* r = explainConflict();
			sat.confl = r;
		}
		return false;
	}
	if (cost.setMinNotR(minC)) {
		Reason r = createReason((minC << 1) | 1);
		if (!cost.setMin(minC, r)) {
			return false;
		}
	}

	// Walk backwards, propagating the shortest path to T.
	for (qidx = stateQ.size() - 1; qidx >= 0; qidx--) {
		int nID = stateQ[qidx];
		Node& node(nodes[nID]);

		// Reset the status flags on the way back.
		node.status = 0;
		int dist_from = INT_MAX;

		int sz = node.out->curr_sz;
		//    for(int ei = 0; ei < node.out->sz; ei++)
		for (int ei = sz - 1; ei >= 0; ei--) {
			int eid = node.out->edges[ei];

			Edge& e(edges[eid]);
			//      if(fixedvars.elem(e.val))
			if (boolvars[e.val].isFalse()) {
				std::swap(node.out->edges[ei], node.out->edges[--sz]);
				continue;
			}

			Node& dest(nodes[e.end]);
			// Need to be careful adding anything to INT_MAX when it's to be
			// stored as an integer.
			if (dest.out_value == INT_MAX || node.in_value + e.weight + dest.out_value > maxC) {
				// No point updating distances if they're infeasible.
				std::swap(node.out->edges[ei], node.out->edges[--sz]);
				continue;
			}
			vals[e.val].status &= (~VAL_UNSUPP);
			dist_from = std::min(dist_from, dest.out_value + e.weight);
		}
		node.out_value = dist_from;
		if (sz < node.out->curr_sz) {
			trailChange(node.out->curr_sz, sz);
		}
	}

#ifdef DEBUG_INFER
	bool changes = false;
#endif
	for (int vv = 0; vv < vals.size(); vv++) {
		if (vals[vv].status != 0U) {
			int var(vals[vv].var);
			int val(vals[vv].val);
			if (intvars[var].remValNotR(val)) {
#ifdef DEBUG_INFER
				if (!changes) {
					changes = true;
					printf("[");
				} else {
					printf(",");
				}
				printf("%d", vv);
#endif
				Reason r = createReason(vv << 1);
				if (!intvars[var].remVal(val, r)) {
					return false;
				}
				//        fixedvars.insert(vv);
			}
			vals[vv].status = 0;
		}
	}
#ifdef DEBUG_INFER
	if (changes) printf("]\n");
#endif

	return true;
}

void WMDDProp::incPropDown(vec<int>& clear_queue, int maxC, vec<int>& valQ) {
	//  for(int ni = 0; ni < nodes.size(); ni++)
	//    nodes[ni].status = 0;
	vec<int> downQ;
	int clear_idx = 0;
	int down_idx = 0;
	int level = -1;
	while (clear_idx < clear_queue.size() || down_idx < downQ.size()) {
		level = (down_idx == downQ.size()) ? vals[clear_queue[clear_idx]].var : level + 1;

		// Remove any additional edges corresponding to values removed from the current variable, and
		// enqueue the affected nodes.
		for (; clear_idx < clear_queue.size(); clear_idx++) {
			int vv = clear_queue[clear_idx];
			if (vals[vv].var != level) {
				break;
			}

			DisjRef es(vals[vv].edges);
			for (int ei = 0; ei < es->sz; ei++) {
				int eid = es->edges[ei];
				assert(eid < edges.size());
				if (dead_edges.elem(eid)) {
					continue;
				}

				dead_edges.insert(eid);
				Edge& e(edges[eid]);
				e.kill_flags |= EDGE_PROC;

				// Enqueue e.end if the loss of e might change the shortest path.
				if (nodes[e.end].status == 0) {
					nodes[e.end].status = 1;
					downQ.push(e.end);
				}
			}
		}

		int down_next = downQ.size();
		for (; down_idx < down_next; down_idx++) {
			int nID = downQ[down_idx];
			Node& node(nodes[nID]);
			node.status = 0;
#ifdef EARLY_CUTOFF
			if (node.in_pathC + node.out_pathC > maxC) {
				continue;
			}
#endif

			// Compute the updated cost c(r -> n)
			int oldC = node.in_pathC;
			int bestC = INT_MAX;
			for (int ei = 0; ei < node.in->sz; ei++) {
				int eid = node.in->edges[ei];
				assert(eid < edges.size());
				//        if(dead_edges.elem(eid))
				if (fixedvars.elem(edges[eid].val)) {
					continue;
				}
				Edge& e(edges[eid]);
				int eC = nodes[e.begin].in_pathC == INT_MAX ? INT_MAX : nodes[e.begin].in_pathC + e.weight;
				if (eC < bestC) {
					bestC = eC;
					if (bestC == oldC) {
						break;
					}
				}
			}
			// If the path length remains the same,
			// we can stop.
			if (bestC == oldC) {
				continue;
			}

			// Separated out this case so we don't have to check if
			// the node is reachable every time we update an edge.
			trailChange(node.in_pathC, bestC);
			if (bestC == INT_MAX) {
				for (int ei = 0; ei < node.out->sz; ei++) {
					int eid = node.out->edges[ei];
					assert(eid < edges.size());
					if (dead_edges.elem(eid)) {
						continue;
					}
					dead_edges.insert(eid);
					if (CHECK_WATCH(eid, W_VAL)) {
						valQ.push(edges[eid].val);
					}

					Edge& e(edges[eid]);

					if (nodes[e.end].status == 0) {
						nodes[e.end].status = 1;
						downQ.push(e.end);
					}
				}
			} else {
				// Propagate the affected nodes, updating
				for (int ei = 0; ei < node.out->sz; ei++) {
					int eid = node.out->edges[ei];
					assert(eid < edges.size());
					if (dead_edges.elem(eid)) {
						continue;
					}
					// If nodes[e.end].out_pathC was INT_MAX, e would already
					// be dead; so we don't need to worry about INT_MAX-y nodes.
					Edge& e(edges[eid]);
					if (bestC + e.weight + nodes[e.end].out_pathC > maxC) {
						dead_edges.insert(eid);
						if (CHECK_WATCH(eid, W_VAL)) {
							valQ.push(edges[eid].val);
						}
					}

					if (nodes[e.end].status == 0) {
						nodes[e.end].status = 1;
						downQ.push(e.end);
					}
				}
			}
		}
	}
}

void WMDDProp::incPropUp(vec<int>& clear_queue, int maxC, vec<int>& valQ) {
	//  for(int ni = 0; ni < nodes.size(); ni++)
	//    nodes[ni].status = 0;

	vec<int> upQ;
	int clear_idx = clear_queue.size() - 1;
	int up_idx = 0;
	int level = nodes[T].var;
	while (clear_idx >= 0 || up_idx < upQ.size()) {
		level = (up_idx == upQ.size()) ? vals[clear_queue[clear_idx]].var : level - 1;

		// Remove any additional edges corresponding to values removed from the current variable, and
		// enqueue the affected nodes.
		for (; clear_idx >= 0; clear_idx--) {
			int vv = clear_queue[clear_idx];
			if (vals[vv].var != level) {
				break;
			}

			DisjRef es(vals[vv].edges);
			for (int ei = 0; ei < es->sz; ei++) {
				int eid = es->edges[ei];
				assert(eid < edges.size());
				// All these edges are already dead, since we've run incPropDown.
				// We use kill-flags instead.
				Edge& e(edges[eid]);
				if ((e.kill_flags & EDGE_PROC) == 0U) {
					continue;
				}
				e.kill_flags &= (~EDGE_PROC);

				// Enqueue e.begin if the loss of e might change the shortest path.
				// FIXME: This actually needs to be the value of pathC
				//        before propagation started, not at the current time.
				if (nodes[e.begin].status == 0) {
					assert(e.begin < nodes.size());
					nodes[e.begin].status = 1;
					upQ.push(e.begin);
				}
			}
		}

		int up_next = upQ.size();
		for (; up_idx < up_next; up_idx++) {
			int nID = upQ[up_idx];
			assert(nID < nodes.size());
			Node& node(nodes[nID]);
			node.status = 0;
#ifdef EARLY_CUTOFF
			if (node.in_pathC + node.out_pathC > maxC) {
				continue;
			}
#endif

			// Compute the updated cost c(r -> n)
			int oldC = node.out_pathC;
			int bestC = INT_MAX;
			for (int ei = 0; ei < node.out->sz; ei++) {
				int eid = node.out->edges[ei];
				Edge& e(edges[eid]);
				//        if(dead_edges.elem(eid))
				if (fixedvars.elem(e.val)) {
					continue;
				}
				int eC = nodes[e.end].out_pathC == INT_MAX ? INT_MAX : nodes[e.end].out_pathC + e.weight;
				//        int eC = nodes[e.end].out_pathC + e.weight;
				if (eC < bestC) {
					bestC = eC;
					if (bestC == oldC) {
						break;
					}
				}
			}
			// If the path length remains the same,
			// we can stop.
			if (bestC == oldC) {
				continue;
			}

			// Separated out this case so we don't have to check if
			// the node is reachable every time we update an edge.
			trailChange(node.out_pathC, bestC);
			if (bestC == INT_MAX) {
				for (int ei = 0; ei < node.in->sz; ei++) {
					int eid = node.in->edges[ei];
					assert(eid < edges.size());
					if (dead_edges.elem(eid)) {
						continue;
					}
					dead_edges.insert(eid);
					if (CHECK_WATCH(eid, W_VAL)) {
						valQ.push(edges[eid].val);
					}

					Edge& e(edges[eid]);
					if (nodes[e.begin].status == 0) {
						assert(e.begin < nodes.size());
						nodes[e.begin].status = 1;
						upQ.push(e.begin);
					}
				}
			} else {
				// Propagate the affected nodes, updating
				for (int ei = 0; ei < node.in->sz; ei++) {
					int eid = node.in->edges[ei];
					assert(eid < edges.size());
					if (dead_edges.elem(eid)) {
						continue;
					}
					// If nodes[e.end].in_pathC was INT_MAX, e would already
					// be dead; so we don't need to worry about INT_MAX-y nodes.
					Edge& e(edges[eid]);
					if (bestC + e.weight + nodes[e.begin].in_pathC > maxC) {
						dead_edges.insert(eid);
						if (CHECK_WATCH(eid, W_VAL)) {
							valQ.push(edges[eid].val);
						}
					}

					if (nodes[e.begin].status == 0) {
						assert(e.begin < nodes.size());
						nodes[e.begin].status = 1;
						upQ.push(e.begin);
					}
				}
			}
		}
	}
}

// Incremental propagation algorithm
bool WMDDProp::incProp() {
	vec<int> valQ;
	// Changing ub(cost) doesn't change the distance
	// along any paths; it just eliminates some paths.
	// So it should be sufficient to check the value watches
	// for any edges such that
	// c(r -> begin) + weight + c(dest -> T) > ub(cost)
	int maxC = cost.getMax();
	if (cost_changed) {
		// Pretty sure this should never fire, since
		// we should have propagated lb(cost) >= c(r -> T)
		// earlier
		if (nodes[root].out_pathC > maxC) {
			if (so.lazy) {
				// Generate an explanation.
				Clause* r = explainConflict();
				sat.confl = r;
			}
			return false;
		}

		// Check if the watch for each value is still
		// alive.
		for (int vv = 0; vv < vals.size(); vv++) {
			if (boolvars[vv].isFalse()) {
				continue;
			}

			// If the watch is no longer on a satisfying path, mark the
			// value for further investigation.
			if (edge_pathC(vals[vv].edges->edges[0]) > maxC) {
				valQ.push(vv);
			}
		}
	}

	if (clear_queue.size() == 0) {
		return true;
	}

	// We want to process the affected edges level-at-a-time.
	// So, sort the values in ascending order.
	std::sort((int*)clear_queue, ((int*)clear_queue) + clear_queue.size());

	// Compute the downward phase first, computing shortest
	// paths c(r -> n).
	incPropDown(clear_queue, maxC, valQ);

	// Check if a path c(r -> n) is still feasible.
	int minC = nodes[T].in_pathC;
	if (minC > maxC) {
		if (so.lazy) {
			// Generate an explanation.
			Clause* r = explainConflict();
			sat.confl = r;
		}
		return false;
	}
	if (cost.setMinNotR(minC)) {
		Reason r = createReason((minC << 1) | 1);
		if (!cost.setMin(minC, r)) {
			return false;
		}
	}

	// Compute the upward phase, shortest paths c(n -> T).
	incPropUp(clear_queue, maxC, valQ);

	// Determine which values are now missing supports.
#ifdef DEBUG_INFER
	bool changes = false;
#endif
	std::sort((int*)valQ, ((int*)valQ) + valQ.size());

	for (int vi = 0; vi < valQ.size(); vi++) {
		int vv = valQ[vi];
		Val& vinfo(vals[vv]);
		vinfo.status = 0;

		// Search for a new watch.
		for (int ei = 0; ei < vinfo.edges->sz; ei++) {
			int eid = vinfo.edges->edges[ei];
			if (!dead_edges.elem(eid)) {
				// Update the watches.
				CLEAR_WATCH(vinfo.edges->edges[0], W_VAL);
				SET_WATCH(eid, W_VAL);
				vinfo.edges->edges[ei] = vinfo.edges->edges[0];
				vinfo.edges->edges[0] = eid;
				goto vwatch_found;
			}
		}

		// No watch. Kill the val.
		{
			int var(vinfo.var);
			int val(vinfo.val);
			if (intvars[var].remValNotR(val)) {
#ifdef DEBUG_INFER
				if (!changes) {
					changes = true;
					printf("[");
				} else {
					printf(",");
				}
				printf("%d", vv);
#endif
				Reason r = createReason(vv << 1);
				if (!intvars[var].remVal(val, r)) {
					return false;
				}
			}
		}
	vwatch_found:
		continue;
	}
#ifdef DEBUG_INFER
	if (changes) printf("]\n");
#endif

	return true;
}

/*
void WMDDProp::checkIncProp(void)
{
	for(int nID = 0; nID < nodes.size(); nID++)
	{
		if(nID != root)
		{
			// Check the up-cost has been updated.
			Node& n(nodes[nID]);

			int minC = INT_MAX;
			for(int ei = 0; ei < n.in->sz; ei++)
			{
				if(dead_edges.elem( ))
			}
		}
		if(nID != T)
		{

		}
	}
}
*/

// (Locally) minimal explanation algorithm
// =======================================
// (1) Walk the graph breadth-first (assuming no long edges),
//     computing the shortest path to T through [|x = v|].
//     This tells us the weakest cost which remains infeasible.
// (2) Walk backwards in the reverse order, annotating each
//     node with the shortest distance from r to n
//     which does not make r -> n -> T feasible.
//     Note that this pass traverses *all* nodes, not just those
//     reachable under the current assignment (cf. (1))
// (3) Walk forward, collecting nodes in the same manner as
//     the MDD algorithm.
// GKG: May be faster to use an inline linked list
//      instead of a queue.

// Compute the least upper bound necessary to restore
// feasibility.
int WMDDProp::compute_minC(int var, int val) {
	assert(0 && "No longer used.");
	//  for(int nID = 0; nID < nodes.size(); nID++)
	//    nodes[nID].status = 0;

	vec<int> stateQ;
	stateQ.push(root);
	int qidx = 0;

	nodes[root].in_value = 0;
	nodes[T].in_value = INT_MAX;

	while (qidx < stateQ.size()) {
		int nID = stateQ[qidx];
		Node& node(nodes[nID]);

		// The path must pass through [|x = v|].
		if (node.var == var) {
			for (int ei = 0; ei < node.out->sz; ei++) {
				int eid = node.out->edges[ei];
				Edge& e(edges[eid]);
				if (e.val == val) {
					Node& dest(nodes[e.end]);
					if (dest.status == 0) {
						dest.status = 1;
						dest.in_value = node.in_value + e.weight;
						stateQ.push(e.end);
					} else {
						dest.in_value = std::min(dest.in_value, node.in_value + e.weight);
					}
				}
			}
		} else {
			// For any other node, just compute the distance similarly.
			for (int ei = 0; ei < node.out->sz; ei++) {
				int eid = node.out->edges[ei];
				Edge& e(edges[eid]);

				//        if(boolvars[e.val].isFalse())
				if (fixedvars.elem(e.val)) {
					continue;
				}

				Node& dest(nodes[e.end]);
				if (dest.status == 0) {
					// Not yet touched.
					dest.status = 1;
					dest.in_value = node.in_value + e.weight;
					stateQ.push(e.end);
				} else {
					dest.in_value = std::min(dest.in_value, node.in_value + e.weight);
				}
			}
		}
		qidx++;
	}

	return nodes[T].in_value;
}

// Same as compute_minC, but with respect to a subset of
// the fixed variables.
int WMDDProp::late_minC(int var, int val) {
	vec<int> stateQ;
	stateQ.push(root);
	int qidx = 0;

	nodes[root].in_value = 0;
	nodes[T].in_value = INT_MAX;

	while (qidx < stateQ.size()) {
		int nID = stateQ[qidx];
		Node& node(nodes[nID]);
		node.status = 0;

		// The path must pass through [|x = v|].
		if (node.var == var) {
			for (int ei = 0; ei < node.out->sz; ei++) {
				int eid = node.out->edges[ei];
				Edge& e(edges[eid]);
				if (e.val == val) {
					Node& dest(nodes[e.end]);
					if (dest.status == 0) {
						dest.status = 1;
						dest.in_value = node.in_value + e.weight;
						stateQ.push(e.end);
					} else {
						dest.in_value = std::min(dest.in_value, node.in_value + e.weight);
					}
				}
			}
		} else {
			// For any other node, just compute the distance similarly.
			for (int ei = 0; ei < node.out->sz; ei++) {
				int eid = node.out->edges[ei];
				Edge& e(edges[eid]);

				//        if(boolvars[e.val].isFalse())
				if (vals[e.val].status != 0U) {
					continue;
				}

				Node& dest(nodes[e.end]);
				if (dest.status == 0) {
					// Not yet touched.
					dest.status = 1;
					dest.in_value = node.in_value + e.weight;
					stateQ.push(e.end);
				} else {
					dest.in_value = std::min(dest.in_value, node.in_value + e.weight);
				}
			}
		}
		qidx++;
	}

	return nodes[T].in_value;
}

// For each node, mark the shortest distance r -> n such that
// c(r -> n -> T) > maxC under [|x = v|].
// Assumption: Nodes are ordered topologically.
// Also resets all node status flags.
int WMDDProp::mark_frontier(int var, int val) {
	assert(T == 0);
	assert(root == 1);
	nodes[T].out_value = 0;

	for (int nID = nodes.size() - 1; nID > 0; nID--) {
		Node& node(nodes[nID]);

		// Reset status flags
		node.status = 0;
		int dist_from = INT_MAX;

		if (node.var == var) {
			for (int ei = 0; ei < node.out->sz; ei++) {
				int eid = node.out->edges[ei];
				Edge& e(edges[eid]);
				if (e.val == val) {
					int dC = nodes[e.end].out_value;
					if (dC < INT_MAX) {
						dist_from = dC + e.weight;
					}
				}
			}
		} else {
			for (int ei = 0; ei < node.out->sz; ei++) {
				int eid = node.out->edges[ei];

				Edge& e(edges[eid]);
				//        if(boolvars[e.val].isFalse())
				if (fixedvars.elem(e.val)) {
					continue;
				}

				Node& dest(nodes[e.end]);
				// Need to be careful adding anything to INT_MAX when it's to be
				// stored as an integer.
				if (dest.out_value == INT_MAX) {
					continue;
				}
				dist_from = std::min(dist_from, dest.out_value + e.weight);
			}
		}
		node.out_value = dist_from;
	}
	nodes[T].status = 0;

	return nodes[root].out_value;
}

// In the presence of early-cutoff, this is not guaranteed
// to be exact (and therefore minimal). However, it should
// be correct.
// We only need to explain nodes that have some path through
// x = v; these are recorded in expl_care.
#define NODE_QUEUED 1
#define NODE_CHECK 2
/*
int WMDDProp::mark_frontier_phased(int var, int val)
{
	assert(var >= 0);
	expl_care.clear();

	// Check which set of edges we start with.
	Val& vinfo(vals[val]);

	vec<int> upQ;

	// Any nodes past the given edge have correct values
	for(int ei = 0; ei < vinfo.edges->sz; ei++)
	{
		EdgeID eid(vinfo.edges->edges[ei]);
		Edge& e(edges[eid]);

		if(!nodes[e.begin].status)
		{
			nodes[e.begin].status = 1;
			nodes[e.begin].dist_from = nodes[e.end].out_pathC + e.weight;
			upQ.push(e.begin);
		} else {
			nodes[e.begin].dist_from = std::min(nodes[e.begin].dist_from, nodes[e.end].out_pathC +
e.weight);
		}
	}

	int qhead = 0;
	while(qhead < upQ.size())
	{
		int nID = upQ[qhead];
		Node& n(nodes[nID]);

		// Reset the status flags.
		n.status = 0;

		// We need to know which nodes to ignore.
		// We'll reset the status flags during collection.
		expl_care.insert(nID);

		for(int ei = 0; ei < n.in->sz; ei++)
		{
			Edge& e(edges[eid]);
			if(!nodes[e.begin].status)
			{
				nodes[e.begin].status = 1;
				nodes[e.begin].dist_from = INT_MAX;
				upQ.push(e.begin);
			}
			if(!fixedvars.elem(e.val))
			{
				nodes[e.begin].dist_from = std::min(nodes[e.begin].dist_from, n.dist_from + e.weight);
			}
		}
	}
}
*/

#define VAL_LOCKED 1
#define VAL_WEAK 2

#define WEAKEN_THRESHOLD 2
// Phased version of minimal explanation.
// For layers [0, var), path cost is given by dest_from.
// For layer [var, N), cost is given by out_pathC.
//
/*
void WMDDProp::minimize_expln_phased(int var, int val, int maxC)
{
	// A variable can be relaxed if its status is 0.
	for(int vi = 0; vi < vals.size(); vi++)
		vals[vi].status = 0;

	vec<int> stateQ;
	stateQ.push(root);
	int qhead = 0;

	nodes[root].in_value = 0;

	int level = 0;

	while(qhead < stateQ.size())
	{
		// Ensure that we're keeping track of the levels correctly.
		assert(nodes[stateQ[qhead]].var == level);

		int qnext = stateQ.size();

		if(level == var)
		{
			for(; qhead < qnext; qhead++)
			{
				int nID = stateQ[qhead];
				Node& node(nodes[nID]);
				for(int ei = 0; ei < node.out->sz; ei++)
				{
					int eid = node.out->edges[ei];
					Edge& e(edges[eid]);
					if(e.val == val)
					{
						if(!expl_care.elem(e.end))
							continue;
						if(!nodes[e.end].status)
						{
							nodes[e.end].status = 1;
							stateQ.push(e.end);
							nodes[e.end].in_value = node.in_value + e.weight;
						} else {
							nodes[e.end].in_value =
								std::min(nodes[e.end].in_value, node.in_value + e.weight);
						}
					}
				}
				node.status = 0;
			}
		} else if(level < var) {
			// Determine which values must be locked.
			for(int qidx = qhead; qidx < qnext; qidx++)
			{
				int nID = stateQ[qidx];
				Node& node(nodes[nID]);
				for(int ei = 0; ei < node.out->sz; ei++)
				{
					int eid = node.out->edges[ei];
					Edge& e(edges[eid]);
					int dC = nodes[e.end].out_value;
					if(dC < INT_MAX && node.in_value + e.weight + dC <= maxC)
					{
						assert(boolvars[e.val].isFalse());
						vals[e.val].status = VAL_LOCKED;
					}
				}
			}

			// Add any nodes along unlocked edges to the next level.
			for(; qhead < qnext; qhead++)
			{
				int nID = stateQ[qhead];
				Node& node(nodes[nID]);
				for(int ei = 0; ei < node.out->sz; ei++)
				{
					int eid = node.out->edges[ei];
					Edge& e(edges[eid]);
					if(!vals[e.val].status)
					{
						if(!nodes[e.end].status)
						{
							nodes[e.end].status = 1;
							stateQ.push(e.end);
							nodes[e.end].in_value = node.in_value + e.weight;
						} else {
							nodes[e.end].in_value =
								std::min(nodes[e.end].in_value, node.in_value + e.weight);
						}
					}
				}
				// Clear the status flags.
				node.status = 0;
			}
		} else {
			// Level > var.
		}
		level++;
	}
}
*/

// Walk the graph var-at-a-time, unfixing any values which will not
// expose a path to T of length <= maxC.
// Assumption:
//  - We've just run mark_frontier. As such, at each node:
//    + n.out_value is the length of the shortest path n -> T
//    + (n.out_value = INT_MAX and n.in_value = 0) or n.in_value + n.out_value = maxC
void WMDDProp::minimize_expln(int var, int val, int maxC) {
	// A variable can be relaxed if its status is 0.
	for (int vi = 0; vi < vals.size(); vi++) {
		vals[vi].status = 0;
	}

	vec<int> stateQ;
	stateQ.push(root);
	int qhead = 0;

	nodes[root].in_value = 0;

	int level = 0;

	while (qhead < stateQ.size()) {
		// Ensure that we're keeping track of the levels correctly.
		assert(nodes[stateQ[qhead]].var == level);

		int qnext = stateQ.size();

		if (level == var) {
			for (; qhead < qnext; qhead++) {
				int nID = stateQ[qhead];
				Node& node(nodes[nID]);
				for (int ei = 0; ei < node.out->sz; ei++) {
					int eid = node.out->edges[ei];
					Edge& e(edges[eid]);
					if (e.val == val) {
						if (nodes[e.end].status == 0) {
							nodes[e.end].status = 1;
							stateQ.push(e.end);
							nodes[e.end].in_value = node.in_value + e.weight;
						} else {
							nodes[e.end].in_value = std::min(nodes[e.end].in_value, node.in_value + e.weight);
						}
					}
				}
				node.status = 0;
			}
		} else {
			// Determine which values must be locked.
#ifdef WEAKNOGOOD
			int val_count = 0;
#endif
			for (int qidx = qhead; qidx < qnext; qidx++) {
				int nID = stateQ[qidx];
				Node& node(nodes[nID]);
				if (node.in_value + out_base[nID] > maxC) {
					continue;
				}
				for (int ei = 0; ei < node.out->sz; ei++) {
					int eid = node.out->edges[ei];
					Edge& e(edges[eid]);
					int dC = nodes[e.end].out_value;
					if (dC < INT_MAX && node.in_value + e.weight + dC <= maxC) {
						assert(boolvars[e.val].isFalse());
#ifdef WEAKNOGOOD
						if (!vals[e.val].status) val_count++;
#endif
						vals[e.val].status = VAL_LOCKED;
					}
				}
			}

#ifdef WEAKNOGOOD
			bool invert = (val_count > WEAKEN_THRESHOLD) && intvars[level].isFixed();
			if (invert) {
				VarInfo vinfo(varinfo[level]);
				int lockval = vinfo.offset + (intvars[level].getVal() - vinfo.min);
				int vidx = vinfo.offset;
				int end = vinfo.offset + vinfo.dom;
				for (; vidx < end; vidx++) {
					vals[vidx].status = (vidx == lockval) ? VAL_WEAK : (VAL_LOCKED | VAL_WEAK);
				}
			}
#endif
			// Add any nodes along unlocked edges to the next level.
			for (; qhead < qnext; qhead++) {
				int nID = stateQ[qhead];
				Node& node(nodes[nID]);
				// Clear the status flags.
				node.status = 0;

				if (node.in_value + out_base[nID] > maxC) {
					continue;
				}
				for (int ei = 0; ei < node.out->sz; ei++) {
					int eid = node.out->edges[ei];
					Edge& e(edges[eid]);
					if ((vals[e.val].status & VAL_LOCKED) == 0U) {
						if (nodes[e.end].status == 0) {
							nodes[e.end].status = 1;
							stateQ.push(e.end);
							nodes[e.end].in_value = node.in_value + e.weight;
						} else {
							nodes[e.end].in_value = std::min(nodes[e.end].in_value, node.in_value + e.weight);
						}
					}
				}
			}
		}
		level++;
	}
}

void WMDDProp::collect_lits(vec<Lit>& expln) {
	// Determine the set of literals that must be included in the explanation.
	for (int vv = 0; vv < vals.size(); vv++) {
		Val& vinfo(vals[vv]);
#ifndef WEAKNOGOOD
		if (vinfo.status != 0U) {
			expln.push(intvars[vinfo.var].getLit(vinfo.val, LR_EQ));
			vinfo.status = 0;
		}
#else
		switch (vinfo.status) {
			case VAL_LOCKED:
				// vinfo.status is set to 2 if the literal is negated
				expln.push(intvars[vinfo.var].getLit(vinfo.val, LR_EQ));
				break;
			case VAL_WEAK:
				expln.push(intvars[vinfo.var].getLit(vinfo.val, LR_NE));
				break;
			default:
				break;
		}
		vinfo.status = 0;
#endif
	}
}

Clause* WMDDProp::explainConflict() {
	vec<Lit> expln;

#ifndef RELAX_UBC_LATER
	int maxC = mark_frontier(-1, -1);
#if 1
	if (maxC < INT_MAX) {
		expln.push(cost.getLit(maxC, LR_GE));
		maxC--;  // Force the assignment to be infeasible.
	}
#else
	maxC = cost.getMax();
	expln.push(cost.getMaxLit());
#endif

	minimize_expln(-1, -1, maxC);
	collect_lits(expln);
#else
	int currC = cost.getMax();
	mark_frontier(-1, -1);
	minimize_expln(-1, -1, currC);

	int maxC = late_minC(-1, -1);
	if (maxC < INT_MAX) {
		expln.push(cost.getLit(maxC, LR_GE));
	}
	collect_lits(expln);
#endif

	/*
	for(int vv = 0; vv < vals.size(); vv++)
		assert(vals[vv].status == 0);
	for(int nID = 1; nID < nodes.size(); nID++)
		assert(nodes[nID].status == 0);
		*/

	//  if(++count == 2)
	//    debugStateDot();

	Clause* r = Reason_new(expln.size());
	for (int ii = 0; ii < expln.size(); ii++) {
		(*r)[ii] = expln[ii];
	}

	return r;
}

Clause* WMDDProp::explain(Lit p, int inf) {
	// Backtrack to the correct time.
	/*
	Pinfo pi = p_info[inf];
	engine.btToPos(pi.btpos);
	int tag = pi.tag;
	*/
	int tag = inf;

	vec<Lit> expln;
	expln.push();

	if ((tag & 1) != 0) {
		if (opts.expl_alg == MDDOpts::E_GREEDY) {
			vec<int> upQ;
			nodes[T].status = (tag >> 1);
			assert(nodes[T].status > 0);
			assert(nodes[T].status <= nodes[T].in_pathC);
			upQ.push(T);
			incExplainUp(upQ, expln);
		} else {
			// Explaining lb(c) >= k
			int maxC = (tag >> 1) - 1;
			mark_frontier(-1, -1);
			minimize_expln(-1, -1, maxC);
			collect_lits(expln);
		}
	} else {
		int val = (tag >> 1);
		int var = vals[val].var;

		if (opts.expl_alg == MDDOpts::E_GREEDY) {
			return incExplain(p, var, val);
		}

#ifndef RELAX_UBC_LATER
		int maxC = mark_frontier(var, val);
#if 1
		if (maxC < INT_MAX) {
			expln.push(cost.getLit(maxC, LR_GE));
			maxC--;
		}
#else
		maxC = cost.getMax();
		expln.push(cost.getMaxLit());
#endif

		minimize_expln(var, val, maxC);
		collect_lits(expln);
#else
		// Relax ub(c) later.
		int currC = cost.getMax();
		mark_frontier(var, val);
		minimize_expln(var, val, currC);

		int maxC = late_minC(var, val);
		if (maxC < INT_MAX) {
			expln.push(cost.getLit(maxC, LR_GE));
		}
		collect_lits(expln);
#endif
	}

#ifdef DEBUG_EXPLN
	expln[0] = p;
	std::cout << expln << std::endl;
#endif

	if (opts.expl_strat == MDDOpts::E_KEEP) {
		expln[0] = p;
		Clause* c = Clause_new(expln, true);
		c->learnt = true;
		sat.addClause(*c);
		return c;
	}
	Clause* r = Reason_new(expln.size());
	for (int ii = 1; ii < expln.size(); ii++) {
		(*r)[ii] = expln[ii];
	}
	(*r)[0] = p;
	return r;
}

// Incremental explanation
// Starts at the set of edges to be explained, then
// walks only as far as is needed for the explanation.

// Precondition:
// For each node, in_pathC and out_pathC is correct,
// and status is 0.
// FIXME: We need to store the unconstrained (level 0)
//        cost to/from each node.
//        Currently assuming this is stored in in_value
//        and out_value.
Clause* WMDDProp::incExplain(Lit p, int var, int val) {
	// Check which set of edges we need to explain
	Val& vinfo(vals[val]);

	vec<Lit> expln;
	expln.push(p);
	expln.push(cost.getMaxLit());

	vec<int> upQ;
	vec<int> downQ;

	int minC = cost.getMax() + 1;
	for (int ei = 0; ei < vinfo.edges->sz; ei++) {
		EdgeID eid(vinfo.edges->edges[ei]);
		Edge& e(edges[eid]);

		// Compute the amount by which the original minimum cost must be exceeded.
		// NOTE: Assumes that inBase and outBase are smallish (not INT_MAX).
		int inBase = in_base[e.begin];
		int outBase = out_base[e.end];
		int surplus = minC - (inBase + outBase + e.weight);

		// If the edge was infeasible to begin with, ignore it.
		if (surplus <= 0) {
			continue;
		}

		// In our generated explanation, we need to maintain
		// the invariant that c(r, s) + w + c(s, T) > maxC.

		// Compute the minimum cost through the edge
		int inC = nodes[e.begin].in_pathC;
		int outC = nodes[e.end].out_pathC;

		// How  are we going to allocate the minC cost?
		int in_part = 0;
		int out_part = 0;
		if (inC == INT_MAX) {
			in_part = minC - (e.weight + outBase);
		} else if (outC == INT_MAX) {
			out_part = minC - (e.weight + inBase);
		} else {
			assert(inC + e.weight + outC >= minC);
			// Explain as much as possible in the upward pass.
			in_part = std::min(inC, minC - e.weight - outBase);
			// Then put the remaining slack into the downward pass.
			out_part = std::max(0, minC - e.weight - in_part);
		}
		assert(in_part >= 0);
		assert(out_part >= 0);
		if (in_part > inBase) {
			if (nodes[e.begin].status == 0) {
				upQ.push(e.begin);
			}
			nodes[e.begin].status = std::max(nodes[e.begin].status, in_part);
			assert(nodes[e.begin].status > 0);
		}
		if (out_part > outBase) {
			if (nodes[e.end].status == 0) {
				downQ.push(e.end);
			}
			nodes[e.end].status = std::max(nodes[e.end].status, out_part);
			assert(nodes[e.end].status > 0);
		}
	}

	incExplainUp(upQ, expln);
	incExplainDown(downQ, expln);

#ifdef DEBUG_EXPLN
	std::cout << expln << std::endl;
#endif

	if (opts.expl_strat == MDDOpts::E_KEEP) {
		expln[0] = p;
		Clause* c = Clause_new(expln, true);
		c->learnt = true;
		sat.addClause(*c);
		return c;
	}
	Clause* r = Reason_new(expln.size());
	for (int ii = 0; ii < expln.size(); ii++) {
		(*r)[ii] = expln[ii];
	}
	return r;
}

void WMDDProp::incExplainUp(vec<int>& upQ, vec<Lit>& expln) {
	vec<int> explVals;

	int qhead = 0;

	while (qhead < upQ.size()) {
		int qnext = qhead;

		// First scan, determine which values must remain
		// fixed.
		for (; qnext < upQ.size(); qnext++) {
			int nID(upQ[qnext]);
			Node& node(nodes[nID]);

			int node_minC = node.status;

			for (int ei = 0; ei < node.in->sz; ei++) {
				int eID(node.in->edges[ei]);
				Edge& e(edges[eID]);
				if (nodes[e.begin].in_pathC == INT_MAX) {
					continue;
				}
				if (nodes[e.begin].in_pathC + e.weight < node_minC) {
					// Including this edge could result in a feasible path
					// through some edge.
					if (vals[e.val].status == 0U) {
						assert(boolvars[e.val].isFalse());
						explVals.push(e.val);
						vals[e.val].status = 1;
					}
				}
			}
		}
		// Second scan; check which edges
		for (; qhead < qnext; qhead++) {
			int nID(upQ[qhead]);
			Node& node(nodes[nID]);

			int node_minC = node.status;

			for (int ei = 0; ei < node.in->sz; ei++) {
				int eID(node.in->edges[ei]);
				Edge& e(edges[eID]);

				// If the value is included in the explanation, ignore the edge.
				if (vals[e.val].status != 0U) {
					continue;
				}
				int dest_minC = node_minC - e.weight;

				// If the required cost is explained at the top level, ignore the edge.
				if (dest_minC <= in_base[e.begin]) {
					continue;
				}

				// If the node already has a greater required cost, no need to update it.
				if (dest_minC <= nodes[e.begin].status) {
					continue;
				}

				if (nodes[e.begin].status == 0) {
					upQ.push(e.begin);
				}
				nodes[e.begin].status = node_minC - e.weight;
				assert(nodes[e.begin].status > 0);
			}

			// Clear the status flag on node.
			node.status = 0;
		}
	}

	// Add the freshly fixed values to the explanation,
	// and reset the status flags.
	for (int vi = 0; vi < explVals.size(); vi++) {
		int vv = explVals[vi];
		Val& vinfo(vals[vv]);
		expln.push(intvars[vinfo.var].getLit(vinfo.val, LR_EQ));

		vinfo.status = 0;
	}
}

void WMDDProp::incExplainDown(vec<int>& downQ, vec<Lit>& expln) {
	vec<int> explVals;

	int qhead = 0;

	while (qhead < downQ.size()) {
		int qnext = qhead;

		// First scan, determine which values must remain
		// fixed.
		for (; qnext < downQ.size(); qnext++) {
			int nID(downQ[qnext]);
			Node& node(nodes[nID]);

			int node_minC = node.status;

			for (int ei = 0; ei < node.out->sz; ei++) {
				int eID(node.out->edges[ei]);
				Edge& e(edges[eID]);
				if (nodes[e.end].out_pathC == INT_MAX) {
					continue;
				}
				if (nodes[e.end].out_pathC + e.weight < node_minC) {
					// Including this edge could result in a feasible path
					// through some edge.
					if (vals[e.val].status == 0U) {
						assert(boolvars[e.val].isFalse());
						explVals.push(e.val);
						vals[e.val].status = 1;
					}
				}
			}
		}
		// Second scan; check which edges
		for (; qhead < qnext; qhead++) {
			int nID(downQ[qhead]);
			Node& node(nodes[nID]);

			int node_minC = node.status;

			bool flow = false;
			for (int ei = 0; ei < node.out->sz; ei++) {
				int eID(node.out->edges[ei]);
				Edge& e(edges[eID]);

				// If the value is included in the explanation, ignore the edge.
				if (vals[e.val].status != 0U) {
					flow = true;
					continue;
				}
				int dest_minC = node_minC - e.weight;

				// If the required cost is explained at the top level, ignore the edge.
				if (dest_minC <= out_base[e.end]) {
					continue;
				}

				flow = true;

				// If the node already has a greater required cost, no need to update it.
				if (dest_minC <= nodes[e.end].status) {
					continue;
				}

				if (nodes[e.end].status == 0) {
					downQ.push(e.end);
				}
				nodes[e.end].status = node_minC - e.weight;
				assert(nodes[e.end].status > 0);
			}
			assert(flow);

			// Clear the status flag on node.
			node.status = 0;
		}
	}

	// Add the freshly fixed values to the explanation,
	// and reset the status flags.
	for (int vi = 0; vi < explVals.size(); vi++) {
		int vv = explVals[vi];
		Val& vinfo(vals[vv]);
		expln.push(intvars[vinfo.var].getLit(vinfo.val, LR_EQ));

		vinfo.status = 0;
	}
}

// Output the current state of the graph
// in dot format.
void WMDDProp::debugStateDot() {
	printf("digraph ingraph { graph [ranksep=\"1.0 equally\"] \n");

	int nID = 1;

	while (nID < nodes.size()) {
		// Scan through the nodes in each level.
		int level = nodes[nID].var;
		for (; nID < nodes.size() && nodes[nID].var == level; nID++) {
			Node& node(nodes[nID]);

			//      printf("   { node [shape=record label=\"{<prefix>%d: (%d, %d) | {", nID,
			//      node.in_value, node.out_value);
			printf("   { node [shape=record label=\"{<prefix>%d: (%d, %d) | {", nID, node.in_pathC,
						 node.out_pathC);
			bool first = true;
			for (int ei = 0; ei < node.out->sz; ei++) {
				int eid = node.out->edges[ei];
				Edge& edge(edges[eid]);

				if (first) {
					first = false;
				} else {
					printf("|");
				}
				printf("<p%d>%d(%d)", eid, edge.val, edge.weight);
				if (boolvars[edge.val].isFalse()) {
					printf("X");
				}
			}
			printf("} }\"] %d };\n", nID);
		}
	}
	for (int eid = 0; eid < edges.size(); eid++) {
		printf("\t%d:p%d -> %d;\n", edges[eid].begin, eid, edges[eid].end);
	}
	printf("};\n");
}

// Ergh. It feels like I'm sort of triple-handling. Because we traverse the graph
// to extract the set of edges, and then traverse the edges to create the propagator.
// WARNING: At no point have we actually checked to ensure there aren't any long edges.
//          Or, indeed, that there aren't any repetitions or inversions in variable order.
WMDDProp* evgraph_to_wmdd(vec<IntVar*> _vs, IntVar* _cost, EVLayerGraph& g,
													EVLayerGraph::NodeID rootID, const MDDOpts& opts) {
	int nNodes = g.traverse(rootID);

	// Level for each node.
	vec<int> level;

	for (int ni = 0; ni < nNodes; ni++) {
		// We can't initialize the levels until we traverse.
		level.push(0);
	}

	// Traversal currently skips T.
	// Set up the level indicator.
	level[0] = _vs.size();

	// T is 0, root is 1.
	vec<Edge> edges;
	for (EVNode curr = g.travBegin(); curr != g.travEnd(); ++curr) {
		level[curr.id()] = curr.var();
		for (int ei = 0; ei < curr.size(); ei++) {
			EVEdge edge(curr[ei]);

			Edge e = {edge.val, edge.weight, curr.id(), edge.dest.id()};
			edges.push(e);
		}
	}

	// Set up the views.
	vec<IntView<> > vs;
	for (int i = 0; i < _vs.size(); i++) {
		_vs[i]->specialiseToEL();
	}
	for (int i = 0; i < _vs.size(); i++) {
		vs.push(IntView<>(_vs[i], 1, 0));
	}
	IntView<> cost(_cost, 1, 0);

	// Create the propagator.
	return new WMDDProp(vs, cost, level, edges, opts);
}
