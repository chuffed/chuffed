#include "chuffed/globals/tree.h"

#include "chuffed/branching/branching.h"
#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/core/propagator.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/core/sat.h"
#include "chuffed/globals/graph.h"
#include "chuffed/support/union_find.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/bool-view.h"
#include "chuffed/vars/vars.h"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <map>
#include <queue>
#include <stack>
#include <unordered_set>
#include <utility>
#include <vector>

/**
 *  Given a graph G, ensure its a tree.
 */

#define TREEPROP_DEBUG 0

/**
 * Detect that whe cannot reach some otehr node from 'node'
 * return true if no conflict, false otherwise (explanation built inside)
 */
bool TreePropagator::reachable(int node, std::vector<bool>& blue, bool doDFS) {
	if (doDFS) {
		blue = std::vector<bool>(nbNodes(), false);
		int count = 0;
		DFSBlue(node, blue, count);
	}
	for (int i = 0; i < nbNodes(); i++) {
		if (blue[i] == false && getNodeVar(i).isFixed() && getNodeVar(i).isTrue()) {
			if (so.lazy) {
				std::unordered_set<edge_id> badEdges;
				std::vector<bool> pink(nbNodes(), false);
				DFSPink(i, pink, blue, badEdges);
				// REASON: 0<i<n visited[i] /\ any-fixed-not-visited => fail

				vec<Lit> ps;
				assert(getNodeVar(node).isFixed());
				ps.push(getNodeVar(node).getValLit());
				std::unordered_set<edge_id>::iterator it;
				for (it = badEdges.begin(); it != badEdges.end(); ++it) {
					assert(getEdgeVar(*it).isFixed());
					ps.push(getEdgeVar(*it).getValLit());
				}
				assert(getNodeVar(i).isFixed());
				ps.push(getNodeVar(i).getValLit());
				Clause* expl = Clause_new(ps);
				expl->temp_expl = 1;
				sat.rtrail.last().push(expl);
				sat.confl = expl;
			}
			return false;
		}
		if (blue[i] == false && !getNodeVar(i).isFixed()) {
			Clause* r = nullptr;
			if (so.lazy) {
				std::unordered_set<edge_id> badEdges;
				std::vector<bool> pink(nbNodes(), false);
				DFSPink(i, pink, blue, badEdges);
				// REASON: 0<i<n visited[i] => unfixed-not-visited = false

				vec<Lit> ps;
				ps.push();
				assert(getNodeVar(node).isFixed());
				ps.push(getNodeVar(node).getValLit());
				std::unordered_set<edge_id>::iterator it;
				for (it = badEdges.begin(); it != badEdges.end(); ++it) {
					assert(getEdgeVar(*it).isFixed());
					ps.push(getEdgeVar(*it).getValLit());
				}
				r = Reason_new(ps);
			}
			// cout << "REACHABLE (N) "<<i<<endl;
			getNodeVar(i).setVal2(false, r);
			last_state_n[i] = VT_OUT;
		}
	}
	return true;
}

/**
 * Detect bridges and articulations and build them (with explanations)
 * return the number of bridges+articulations built
 */
int TreePropagator::articulations(int n, std::vector<bool>& reachable, int& count) {
	reachable = std::vector<bool>(nbNodes(), false);

	std::vector<int> parent(nbNodes(), -1);
	std::vector<int> depth(nbNodes(), -1);
	std::vector<int> low_(nbNodes(), -1);

	std::stack<node_id> hits;
	hits.push(-1);
	std::stack<edge_id> s;

	count = 0;

	std::vector<std::pair<edge_id, node_id> > tmpExpl;
	std::vector<partialExpl> bridgeExpl;
	std::vector<partialExpl> articuExpl;

	_findAndBuildBridges(n, count, s, depth.data(), low_.data(), reachable, parent.data(), hits,
											 tmpExpl, bridgeExpl, articuExpl);

	int nbBridgesBuilt = 0;

	bridgeExpl.insert(bridgeExpl.end(), articuExpl.begin(), articuExpl.end());

	std::map<node_id, node_id> memory;
	std::vector<int> toBePropagated(nbNodes(), -1);
	if (!bridgeExpl.empty()) {
		std::vector<partialExpl>::iterator it;
		for (it = bridgeExpl.begin(); it != bridgeExpl.end(); it++) {
			Clause* r = nullptr;
			int cause1 = it->cause1;
			int cause2 = it->cause2;
			int bridge = it->bridge;
			const bool isArt = bridge < 0;
			if (isArt) {
				bridge = -(bridge + 1);
			}

			if (isArt && !getNodeVar(bridge).setValNotR(true)) {
				continue;
			}
			if (!isArt && !getEdgeVar(bridge).setValNotR(true)) {
				toBePropagated[getEndnode(bridge, 0)] = bridge;
				toBePropagated[getEndnode(bridge, 1)] = bridge;
				// newFixedE.push(bridge);
				nbBridgesBuilt++;
				continue;
			}

			// Dont build articulations that are extremities of bridge
			// becasue the reason is worse than the reason in newEdge
			// UPDATE: just do it here....
			if (isArt && toBePropagated[bridge] != -1) {
				const int e = toBePropagated[bridge];
				const int a = bridge;
				Clause* r = nullptr;
				if (so.lazy) {
					vec<Lit> ps;
					ps.push();
					ps.push(getEdgeVar(e).getLit(true));
					r = Reason_new(ps);
				}
				// cout << "Arti (N) "<<a<<endl;
				getNodeVar(a).setVal2(true, r);
				last_state_n[a] = VT_IN;
				continue;
			}

			if (so.lazy) {
				std::vector<int> reasons;

				std::vector<bool> walk1(nbNodes(), false);
				walkIsland(cause1, walk1, bridge, isArt);
				std::vector<bool> walk2(nbNodes(), false);
				walkBrokenBridges(cause1, reachable, walk1, walk2, bridge, reasons, isArt);
				vec<Lit> ps;
				ps.push();
				if (!isTerminal[cause1]) {
					if (memory.find(cause1) == memory.end()) {
						struct CC cc;
						std::vector<bool> tmpV(nbNodes(), false);
						getCC(cause1, tmpV, &cc);
						int term = cause1;
						for (int tt = 0; tt < nbNodes(); tt++) {
							if (tmpV[tt] && isTerminal[tt]) {
								term = tt;
								break;
							}
						}
						memory[cause1] = term;
						cause1 = term;
					} else {
						cause1 = memory[cause1];
					}
				}
				if (!isTerminal[cause2]) {
					if (memory.find(cause2) == memory.end()) {
						struct CC cc;
						std::vector<bool> tmpV(nbNodes(), false);
						getCC(cause2, tmpV, &cc);
						int term = cause2;
						for (int tt = 0; tt < nbNodes(); tt++) {
							if (tmpV[tt] && isTerminal[tt]) {
								term = tt;
								break;
							}
						}
						memory[cause2] = term;
						cause2 = term;
					} else {
						cause2 = memory[cause2];
					}
				}
				assert(getNodeVar(cause1).isFixed());
				ps.push(getNodeVar(cause1).getValLit());
				assert(getNodeVar(cause2).isFixed());
				ps.push(getNodeVar(cause2).getValLit());
				for (const int reason : reasons) {
					assert(getEdgeVar(reason).isFixed());
					ps.push(getEdgeVar(reason).getValLit());
				}
				if (TREEPROP_DEBUG) {
					std::cout << "BRIDGE " << bridge << " caused by " << cause1 << " and " << cause2
										<< " and edges ";
					for (const int reason : reasons) {
						std::cout << reason << " ";
					}
					std::cout << '\n';
				}
				r = Reason_new(ps);
			}
			if (isArt) {
				// cout << "Bridge (N) "<<bridge<<endl;
				getNodeVar(bridge).setVal2(true, r);
				last_state_n[bridge] = VT_IN;
			} else {
				assert(!getEdgeVar(bridge).isFalse());
				if (TREEPROP_DEBUG) {
					std::cout << "BRIDGE " << bridge << '\n';
				}
				// cout << "Bridge (E) "<<bridge<<endl;
				getEdgeVar(bridge).setVal2(true, r);
				last_state_e[bridge] = VT_IN;
				moveInEdgeToFront(bridge);
				toBePropagated[getEndnode(bridge, 0)] = bridge;
				toBePropagated[getEndnode(bridge, 1)] = bridge;
				// newFixedE.push(bridge);
				nbBridgesBuilt++;
			}
		}
	}
	return nbBridgesBuilt;
}

/**
 * Detects a cycle involving 'edge'
 * return true if no conflict, false otherwise (explanation built inside)
 */
bool TreePropagator::cycle_detect(int edge) {
	const int u = getEndnode(edge, 0);
	const int v = getEndnode(edge, 1);

	if (uf.connected(u, v)) {
		std::vector<int> pathn = ruf.connectionsFromTo(u, v);
		// u and v where already connected thorugh pathn
		// This detects a new cycle created
		if (so.lazy) {
			vec<Lit> pathe;
			for (int k = 0; k < pathn.size() - 1; k++) {
				int t = findEdge(pathn[k], pathn[k + 1]);
				if (t < 0 || !getEdgeVar(t).isFixed() || getEdgeVar(t).isFalse()) {
					t = findEdge(pathn[k], pathn[k + 1], 1);
				}
				assert(getEdgeVar(t).isFixed());
				pathe.push(getEdgeVar(t).getValLit());
			}
			assert(getEdgeVar(edge).isFixed());
			pathe.push(getEdgeVar(edge).getValLit());
			Clause* expl = Clause_new(pathe);
			expl->temp_expl = 1;
			sat.rtrail.last().push(expl);
			sat.confl = expl;
		}
		return false;
	}
	return true;
}

/**
 * Detect a potential cycle involving 'unk_edge'
 * return true if no conflict, false otherwise (explanation built inside)
 */
void TreePropagator::precycle_detect(int unk_edge) {
	assert(!getEdgeVar(unk_edge).isFixed());

	const int u = getEndnode(unk_edge, 0);
	const int v = getEndnode(unk_edge, 1);

	if (uf.connected(u, v)) {
		std::vector<int> pathn = ruf.connectionsFromTo(u, v);
		Clause* r = nullptr;
		if (so.lazy) {
			vec<Lit> pathe;
			pathe.push();
			for (int k = 0; k < pathn.size() - 1; k++) {
				int t = findEdge(pathn[k], pathn[k + 1]);
				if (t < 0 || !getEdgeVar(t).isFixed() || getEdgeVar(t).isFalse()) {
					t = findEdge(pathn[k], pathn[k + 1], 1);
				}
				assert(getEdgeVar(t).isFixed());
				pathe.push(getEdgeVar(t).getValLit());
			}
			r = Reason_new(pathe);
		}

		if (TREEPROP_DEBUG) {
			std::cout << "PRECYCLE " << unk_edge << '\n';
		}
		// cout << "Precycle (E) "<<unk_edge<<endl;
		getEdgeVar(unk_edge).setVal2(false, r);
		last_state_e[unk_edge] = VT_OUT;
	}
}

/**
 * Union int he RerootedUnionFind
 */
void TreePropagator::unite(int u, int v) {
	assert(!uf.connected(u, v));
	if (!getNodeVar(u).isFixed()) {
		uf.unite(u, v);
		ruf.unite(u, v);
		assert(ruf.isRoot(v));
	} else {
		uf.unite(v, u);
		ruf.unite(v, u);
		assert(ruf.isRoot(u));
	}
}

void TreePropagator::_findAndBuildBridges(int u, int& count, std::stack<edge_id>& s, int depth[],
																					int low[], std::vector<bool>& visited, int parent[],
																					std::stack<node_id>& hits,
																					std::vector<std::pair<edge_id, node_id> >& semiExpl,
																					std::vector<partialExpl>& bridgeExpl,
																					std::vector<partialExpl>& articuExpl) {
	visited[u] = true;
	count++;
	depth[u] = count;
	low[u] = depth[u];

	// Detect a cause for bridge
	if (getNodeVar(u).isFixed() && getNodeVar(u).isTrue()) {
		hits.push(u);
	}
	const int prevHitsTop = hits.top();

	int topChangedTo = -1;

	for (int i = 0; i < adj[u].size(); i++) {
		const int e = adj[u][i];
		if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
			continue;
		}
		const int v = OTHER(getEndnode(e, 0), getEndnode(e, 1), u);
		if (!visited[v]) {
			s.push(e);
			parent[v] = u;

			// cout <<"taking edge "<<e<<endl;
			_findAndBuildBridges(v, count, s, depth, low, visited, parent, hits, semiExpl, bridgeExpl,
													 articuExpl);

			if (!getNodeVar(u).isFixed() && hits.top() != prevHitsTop) {
				// always prefer terminals, explanations witht hem will eb mroe reusable
				if (topChangedTo == -1 || isTerminal[topChangedTo]) {
					topChangedTo = hits.top();
				}
			}

			if (low[v] >= depth[u]) {  // u is articulation
				edge_id e2 = -1;
				int cnt = 0;
				do {
					e2 = s.top();
					s.pop();
					cnt++;
				} while (e2 != e);

				if (prevHitsTop != hits.top()) {
					// Bridge
					if (cnt == 1 && !getEdgeVar(e2).isFixed()) {
						semiExpl.emplace_back(e2, hits.top());
						// cout <<"BRIDGE"<<e2<<endl;
					}
					if (!getNodeVar(u).isFixed()) {
						// Articulation
						// negative - 1 means articulation, > 0 means bridge
						semiExpl.emplace_back(-u - 1, hits.top());
					}
				}
			}
			while (hits.top() != prevHitsTop) {
				hits.pop();
			}

			low[u] = std::min(low[u], low[v]);
		} else if (parent[u] != v && depth[v] < depth[u]) {
			// e is a backedge from u to its ancestor v
			s.push(e);
			low[u] = std::min(low[u], depth[v]);
		}
	}

	if (getNodeVar(u).isFixed() && getNodeVar(u).getVal() == 1) {
		while (hits.top() != u) {
			hits.pop();
		}
		for (auto& i : semiExpl) {
			partialExpl pE;
			pE.bridge = i.first;
			pE.cause1 = i.second;
			pE.cause2 = u;
			if (pE.bridge > 0) {
				bridgeExpl.push_back(pE);
			} else {
				articuExpl.push_back(pE);
			}
		}
		semiExpl.clear();
	} else {
		if (topChangedTo != -1) {
			hits.push(topChangedTo);
		}
	}
}

/**
 * Edge between u and v if any (-1 if does not exist)
 **/
edge_id TreePropagator::findEdge(int u, int v, int idx) {
	if (u > v) {  // If I only read one, I only need to update one...
		const int tmp = u;
		u = v;
		v = tmp;
	}
	if (nodes2edge[u][v].size() <= idx) {
		return -1;
	}
	return nodes2edge[u][v][idx];
}

void TreePropagator::moveInEdgeToFront(int e) {
	int u = getEndnode(e, 0);
	int v = getEndnode(e, 1);
	if (u > v) {  // If I only read one, I only need to update one...
		const int tmp = u;
		u = v;
		v = tmp;
	}
	int i = 0;
	for (i = 0; i < nodes2edge[u][v].size(); i++) {
		if (nodes2edge[u][v][i] == e) {
			break;
		}
	}
	assert(i < nodes2edge[u][v].size());

	const int tmp = nodes2edge[u][v][0];
	nodes2edge[u][v][0] = nodes2edge[u][v][i];
	nodes2edge[u][v][i] = tmp;
}

std::vector<TreePropagator*> TreePropagator::tree_propagators = std::vector<TreePropagator*>();

TreePropagator::TreePropagator(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _adj,
															 vec<vec<int> >& _en)
		: GraphPropagator(_vs, _es, _en),
			uf(_vs.size()),
			ruf(_vs.size()),
			nb_innodes(0),
			nb_avn(nbNodes()) {
	tree_propagators.push_back(this);

	isTerminal = new bool[nbNodes()];
	for (int i = 0; i < nbNodes(); i++) {
		isTerminal[i] = getNodeVar(i).isFixed() && getNodeVar(i).isTrue();
		if (isTerminal[i]) {
			nb_innodes++;
		}
		if (getNodeVar(i).isFixed() && getNodeVar(i).isFalse()) {
			nb_avn--;
		}
	}

	adj = std::vector<std::vector<int> >(_adj.size(), std::vector<int>());
	for (int i = 0; i < _adj.size(); i++) {
		for (int j = 0; j < _adj[i].size(); j++) {
			adj[i].push_back(_adj[i][j]);
		}
	}

	nodes2edge = std::vector<std::vector<std::vector<int> > >(nbNodes());
	for (int i = 0; i < nbNodes(); i++) {
		nodes2edge[i] = std::vector<std::vector<int> >(nbNodes(), std::vector<int>());
	}
	for (unsigned int e = 0; e < nbEdges(); e++) {
		nodes2edge[getEndnode(e, 0)][getEndnode(e, 1)].push_back(e);
		nodes2edge[getEndnode(e, 1)][getEndnode(e, 0)].push_back(e);
	}

	// Attach to all the vertices lower and upper bound changes
	for (int i = 0; i < nbNodes(); i++) {
		getNodeVar(i).attach(this, i, EVENT_LU);
	}

	// Attach to all edges. they are identified by a number higher
	// than nbNodes()
	for (int j = 0; j < nbEdges(); j++) {
		getEdgeVar(j).attach(this, nbNodes() + j, EVENT_LU);
	}

	newFixedE.clear();
	newFixedN.clear();
	newNodeCompleteCheckup = true;
	newNodeCompleteCheckup_Count = 0;
	in_edges_tsize = 0;
	in_edges_size = 0;

	last_state_n.resize(nbNodes());
	for (int i = 0; i < nbNodes(); i++) {
		last_state_n[i] = UNK;
	}
	last_state_e.resize(nbEdges());
	for (int i = 0; i < nbEdges(); i++) {
		last_state_e[i] = UNK;
	}
}

TreePropagator::~TreePropagator() { delete[] isTerminal; }

void TreePropagator::wakeup(int i, int /*c*/) {
	if (TREEPROP_DEBUG) {
		std::cout << "Wakeup" << '\n';
		std::cout << __FILE__ << " " << __LINE__ << " i " << i << '\n';
		std::cout << "event fix" << '\n';
	}
	// Check it's an event on edges
	if (i >= nbNodes() && i < nbNodes() + nbEdges()) {
		// EVENT ON EDGES
		const int j = i - nbNodes();
		if (last_state_e[j] != UNK) {
			return;
		}
		if (TREEPROP_DEBUG) {
			std::cout << __FILE__ << " " << __LINE__ << " edge " << j << " esvalue "
								<< getEdgeVar(j).getVal() << '\n';
		}
		newFixedE.insert(j);
	} else if (i >= 0 && i < nbNodes()) {
		// EVENT ON NODES
		if (last_state_n[i] != UNK) {
			return;
		}
		if (TREEPROP_DEBUG) {
			std::cout << __FILE__ << " " << __LINE__ << " vsvalue " << getNodeVar(i).getVal() << '\n';
		}
		newFixedN.insert(i);
	}

	pushInQueue();
}

bool TreePropagator::propagate() {
	if (in_edges_tsize < in_edges_size) {
		in_edges.resize(in_edges_tsize);
		in_edges_size = in_edges_tsize;
	}

	std::unordered_set<int>::iterator it;
	for (it = newFixedE.begin(); it != newFixedE.end(); ++it) {
		const int j = *it;  // newFixedE[i];
		if (getEdgeVar(j).isTrue()) {
			if (!propagateNewEdge(j)) {
				return false;
			}
		} else {
			if (!propagateRemEdge(j)) {
				return false;
			}
		}
	}

	for (it = newFixedN.begin(); it != newFixedN.end(); ++it) {
		const int j = *it;  // newFixedN[i];
		if (!isTerminal[j]) {
			nb_innodes = nb_innodes + ((getNodeVar(j).isTrue()) ? 1 : 0);
		}
		if (getNodeVar(j).isTrue()) {
			if (!propagateNewNode(j)) {
				return false;
			}
		} else {
			if (!propagateRemNode(j)) {
				nb_avn--;
				return false;
			}
		}
	}

	/*for (int i = 0; i < nbNodes(); i++) {
			if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue()) {
					bool blue[nbNodes()];
					if(!reachable(i,blue,true))
							return false;
			}
			}*/

	return true;
}

// Walks only on fixed edges == 1
void TreePropagator::getCC(int node, std::vector<bool>& visited, CC* cc) {
	visited[node] = true;
	cc->count++;
	cc->nodesIds.push_back(node);

	for (int i = 0; i < adj[node].size(); i++) {
		const int e = adj[node][i];
		if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
			const int other = OTHER(getEndnode(e, 0), getEndnode(e, 1), node);
			if (!visited[other]) {
				getCC(other, visited, cc);
			}
		}
	}
}

bool TreePropagator::propagateNewNode(int node) {
	/*
		//Moved to minimum_weight_tree.c: 1) Steiner Node
		2) Articulations/Bridges
		3) Pre-cycle detect
		4) Reachable
	 */

	std::vector<bool> blue(nbNodes());
	bool didBlueDFS = false;
	const int& count = newNodeCompleteCheckup_Count;
	if (newNodeCompleteCheckup) {
		articulations(node, blue, newNodeCompleteCheckup_Count);
		didBlueDFS = true;
		newNodeCompleteCheckup = false;
	}

	// See if the new node is bringing a potential cycle
	for (int i = 0; i < adj[node].size(); i++) {
		const int e = adj[node][i];
		if (getEdgeVar(e).isFixed()) {
			continue;
		}
		const int other = OTHER(getEndnode(e, 0), getEndnode(e, 1), node);
		if (!getNodeVar(other).isFixed() || getNodeVar(other).isFalse()) {
			continue;
		}

		precycle_detect(e);
	}

	// assert(count != 0);
	assert(nb_innodes > 0);
	if (count < nb_innodes) {
		if (!reachable(node, blue, !didBlueDFS)) {
			return false;
		}
	}

	return true;
}

bool TreePropagator::propagateRemNode(int node) {
	/*
		1) Coherence
	 */
	std::vector<edge_id> remvd_e;
	const bool ok = coherence_outedges(node, remvd_e);
	newFixedE.insert(remvd_e.begin(), remvd_e.end());
	return ok;  // GraphPropagator::coherence_outedges(node);
}

bool TreePropagator::propagateNewEdge(int edge) {
	/*
		1) Cycle detection
		2) Union
		3) Coherence
		4) Pre-cycle detect
	 */
	in_edges.push_back(edge);
	in_edges_tsize = in_edges.size();
	in_edges_size = in_edges.size();

	if (!cycle_detect(edge)) {
		return false;
	}

	const int u = getEndnode(edge, 0);
	const int v = getEndnode(edge, 1);
	unite(u, v);

	if (!GraphPropagator::coherence_innodes(edge)) {
		return false;
	}

	// Put the new edge int he first position of nodes2edge so it can be faster
	//  to walk through in-edges for cycle detection:
	moveInEdgeToFront(edge);

	// Doesn't make much difference in number of nodes but is good
	// Remove possible cycles
	std::unordered_set<edge_id> unk;
	std::vector<bool> blue(nbNodes(), false);
	getUnkEdgesInCC(u, blue, unk);
	auto it = unk.begin();
	for (; it != unk.end(); ++it) {
		if (blue[getEndnode(*it, 0)] && blue[getEndnode(*it, 1)]) {
			precycle_detect(*it);
		}
	}
	//*/

	return true;
}

bool TreePropagator::propagateRemEdge(int edge) {
	/*
		0) Detect node of degree 0 (fast Reachable)
		1) Articulations
		2) Reachable
		//Moved to minimum_weight_tree.c: 3) Steiner Node
	 */

	// Detect if we leave a node of degree 0
	for (int i = 0; i < 2; i++) {
		const int node = getEndnode(edge, i);

		// count the number of edges still connecting this node
		int degree = 0;
		for (const int e : adj[node]) {
			if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isTrue()) {
				degree++;
			}
		}

		if (degree == 0) {  // The node is left all alone
			// If the node is == 1 and there are more nodes,
			// we are creating an unreachable node...
			if (getNodeVar(node).isFixed() && getNodeVar(node).isTrue()) {
				if (nb_innodes > 1) {
					int unreachableNodeIn = -1;
					for (int k = 0; k < nbNodes(); k++) {
						if (node == k) {
							continue;
						}
						if (getNodeVar(k).isFixed() && getNodeVar(k).isTrue()) {
							unreachableNodeIn = k;
							break;
						}
					}
					assert(unreachableNodeIn != -1);

					// We fail because unreachableNodeIn is unreachable
					if (so.lazy) {
						vec<Lit> ps;
						// node == 1 /\unrechableNodeIn == 1
						//           /\ \forall e in adj[node] e == false
						assert(getNodeVar(node).isFixed());
						ps.push(getNodeVar(node).getValLit());
						assert(getNodeVar(unreachableNodeIn).isFixed());
						ps.push(getNodeVar(unreachableNodeIn).getValLit());

						for (const int k : adj[node]) {
							assert(getEdgeVar(k).isFixed());
							ps.push(getEdgeVar(k).getValLit());
						}

						Clause* expl = Clause_new(ps);
						expl->temp_expl = 1;
						sat.rtrail.last().push(expl);
						sat.confl = expl;
					}
					return false;
				}
			} else if (!getNodeVar(node).isFixed()) {
				// The node is not forced in, but if we force it in
				// given the current edges, we would fail as above,
				// so we force it out
				if (nb_innodes >= 1) {
					int unreachableNodeIn = -1;
					for (int k = 0; k < nbNodes(); k++) {
						if (node == k) {
							continue;
						}
						if (getNodeVar(k).isFixed() && getNodeVar(k).isTrue()) {
							unreachableNodeIn = k;
							break;
						}
					}
					assert(unreachableNodeIn != -1);  // There is anothe node in
					// node is in at the same time as another node (we chose one)

					Clause* r = nullptr;
					if (so.lazy) {
						vec<Lit> ps;
						ps.push();
						assert(getNodeVar(unreachableNodeIn).isFixed());
						ps.push(getNodeVar(unreachableNodeIn).getValLit());
						for (const int k : adj[node]) {
							assert(getEdgeVar(k).isFixed());
							ps.push(getEdgeVar(k).getValLit());
						}
						r = Reason_new(ps);
					}
					// cout << "RemEdge (N) "<<node<<endl;
					getNodeVar(node).setVal2(false, r);
					last_state_n[node] = VT_OUT;
					// newFixedN.push(node);
				}
			}
		}
	}

	// Look for new bridges that may be appearing now that you removed
	// this edge.

	if (nb_innodes <= 1) {
		return true;
	}

	// for (int i = 0 ; i < 2; i++){
	//     int node = getEndnode(edge,i);

	int node = 0;
	for (int i = 0; i < nbNodes(); i++) {
		if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue()) {
			node = i;
			break;
		}
	}
	// if (!getNodeVar(node).isFixed() || getNodeVar(node).isFalse())
	//     continue;

	std::vector<bool> blue(nbNodes());
	bool didBlueDFS = false;
	const int& count = newNodeCompleteCheckup_Count;
	if (newNodeCompleteCheckup) {
		articulations(node, blue, newNodeCompleteCheckup_Count);
		didBlueDFS = true;
		newNodeCompleteCheckup = false;
	}
	assert(nb_avn > 0);

	if (count < nb_avn) {
		if (!reachable(node, blue, !didBlueDFS)) {
			return false;
		}
	}

	//}

	return true;
}

void TreePropagator::clearPropState() {
	if (TREEPROP_DEBUG) {
		std::cout << " clear prop state" << '\n';
	}

	GraphPropagator::clearPropState();
	newFixedN.clear();
	newFixedE.clear();
	newNodeCompleteCheckup = true;
	newNodeCompleteCheckup_Count = 0;

	if (TREEPROP_DEBUG) {
		std::cout << " clear prop state end" << '\n';
	}
}

void TreePropagator::getUnkEdgesInCC(int r, std::vector<bool>& visited,
																		 std::unordered_set<edge_id>& unk) {
	visited[r] = true;
	for (int i = 0; i < adj[r].size(); i++) {
		const int e = adj[r][i];
		if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
			continue;
		}
		if (!getEdgeVar(e).isFixed()) {
			unk.insert(e);
			continue;
		}
		const int other = getEndnode(e, 0) == r ? getEndnode(e, 1) : getEndnode(e, 0);
		if (visited[other]) {
			continue;
		}
		getUnkEdgesInCC(other, visited, unk);
	}
}

/**
 * Goes through in and unknown edges.
 */
void TreePropagator::DFSBlue(int r, std::vector<bool>& visited, int& count) {
	visited[r] = true;
	count++;
	for (int i = 0; i < adj[r].size(); i++) {
		const int e = adj[r][i];
		if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
			continue;
		}
		const int e1 = getEndnode(e, 1);
		const int e0 = getEndnode(e, 0);
		const int other = e0 == r ? e1 : e0;
		if (getNodeVar(other).isFixed() && getNodeVar(other).isFalse()) {
			continue;
		}
		if (visited[other] == false) {
			DFSBlue(other, visited, count);
		}
	}
}

/**
 * Goes through all edges until it hits a 'blue' node.
 * badEdges is the set of edges with one node pink and one node blue.
 */
void TreePropagator::DFSPink(int r, std::vector<bool>& visited, std::vector<bool>& blue,
														 std::unordered_set<edge_id>& badEdges) {
	visited[r] = true;
	for (int i = 0; i < adj[r].size(); i++) {
		const int e = adj[r][i];
		const int e1 = getEndnode(e, 1);
		const int e0 = getEndnode(e, 0);
		const int other = e0 == r ? e1 : e0;
		if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
			if (blue[other]) {
				badEdges.insert(e);
				continue;
			}
		} else if (blue[other]) {
			continue;
		}
		if (visited[other] == false) {
			DFSPink(other, visited, blue, badEdges);
		}
	}
}

/**
 * Goes through in and unkown edges. Avoid 'avoidBridge'
 */
void TreePropagator::walkIsland(int r, std::vector<bool>& visited, int avoidBridge, bool isArt,
																int parent) {
	// cout << "Walking my island.... :" << r<<endl;
	visited[r] = true;

	for (int i = 0; i < adj[r].size(); i++) {
		const int e = adj[r][i];
		const int e1 = getEndnode(e, 1);
		const int e0 = getEndnode(e, 0);
		const int other = e0 == r ? e1 : e0;
		if (isArt && other == avoidBridge) {
			continue;
		}
		if (!isArt && e == avoidBridge) {
			continue;
		}
		if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isTrue()) {
			if (other == parent) {
				continue;
			}
			if (!visited[other]) {
				walkIsland(other, visited, avoidBridge, isArt, r);
			}
		}
	}
}

/**
 * Goes through all edges. Avoid 'avoidBridge'
 * Bridges is the seat of edges that could bring us from visited to a
 * walked and reachable node.
 */
void TreePropagator::walkBrokenBridges(int r, std::vector<bool>& reachable,
																			 std::vector<bool>& walked, std::vector<bool>& visited,
																			 int avoidBridge, std::vector<edge_id>& bridges, bool isArt,
																			 int parent) {
	// cout << "Walking my island again.... :" << r<<" "<<avoidBridge<<endl;
	visited[r] = true;
	for (int i = 0; i < adj[r].size(); i++) {
		const int e = adj[r][i];
		const int e1 = getEndnode(e, 1);
		const int e0 = getEndnode(e, 0);
		const int other = e0 == r ? e1 : e0;
		if (isArt && other == avoidBridge) {
			continue;
		}
		if (!isArt && e == avoidBridge) {
			continue;
		}
		if (other == parent) {
			continue;
		}
		if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
			// cout << other<<" "<<reachable[other] <<" "<< walked[other]<<endl;
			if (reachable[other] && !walked[other] && !visited[other]) {
				bridges.push_back(e);
				continue;
			}
		}
		if (!visited[other]) {
			walkBrokenBridges(other, reachable, walked, visited, avoidBridge, bridges, isArt, r);
		}
	}
}

bool TreePropagator::checkFinalSatisfied() {
	// cout<<all_to_dot()<<endl;
	std::stack<node_id> s;
	for (int i = 0; i < nbNodes(); i++) {
		if (getNodeVar(i).isTrue()) {
			s.push(i);
			break;
		}
	}
	std::vector<bool> vis = std::vector<bool>(nbNodes(), false);
	std::vector<int> par = std::vector<int>(nbNodes(), -1);
	while (!s.empty()) {
		const int curr = s.top();
		s.pop();
		vis[curr] = true;
		for (unsigned int i = 0; i < adj[curr].size(); i++) {
			const int e = adj[curr][i];
			if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isFalse()) {
				continue;
			}
			const int o = getOtherEndnode(e, curr);
			if (par[curr] == o || o == curr) {
				continue;
			}
			if (!vis[o]) {
				par[o] = curr;
				s.push(o);
			} else {
				std::cerr << "TreePropagator not satisfied " << __FILE__ << ":" << __LINE__ << '\n';
				if (DEBUG) {
					std::cout << "Edges in: ";
					for (int i = 0; i < nbEdges(); i++) {
						if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) {
							std::cout << i << " ";
						}
					}
					std::cout << '\n';
				}
				assert(false);
				return false;
			}
		}
	}
	return true;
}

void tree(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _adj, vec<vec<int> >& _en) {
	auto* t = new TreePropagator(_vs, _es, _adj, _en);
	// if (so.check_prop)
	//     engine.propagators.push(t);
}

void connected(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _adj,
							 vec<vec<int> >& _en) {
	auto* t = new ConnectedPropagator(_vs, _es, _adj, _en);
	// if (so.check_prop)
	//     engine.propagators.push(t);
}

class PrimStrategy : public BranchGroup {
	std::vector<std::vector<int> > dist;
	std::vector<std::vector<bool> > inf;
	std::vector<std::vector<std::vector<std::pair<int, int> > > > leaving_cc;
	std::vector<std::vector<std::vector<int> > > border_cc;

public:
	PrimStrategy(vec<Branching*>& _x, VarBranch vb, bool t) : BranchGroup(_x, vb, t) {}

	void compute_dists() {
		TreePropagator* p = TreePropagator::tree_propagators[0];
		dist = std::vector<std::vector<int> >(p->nbNodes(), std::vector<int>(p->nbNodes(), -1));
		inf = std::vector<std::vector<bool> >(p->nbNodes(), std::vector<bool>(p->nbNodes(), false));
		for (int i = 0; i < p->nbNodes(); i++) {
			for (int j = 0; j < p->nbNodes(); j++) {
				dist[i][j] = 0;
				inf[i][j] = (i != j);  // is infinite
			}
		}
		for (int edge = 0; edge < p->nbEdges(); edge++) {
			const int from = p->getEndnode(edge, 0);
			const int to = p->getEndnode(edge, 1);
			dist[from][to] = 1;
			inf[from][to] = false;
			dist[to][from] = 1;
			inf[to][from] = false;
		}
		for (int k = 0; k < p->nbNodes(); k++) {
			for (int i = 0; i < p->nbNodes(); i++) {
				for (int j = 0; j < p->nbNodes(); j++) {
					if ((inf[i][j] || dist[i][j] > dist[i][k] + dist[k][j]) && !inf[i][k] && !inf[k][j]) {
						dist[i][j] = dist[i][k] + dist[k][j];
						inf[i][j] = false;
					}
				}
			}
		}
	}

	void connected_components() {
		leaving_cc.clear();
		border_cc.clear();
		for (auto* p : TreePropagator::tree_propagators) {
			leaving_cc.emplace_back();
			border_cc.emplace_back();
			const int last_t = leaving_cc.size() - 1;
			std::vector<bool> visited = std::vector<bool>(p->nbNodes(), false);
			for (int n = 0; n < p->nbNodes(); n++) {
				if (!p->getNodeVar(n).isFixed() || p->getNodeVar(n).isFalse()) {
					continue;
				}
				// n is mand
				if (!visited[n]) {
					leaving_cc[last_t].emplace_back();
					border_cc[last_t].emplace_back();
					const int last_cc = leaving_cc[last_t].size() - 1;
					std::queue<int> q;
					q.push(n);
					while (!q.empty()) {
						const int c = q.front();
						q.pop();
						visited[c] = true;
						const std::vector<int> adj = p->getAdjacentEdges(c);
						for (const int e : adj) {
							if (!p->getEdgeVar(e).isFixed()) {
								leaving_cc[last_t][last_cc].emplace_back(e, p->getOtherEndnode(e, c));
								if (border_cc[last_t][last_cc].empty() || border_cc[last_t][last_cc].back() != c) {
									border_cc[last_t][last_cc].push_back(c);
								}
							} else if (p->getEdgeVar(e).isTrue() && !visited[p->getOtherEndnode(e, c)]) {
								q.push(p->getOtherEndnode(e, c));
							}
						}
					}
				}
			}
		}
	}

	bool finished() override {
		if (fin != 0) {
			return true;
		}
		for (int i = 0; i < x.size(); i++) {
			if (!x[i]->finished()) {
				return false;
			}
		}
		fin = 1;
		return true;
	}

	DecInfo* branch() override {
		assert(!TreePropagator::tree_propagators.empty());

		if (dist.empty()) {
			compute_dists();
		}

		connected_components();
		/*cout<<"Trees: "<<leaving_cc.size()<<endl;
		for (unsigned int i = 0; i < leaving_cc.size(); i++) {
				cout<<"CCs in "<<i<<" "<<leaving_cc[i].size()<<endl;
				for (unsigned int j = 0; j < leaving_cc[i].size(); j++) {
						cout<<"CC "<< j<<endl;
						for (unsigned int k = 0; k < leaving_cc[i][j].size(); k++) {
								cout<<"   "<<leaving_cc[i][j][k].first<<" "<< leaving_cc[i][j][k].second<<endl;
						}
				}
				}*/

		int min_t = -1;
		int min_e = -1;
		int min_h = -1;
		int min_d = -1;

		for (unsigned int i = 0; i < leaving_cc.size(); i++) {
			// For each tree...

			for (unsigned int cc1 = 0; cc1 < leaving_cc[i].size(); cc1++) {
				for (unsigned int cc2 = 0; cc2 < leaving_cc[i].size(); cc2++) {
					if (cc2 == cc1) {
						continue;
					}
					for (unsigned int l1 = 0; l1 < leaving_cc[i][cc1].size(); l1++) {
						for (unsigned int b2 = 0; b2 < border_cc[i][cc2].size(); b2++) {
							const int h1 = leaving_cc[i][cc1][l1].second;
							const int h2 = border_cc[i][cc2][b2];
							if (inf[h1][h2]) {
								continue;
							}
							const int d = dist[h1][h2];
							if (min_d == -1 || min_d > d) {
								min_t = i;
								min_e = leaving_cc[i][cc1][l1].first;
								min_h = h1;
								min_d = d;
							} else if (min_d == d) {
								// Prefer one that goes to a mandatory node
								const int e = leaving_cc[i][cc1][l1].first;
								const int h = TreePropagator::tree_propagators[i]->getEndnode(e, 0);
								const int t = TreePropagator::tree_propagators[i]->getEndnode(e, 1);
								if (TreePropagator::tree_propagators[i]->getNodeVar(h).isFixed() &&
										TreePropagator::tree_propagators[i]->getNodeVar(t).isFixed()) {
									min_t = i;
									min_e = leaving_cc[i][cc1][l1].first;
									min_h = h1;
									min_d = d;
								}
							}
						}
					}
				}
			}
			/*for (unsigned int cc1 = 0; cc1 < leaving_cc[i].size(); cc1++) {
					for (unsigned int cc2 = 0; cc2 < leaving_cc[i].size(); cc2++) {
							if (cc2 == cc1) continue;
							for (unsigned int l1 = 0; l1 < leaving_cc[i][cc1].size(); l1++) {
									for (unsigned int l2 = l1+1; l2 < leaving_cc[i][cc2].size(); l2++) {
											int h1 = leaving_cc[i][cc1][l1].second;
											int h2 = leaving_cc[i][cc2][l2].second;
											if (inf[h1][h2]) continue;
											int d = dist[h1][h2];
											if (min_d == -1 || min_d > d) {
													min_t = i;
													min_e = leaving_cc[i][cc1][l1].first;
													min_h = h1;
													min_d = d;
											} else if ( min_d == d) {
													//Prefer one that goes to a mandatory node
													int e = leaving_cc[i][cc1][l1].first;
													int h = TreePropagator::tree_propagators[i]->getEndnode(e,0);
													int t = TreePropagator::tree_propagators[i]->getEndnode(e,1);
													if (TreePropagator::tree_propagators[i]->getNodeVar(h).isFixed() &&
															TreePropagator::tree_propagators[i]->getNodeVar(t).isFixed()) {
															min_t = i;
															min_e = leaving_cc[i][cc1][l1].first;
															min_h = h1;
															min_d = d;
													}
											}
									}
							}
					}
					}*/
		}
		const int arg_min = min_t * TreePropagator::tree_propagators[0]->nbEdges() + min_e;
		if (false && arg_min >= 0) {
			std::cout << "Tree " << min_t << " taking "
								<< TreePropagator::tree_propagators[0]->getEndnode(min_e, 0) << " "
								<< TreePropagator::tree_propagators[0]->getEndnode(min_e, 1) << " " << min_d
								<< '\n';
		}
		// cout<<min_t<<" "<<arg_min<<endl;

		/*
		int arg_min = -1;

		for (unsigned int i = 0; i < TreePropagator::tree_propagators.size(); i++) {
				TreePropagator* p = TreePropagator::tree_propagators[i];
				for (int n = 0; n < p->nbNodes(); n++) {
						if (!p->getNodeVar(n).isFixed() || p->getNodeVar(n).isFalse())
								continue;
						vector<int> adj = p->getAdjacentEdges(n);
						for (int j = 0; j < adj.size(); j++) {
								int e = adj[j];
								if (x[e]->finished())
										continue;
								if (arg_min == -1) {
										arg_min = e;
								}
						}
				}
				}*/
		if (arg_min < 0) {
			if (!finished()) {
				for (int i = 0; i < x.size(); i++) {
					if (!x[i]->finished()) {
						return new DecInfo(x[i], 0, 1);
					}
				}
			}
			return nullptr;
		}
		assert(!x[arg_min]->finished());
		return new DecInfo(x[arg_min], 1, 1);  // o is at the next position

		assert(finished());
		return nullptr;
	}
};
