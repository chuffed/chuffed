#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/core/propagator.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/core/sat.h"
#include "chuffed/globals/tree.h"
#include "chuffed/support/misc.h"
#include "chuffed/support/union_find.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/bool-view.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/vars.h"

#include <cassert>
#include <climits>
#include <cstring>
#include <iostream>
#include <queue>
#include <unordered_set>
#include <utility>
#include <vector>

#define CPLEX_AVAILABLE 0
#define LEMON_AVAILABLE 0
#if CPLEX_AVAILABLE && LEMON_AVAILABLE
#include <ilcplex/cplex.h>
#include <lemon/edmonds_karp.h>
#include <lemon/list_graph.h>
#endif

/**
 * Given a graph G and a set of nodes V,
 * find a subgraph T of G that is a tree.
 * And spans all nodes in V (at least).
 * It is NOT an MST because no need to span all
 * the nodes of G, so the lower bound is different.
 */

#define TREEPROP_DEBUG 0

//*
// This version needs to work in conjucntion with a TreePropagator
// It won't do the propagations of treeness, only inherits from it
// to avoid replicating code
class IncrementalMinimumWTreePropagator : public TreePropagator {
protected:
	vec<int> weights;
	Tint mw;
	Tint splb;

	std::vector<Tint> spTo;  // To whom is this the shortest path
	std::vector<Tint> spC;   // What is the cost of it

	std::vector<std::vector<Tint>> eInSP;  // eInSP[n][e] <=> e is in the sp from n to anyone

	std::vector<Tint> e_already_counted;
	std::vector<Tint> n_already_counted;
	vec<Lit> explvf;
	vec<Lit> explvp;
	Tint explv_sz;
	Tint ccs;

	Tint specialtint;

	bool verify_state() {
		int ccc = 0;
		for (int i = 0; i < nbNodes(); i++) {
			if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() && uf.find(i) == i) {
				ccc++;
			}
		}
		if (ccc != ccs) {
			uf.print();
			for (int i = 0; i < nbNodes(); i++) {
				if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue()) {
					std::cout << i << " ";
				}
			}
			std::cout << '\n';
			for (int i = 0; i < nbNodes(); i++) {
				if (spC[i] != -1) {
					std::cout << i << " ";
				}
			}
			std::cout << '\n';
			std::cout << ccc << " " << ccs << '\n';
		}
		assert(ccc == ccs);
		for (int i = 0; i < nbNodes(); i++) {
			if (!getNodeVar(i).isFixed() || getNodeVar(i).isFalse()) {
				assert(uf.find(i) == i);
			} else {
				assert(getNodeVar(i).isTrue());
				if (uf.find(i) == i) {
					if (ccs > 1) {
						if (!(spC[i] > 0 && spTo[i] != -1 && spTo[i] != i)) {
							uf.print();
							std::cout << "Node " << i << " " << spC[i] << " " << spTo[i] << '\n';
						}
						assert(spC[i] > 0 && spTo[i] != -1 && spTo[i] != i);
						int s = 0;
						for (int j = 0; j < nbEdges(); j++) {
							if (eInSP[i][j] != 0) {
								s += weights[j] * static_cast<int>(edgeConnectsCCs(j));
								assert(!getEdgeVar(j).isFixed() || getEdgeVar(j).isTrue());
							}
						}
						if (s != spC[i]) {
							uf.print();
							std::cout << "Node " << i << " " << spC[i] << " " << spTo[i] << " " << s << '\n';
						}
						assert(s == spC[i]);
					} else {
						if (!(spC[i] == -1 && spTo[i] == -1)) {
							uf.print();
							std::cout << "Node " << i << " " << spC[i] << " " << spTo[i] << '\n';
							for (int j = 0; j < nbNodes(); j++) {
								if (getNodeVar(j).isFixed() && getNodeVar(j).isTrue()) {
									std::cout << j << " ";
								}
							}
							std::cout << '\n';
						}
						assert(spC[i] == -1 && spTo[i] == -1);
						for (int j = 0; j < nbEdges(); j++) {
							assert(eInSP[i][j] == 0);
						}
					}
				} else {
					assert(spC[i] == -1 && spTo[i] == -1);
					for (int j = 0; j < nbEdges(); j++) {
						assert(eInSP[i][j] == 0);
					}
				}
			}
		}
		return true;
	}

	inline void clearPathData(int node) {
		// std::memset(eInSP[i],0,sizeof(Tint)*nbEdges());
		for (int i = 0; i < nbEdges(); i++) {
			if (eInSP[node][i] != 0) {
				eInSP[node][i] = 0;
			}
		}
	}
	inline void copyPathData(int dest, int source) {
		for (int k = 0; k < nbEdges(); k++) {
			eInSP[dest][k] = eInSP[source][k];
		}
	}
	inline void renamePathTo(int node, int new_dest) {
		for (int i = 0; i < nbNodes(); i++) {
			if (spTo[i] == node) {
				spTo[i] = new_dest;
			}
		}
	}
	class comp {
	public:
		bool operator()(const std::pair<int, int>& lhs, const std::pair<int, int>& rhs) const {
			return lhs.second > rhs.second;
		}
	};

	int short_dijkstra(int s) {
		// cout<<"Doing a Short Dijkstra from "<<s<<endl;
		spTo[s] = -1;
		spC[s] = -1;
		clearPathData(s);

		std::vector<bool> visited(nbNodes(), false);
		std::vector<int> costs(nbNodes(), INT_MAX);
		std::vector<int> edge(nbNodes(), -1);
		std::priority_queue<std::pair<int, int>, std::vector<std::pair<int, int>>,
												comp>
				q;  // priority key: cost
		int count = 0;
		costs[s] = 0;
		const std::pair<int, int> val(s, costs[s]);
		q.push(val);

		int curr = s;
		while (count < nbNodes()) {
			const std::pair<int, int> top = q.top();
			curr = top.first;
			visited[curr] = true;
			// Reached the closest terminal outside of the CC of s
			if (getNodeVar(curr).isFixed() && getNodeVar(curr).isTrue() && !areSameCC(s, curr) &&
					uf.find(curr) == curr) {
				spTo[s] = curr;
				spC[s] = top.second;
				int other = getOtherEndnode(edge[curr], curr);
				if (edgeConnectsCCs(edge[curr])) {
					eInSP[s][edge[curr]] = 1;
				}
				while (edge[other] != -1) {
					if (edgeConnectsCCs(edge[other])) {
						eInSP[s][edge[other]] = 1;
					}
					other = getOtherEndnode(edge[other], other);
				}
				return curr;
			}

			q.pop();
			count++;

			for (int i = 0; i < adj[curr].size(); i++) {
				const int e = adj[curr][i];
				if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
					continue;  // Cannot take this edge
				}
				const int other = getOtherEndnode(e, curr);
				if (visited[other] || (getNodeVar(other).isFixed() && getNodeVar(other).isFalse())) {
					continue;  // cannot take this node
				}

				int cost = weights[e];
				// The cost of a fixed edge is 0, we want to go through
				// the CC of s for free.
				// if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue())
				if (!edgeConnectsCCs(e)) {
					cost = 0;
				}

				if (costs[curr] + cost < costs[other]) {
					edge[other] = e;
					costs[other] = costs[curr] + cost;
					const std::pair<int, int> val(other, costs[other]);
					q.push(val);
				}
			}
		}
		return -1;
	}

	void full_dijkstra(int s) {
		// cout<<"Doing a Full Dijkstra from "<<s<<endl;
		spTo[s] = -1;
		spC[s] = -1;
		clearPathData(s);

		std::vector<bool> visited(nbNodes(), false);
		std::vector<int> costs(nbNodes(), INT_MAX);
		std::vector<int> edge(nbNodes(), -1);
		std::priority_queue<std::pair<int, int>, std::vector<std::pair<int, int>>,
												comp>
				q;  // priority key: cost
		bool first_hit = true;
		int count = 0;
		costs[s] = 0;
		const std::pair<int, int> val(s, costs[s]);
		q.push(val);

		int curr = s;
		while (!q.empty() && count < nbNodes()) {
			const std::pair<int, int> top = q.top();
			curr = top.first;
			visited[curr] = true;
			// Reached the closest terminal outside of the CC of s
			if (getNodeVar(curr).isFixed() && getNodeVar(curr).isTrue() && !areSameCC(s, curr) &&
					uf.find(curr) == curr) {
				if (first_hit) {
					spTo[s] = curr;
					spC[s] = costs[curr];
					splb += spC[s] / 2;
					int other = getOtherEndnode(edge[curr], curr);
					if (edgeConnectsCCs(edge[curr])) {
						eInSP[s][edge[curr]] = 1;
					}
					while (edge[other] != -1) {
						if (edgeConnectsCCs(edge[other])) {
							eInSP[s][edge[other]] = 1;
						}
						other = getOtherEndnode(edge[other], other);
					}
					first_hit = false;
				}
				if (spC[curr] == -1 || spC[curr] > costs[curr]) {
					if (spC[curr] != -1) {
						splb -= spC[curr] / 2;
					}
					spC[curr] = costs[curr];
					splb += spC[curr] / 2;
					spTo[curr] = s;
					clearPathData(curr);
					int other = getOtherEndnode(edge[curr], curr);
					if (edgeConnectsCCs(edge[curr])) {
						eInSP[curr][edge[curr]] = 1;
					}
					while (edge[other] != -1) {
						if (edgeConnectsCCs(edge[other])) {
							eInSP[curr][edge[other]] = 1;
						}
						other = getOtherEndnode(edge[other], other);
					}
				}
			}

			q.pop();
			count++;

			for (int i = 0; i < adj[curr].size(); i++) {
				const int e = adj[curr][i];
				if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
					continue;  // Cannot take this edge
				}
				const int other = getOtherEndnode(e, curr);
				if (visited[other] || (getNodeVar(other).isFixed() && getNodeVar(other).isFalse())) {
					continue;  // cannot take this node
				}

				int cost = weights[e];
				// The cost of a fixed edge is 0, we want to go through
				// the CC of s for free.
				// if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue())
				if (!edgeConnectsCCs(e)) {
					cost = 0;
				}

				if (costs[curr] + cost < costs[other]) {
					edge[other] = e;
					costs[other] = costs[curr] + cost;
					const std::pair<int, int> val(other, costs[other]);
					q.push(val);
				}
			}
		}
	}

public:
	IntVar* w;

	IncrementalMinimumWTreePropagator(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id>>& _adj,
																		vec<vec<int>>& _en, IntVar* _w, vec<int> _ws)
			: TreePropagator(_vs, _es, _adj, _en),
				mw(0),
				splb(0),
				explv_sz(0),
				ccs(0),
				specialtint(0),
				w(_w) {
		explvp.push();
		priority = 5;
		nb_innodes = 0;

		for (int i = 0; i < _ws.size(); i++) {
			weights.push(_ws[i]);
		}

		w->attach(this, nbNodes() + nbEdges(), EVENT_U);

		if (w->setMinNotR(0)) {
			w->setMin(0);
		}
		// Initialise the minimum to the maximum value it can ever get.
		// We will try to bring it down from now on
		int ub = 0;
		for (int i = 0; i < nbEdges(); i++) {
			if (!getEdgeVar(i).isFixed() || getEdgeVar(i).isTrue()) {
				ub += weights[i];
			}
			assert(weights[i] > 0);
		}
		if (w->setMaxNotR(ub)) {
			w->setMax(ub);
		}

		eInSP.resize(nbNodes());
		spTo.resize(nbNodes());
		spC.resize(nbNodes());
		for (int i = 0; i < nbNodes(); i++) {
			eInSP[i].resize(nbEdges());
			clearPathData(i);
			spTo[i] = -1;
			spC[i] = -1;
		}

		e_already_counted.resize(nbEdges());
		for (int i = 0; i < nbEdges(); i++) {
			e_already_counted[i] = 0;
		}
		n_already_counted.resize(nbNodes());
		for (int i = 0; i < nbNodes(); i++) {
			n_already_counted[i] = 0;
		}
	}

	void wakeup(int i, int c) override {
		if (i < nbNodes() + nbEdges()) {
			TreePropagator::wakeup(i, c);
		} else {
			pushInQueue();
		}
	}

	bool areSameCC(int a, int b) { return uf.connected(a, b); }
	bool edgeConnectsCCs(int e) { return !uf.connected(getEndnode(e, 0), getEndnode(e, 1)); }

	bool propagateNewNode(int n) override {
		// Full Dijkstra from this node
		//  -> udpate spTo[n], spC[n] and spFrom[n]
		//  -> for all other mandatories,
		//      if spC[other] > full_dijkstra(n)[other]
		//          splb -= spC[other]
		//          spC[other] = full_dijkstra(n)[other]
		//          splb += spC[other]
		//          spTo[other] = n
		//          eInSP[other] = vector<edge>(zeroes)
		//          eInSP[other] = [1 for e in edges if e used from n to other]

		const int rn = uf.find(n);
		full_dijkstra(rn);
		assert(spTo[rn] != uf.find(rn));

		return true;
	}

	bool propagateRemEdge(int e) override {
		// Done in wakeup for explanations!!
		// Start a short Dijkstra at each CC that
		// used e in it's shortest path
		//  splp -= spC[CC[i]]
		//  spC[CC[i]] = short_dijkstra(CC[i])
		//  splb += spC[CC[i]]

		for (int i = 0; i < nbNodes(); i++) {
			if (eInSP[i][e] != 0) {
				const int tmp = splb;
				splb -= spC[i] / 2;
				short_dijkstra(i);
				assert(spTo[i] != i);
				splb += spC[i] / 2;
				explvf.push(getEdgeVar(e).getValLit());
				explvp.push(getEdgeVar(e).getValLit());
				explv_sz++;
			}
		}
		return true;
	}

	bool propagateNewEdge(int e) override {
		if (e_already_counted[e] == 0) {
			mw += weights[e];
			e_already_counted[e] = 1;
			explvf.push(getEdgeVar(e).getValLit());
			explvp.push(getEdgeVar(e).getValLit());
			explv_sz++;
		}

		const int u = getEndnode(e, 0);
		const int v = getEndnode(e, 1);
		assert(getNodeVar(u).isFixed() && getNodeVar(u).isTrue());
		assert(getNodeVar(v).isFixed() && getNodeVar(v).isTrue());

		const int ru = uf.find(u);
		const int rv = uf.find(v);

		if (ru == rv) {
			return true;
		}

		// If only one was already int eh graph
		// make sure the leader is the one that was already
		// in the graph, so you don't need to do a full_dij
		// from the new node
		/*
		if (spC[ru] == -1 && spC[rv] != -1) {
				uf.id[ru] = rv;
		} else if (spC[ru] == -1 && spC[rv] != -1) {
				uf.id[rv] = ru;
		} else {
				uf.unite(u,v);
		}//*/
		uf.unite(u, v);
		const int n_r = uf.find(ru);
		// cout<<"United "<<u<<" "<<v<<" ->"<<n_r<<endl;

		// United to CCs that had each otehr as SP
		if (spTo[ru] == rv && spTo[rv] == ru) {
			assert(ru != rv);
			const int loser = n_r == ru ? rv : ru;
			spC[loser] = -1;
			spTo[loser] = -1;
			clearPathData(loser);
			renamePathTo(loser, n_r);
			short_dijkstra(n_r);
			return true;
		}

		int cheapest = spC[ru] < spC[rv] ? ru : rv;

		// Make sure you don't consider a node that goes to nowhere
		//  (a new node) the origin the cheapest node.
		// Also, don't consider a node the cheapest node
		//  if it's spTo is actually going to be subusmmed by the new edge
		if (spC[ru] == -1 || spTo[ru] == rv) {
			cheapest = rv;
		} else if (spC[rv] == -1 || spTo[rv] == ru) {
			cheapest = ru;
		}

		if (n_r != cheapest) {
			spC[n_r] = spC[cheapest];
			if (spTo[cheapest] != n_r) {
				spTo[n_r] = spTo[cheapest];
			}
			copyPathData(n_r, cheapest);
			eInSP[n_r][e] = 0;  // because e is inside a CC
			spC[cheapest] = -1;
			spTo[cheapest] = -1;
			clearPathData(cheapest);
			renamePathTo(cheapest, n_r);
		}

		// cout<<"n_r and cheapest "<<n_r<<" "<<cheapest<<endl;

		if (n_r == ru) {
			spC[rv] = -1;
			spTo[rv] = -1;
			clearPathData(rv);
		} else if (n_r == rv) {
			spC[ru] = -1;
			spTo[ru] = -1;
			clearPathData(ru);
		}

		if (eInSP[n_r][e] != 0) {
			spC[n_r] -= weights[e];
		}

		return true;
	}

	bool propagate() override {
		if (explv_sz < explvf.size()) {
			explvf.resize(explv_sz);
			explvp.resize(explv_sz + 1);
		}

		/*
		uf.print();
		for (int i = 0; i < nbNodes(); i++) {
				if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue())
						cout<<i<<" ";
		}
		cout<<endl;
		for (int i = 0; i < nbNodes(); i++) {
				if (spC[i] != -1)
						cout<<i<<" ";
		}
		cout<<endl;
		//*/

		std::unordered_set<int>::iterator it;

		// cout<<"1. spC[0] = "<<spC[0]<<endl;
		// uf.print();

		for (it = newFixedN.begin(); it != newFixedN.end(); ++it) {
			if (getNodeVar(*it).isTrue()) {
				if (n_already_counted[*it] != 0) {
					continue;
				}
				ccs++;
			}
		}

		for (it = newFixedE.begin(); it != newFixedE.end(); ++it) {
			if (getEdgeVar(*it).isTrue()) {
				assert(!uf.connected(getEndnode(*it, 0), getEndnode(*it, 1)));
				// cout<<"new edge "<<*it<<" ("<<getEndnode(*it,0)<<" "<<getEndnode(*it,1)<<"
				// ccs:"<<ccs<<endl;
				const int u = getEndnode(*it, 0);
				const int v = getEndnode(*it, 1);
				// if (spC[uf.find(u)] != -1 && spC[uf.find(v)] != -1)
				ccs--;
				propagateNewEdge(*it);
			}
		}

		// uf.print();
		// cout<<"2. spC[0] = "<<spC[0]<<endl;
		for (it = newFixedN.begin(); it != newFixedN.end(); ++it) {
			if (getNodeVar(*it).isTrue()) {
				if (n_already_counted[*it] != 0) {
					continue;
				}
				// cout<<"new node "<<*it<<endl;
				nb_innodes++;
				// if (uf.find(*it) == *it) ccs++;
				n_already_counted[*it] = 1;
				propagateNewNode(*it);
			}
		}

		// cout<<"3. spC[0] = "<<spC[0]<<endl;

		for (it = newFixedE.begin(); it != newFixedE.end(); ++it) {
			if (getEdgeVar(*it).isFalse()) {
				// cout<<"rem edge "<<*it<<" ("<<getEndnode(*it,0)<<" "<<getEndnode(*it,1)<<endl;
				propagateRemEdge(*it);
			}
		}

		// cout<<"4. spC[0] = "<<spC[0]<<endl;

		const int old = splb;
		int sum = 0;
		int minspC = -1;
		const int ccc = ccs;

#if TREEPROP_DEBUG
		for (int i = 0; i < nbNodes(); i++)
			if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() && uf.find(i) == i) ccc++;

		if (ccc != ccs) {
			uf.print();
			for (int i = 0; i < nbNodes(); i++) {
				if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue()) cout << i << " ";
			}
			cout << endl;
			for (int i = 0; i < nbNodes(); i++) {
				if (spC[i] != -1) cout << i << " ";
			}
			cout << endl;
			cout << ccc << " " << ccs << endl;
		}
		assert(ccc == ccs);
		//*/
#endif
		for (int i = 0; ccc > 1 && i < nbNodes(); i++) {
			if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() && uf.find(i) == i) {
#if TREEPROP_DEBUG
				if (spC[i] <= 0) {
					cout << i << " " << spC[i] << " " << spTo[i] << "    nb_innodes = " << nb_innodes << endl;
					cout << "edges -> ";
					for (int j = 0; j < nbEdges(); j++)
						if (eInSP[i][j])
							cout << j << "(" << getEndnode(j, 0) << "," << getEndnode(j, 1) << "," << weights[j]
									 << "," << edgeConnectsCCs(j) << ") ";
					cout << endl;
					uf.print();
					for (int i = 0; i < nbNodes(); i++) {
						if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue()) cout << i << " ";
					}
					cout << endl;
					for (int i = 0; i < nbNodes(); i++) {
						if (spC[i] != -1) cout << i << "(" << spTo[i] << ") ";
					}
					cout << endl;
				}
				assert(spC[i] > 0);
				//(spC[i] != -1) {
				int old = spC[i];
				short_dijkstra(i);
				if (old != spC[i]) {
					cout << "  node " << i << " " << old << " " << spC[i] << endl;
					cout << "Node!! " << spTo[26] << " used edges ";
					for (int k = 0; k < nbEdges(); k++) {
						if (eInSP[i][k]) cout << k << " ";
					}
					cout << endl;
				}
				assert(old == spC[i]);
#endif
				sum += spC[i] / 2;
				if (minspC == -1 || spC[i] < minspC) {
					minspC = spC[i];
				}
			} else {
				assert(spC[i] == -1);
			}
		}

		if (ccc > 1 && ccc % 2 == 1) {
			sum -= minspC;
		}

		assert(sum != 1);
		const int splb = sum;

		assert(verify_state());

		Clause* r = nullptr;
		if (splb + mw > w->getMax()) {
			// cout<<"Lower bound is "<<splb<<" "<<mw<<" "<<splb+mw<<" "<<w->getMax()<<endl;
			if (so.lazy) {
				explvf.push(w->getMaxLit());
				Clause* expl = Clause_new(explvf);
				expl->temp_expl = 1;
				sat.rtrail.last().push(expl);
				sat.confl = expl;
				explvf.resize(explvf.size() - 1);
			}
			return false;
		}
		if (w->setMinNotR(splb + mw)) {
			if (so.lazy) {
				r = Reason_new(explvp);
			}
			w->setMin(splb + mw, r);
		}

		return true;
	}
};
//*/

class MinimumWTreePropagator : public TreePropagator {
protected:
	vec<int> weights;
	Tint mandatoryWeight;
	int totalWeightVarID;
	Tint lowerBound;

	// Array of nbNodes()*nbEdges()
	// For each node, gives the edges used in its shortest path to another CC
	//  [a][b] == 1 if b is an edge used in the shortest path starting in a
	//  [a][b] == 0 if b is not used.
	Tint** shortestPathsEdges;
	// Array nbNodes()*2, contains, for each node:
	// If the node the repsents a CC:
	//     [cost of its shortest path to other CC, repr of the other CC]
	// If not,, [-1,-1]
	// Therefore, only nodes that are repr have an itneresting value
	Tint** shortestPathsInfo;

	Tint* removedEdgesFromSP;

	/**
	 * Propagation rules on Stiener nodes (cf. paper)
	 */
	bool steiner_node(int node) {
		if (!getNodeVar(node).isFixed() || getNodeVar(node).isFalse()) {
			return true;
		}
		// A steiner node (non-terminal) of degree 2 MUST use its two edges.
		// Otherwise its costing us wieght for nothing
		// If adding that new edge creates a cycle, we will fail and learn later
		// If we cant add the second edge, we fail.
		//!\This is only valid if tree() is the only constraint forcing terminals in
		if (!isTerminal[node]) {
			int degree = 0;
			vec<edge_id> connectingEdges;
			for (const int e : adj[node]) {
				if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isTrue()) {
					degree++;
					connectingEdges.push(e);
				}
			}
			// a configuration where the node is of deg 1 and with the edge
			// fixed is valid and could still be cheaper... not the cheapest,
			// but cheaper
			if (degree == 1 /*&& es[connectingEdges[0]].isFixed()*/) {
				// Fail, given the adj[node] edges that are set to false
				if (so.lazy) {
					vec<Lit> ps;
					assert(getNodeVar(node).isFixed());
					ps.push(getNodeVar(node).getValLit());
					for (const int e : adj[node]) {
						if (getEdgeVar(e).isFixed()) {
							ps.push(getEdgeVar(e).getValLit());
						}
					}
					Clause* expl = Clause_new(ps);
					expl->temp_expl = 1;
					sat.rtrail.last().push(expl);
					sat.confl = expl;
				}
				return false;
			}
			if (degree == 2) {
				// Force both edges in if they arent already.
				for (int i = 0; i < 2; i++) {
					const edge_id e = connectingEdges[i];
					// If its fixed, its fixed to 1, which is OK
					if (!getEdgeVar(e).isFixed()) {
						Clause* r = nullptr;
						if (so.lazy) {
							vec<Lit> ps;
							ps.push();
							assert(getNodeVar(node).isFixed());
							ps.push(getNodeVar(node).getValLit());
							for (const int i : adj[node]) {
								if (getEdgeVar(i).isFixed()) {
									ps.push(getEdgeVar(i).getValLit());
								}
							}
							r = Reason_new(ps);
						}
						if (TREEPROP_DEBUG) {
							std::cout << "STEINER " << e << '\n';
						}
						getEdgeVar(e).setVal(true, r);  // New edge in (bridge)
					}
				}
			}
		}
		return true;
	}

public:
	IntVar* totalWeight;

	MinimumWTreePropagator(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id>>& _adj,
												 vec<vec<int>>& _en, IntVar* _w, vec<int> _ws)
			: TreePropagator(_vs, _es, _adj, _en),
				mandatoryWeight(0),  // apsp(this),
				lowerBound(0),
				totalWeight(_w) {
		for (int i = 0; i < _ws.size(); i++) {
			weights.push(_ws[i]);
		}

		totalWeightVarID = nbNodes() + nbEdges();
		totalWeight->attach(this, totalWeightVarID, EVENT_U);

		// Will add upon propagation. If you add it now, and then, you might add it twice
		// Otherwise, could use a last_state_e kind of thing.
		// for (int i = 0; i < nbEdges(); i++) {
		//     mandatoryWeight += (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue())? _ws[i] : 0;
		// }

		// Can set values in constructor?
		if (totalWeight->getMin() < mandatoryWeight) {
			totalWeight->setMin(mandatoryWeight);
		}

		// Initialise the minimum to the maximum value it can ever get.
		// We will try to bring it down from now on
		int ub = 0;
		for (int i = 0; i < nbEdges(); i++) {
			if (!getEdgeVar(i).isFixed() || getEdgeVar(i).isTrue()) {
				ub += weights[i];
			}
		}
		if (totalWeight->setMaxNotR(ub)) {
			totalWeight->setMax(ub);
		}

		shortestPathsEdges = new Tint*[nbNodes()];
		shortestPathsInfo = new Tint*[nbNodes()];
		for (int i = 0; i < nbNodes(); i++) {
			shortestPathsEdges[i] = new Tint[nbEdges()];
			std::memset(shortestPathsEdges[i], 0, sizeof(Tint) * nbEdges());
			shortestPathsInfo[i] = new Tint[2];
			std::memset(shortestPathsInfo[i], -1, sizeof(Tint) * 2);
		}

		removedEdgesFromSP = new Tint[nbEdges()];
		std::memset(removedEdgesFromSP, 0, sizeof(Tint) * nbEdges());

		return;

		// Remove non terminals of deg 1
		bool changes = false;
		do {
			changes = false;
			for (int i = 0; i < nbNodes(); i++) {
				if (!isTerminal[i] && !getNodeVar(i).isFixed()) {
					int deg = 0;
					int lastSeen = -1;
					for (const int j : adj[i]) {
						if (!getEdgeVar(j).isFixed() || getEdgeVar(j).isTrue()) {
							deg++;
							lastSeen = j;
						}
					}
					if (deg == 1 && lastSeen != -1) {
						getNodeVar(i).setVal(false);
						getEdgeVar(lastSeen).setVal(false);
						changes = true;
					} else if (deg == 0) {
						getNodeVar(i).setVal(false);
						changes = true;
					}
				}
			}
		} while (changes);
	}

	void wakeup(int i, int c) override {
		if (i == totalWeightVarID) {
			if (TREEPROP_DEBUG) {
				std::cout << "Wakeup" << '\n'
									<< __FILE__ << " " << __LINE__ << " totalWeight " << totalWeight->getMax() << '\n'
									<< "event Upperbound" << '\n';
			}
			pushInQueue();
		} else {
			TreePropagator::wakeup(i, c);
		}
	}

	~MinimumWTreePropagator() override {
		for (int i = 0; i < nbNodes(); i++) {
			delete[] shortestPathsEdges[i];
			delete[] shortestPathsInfo[i];
		}
		delete[] shortestPathsEdges;
		delete[] shortestPathsInfo;

		delete[] removedEdgesFromSP;
	}

	class comp {
	public:
		bool operator()(const std::pair<int, int>& lhs, const std::pair<int, int>& rhs) const {
			return lhs.second > rhs.second;
		}
	};

	struct DijkstraInfo {
		int cost{0};
		int prev{0};
		int edge{0};
		DijkstraInfo() = default;
	};

	/**
	 * This implementation of Dijkstra stops when reaching a "terminal"
	 * s: starting node
	 * res[]: for each node, cost and predecor info
	 * n: number of nodes in the graph
	 */
	int Dijkstra(int s, DijkstraInfo res[], std::vector<bool>& cc, int n) {
		for (int i = 0; i < n; i++) {
			res[i].cost = INT_MAX;
		}

		std::priority_queue<std::pair<int, int>, std::vector<std::pair<int, int>>,
												comp>
				q;  // priority key: cost
		std::vector<bool> visited(n, false);
		int count = 0;
		res[s].prev = s;
		res[s].cost = 0;

		const std::pair<int, int> val(s, res[s].cost);
		q.push(val);

		int curr = s;
		while (count < n) {
			const std::pair<int, int> top = q.top();
			curr = top.first;
			// Reached the closest terminal outside of the CC of s
			if (getNodeVar(curr).isFixed() && getNodeVar(curr).isTrue()) {
				if (!cc[curr]) {
					// cout <<"Dijkstra exit1 "<<curr<<endl;
					return curr;
				}
			}

			q.pop();
			visited[curr] = true;
			count++;

			for (int i = 0; i < adj[curr].size(); i++) {
				const int e = adj[curr][i];
				const int other = OTHER(getEndnode(e, 0), getEndnode(e, 1), curr);

				if (visited[other] || (getNodeVar(other).isFixed() && getNodeVar(other).isFalse())) {
					continue;  // cannot take this node
				}

				int cost = weights[e];
				// The cost of a fixed edge is 0, we want to go through
				// the CC of s for free.
				if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
					cost = 0;
				} else if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
					continue;  // Cannot take this edge
				}

				if (res[curr].cost + cost < res[other].cost) {
					res[other].prev = curr;
					res[other].edge = e;
					res[other].cost = res[curr].cost + cost;

					const std::pair<int, int> val(other, res[other].cost);

					q.push(val);
				}
			}
		}
		// cout <<"Dijkstra exit2"<<endl;
		return curr;
	}
	int fullDijkstra(int s, DijkstraInfo res[], int n) {
		for (int i = 0; i < n; i++) {
			res[i].cost = INT_MAX;
		}

		std::priority_queue<std::pair<int, int>, std::vector<std::pair<int, int>>,
												comp>
				q;  // priority key: cost
		std::vector<bool> visited(n, false);
		int count = 0;
		res[s].prev = s;
		res[s].cost = 0;

		const std::pair<int, int> val(s, res[s].cost);
		q.push(val);

		int curr = s;
		while (count < n) {
			const std::pair<int, int> top = q.top();
			curr = top.first;

			q.pop();
			visited[curr] = true;
			count++;

			for (int i = 0; i < adj[curr].size(); i++) {
				const int e = adj[curr][i];
				const int other = OTHER(getEndnode(e, 0), getEndnode(e, 1), curr);

				if (visited[other] || (getNodeVar(other).isFixed() && getNodeVar(other).isFalse())) {
					continue;  // cannot take this node
				}

				int cost = weights[e];
				// The cost of a fixed edge is 0, we want to go through
				// the CC of s for free.
				if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
					cost = 0;
				} else if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
					continue;  // Cannot take this edge
				}

				if (res[curr].cost + cost < res[other].cost) {
					res[other].prev = curr;
					res[other].edge = e;
					res[other].cost = res[curr].cost + cost;

					const std::pair<int, int> val(other, res[other].cost);

					q.push(val);
				}
			}
		}
		return curr;
	}

	/**
	 * Update node i if its a representative of a CC
	 * eopt is used to force the update in case of an edge removal
	 *  because the weight of the newlly found sp might be == to the old
	 *  one and thus look like its not necesary to do anything, yet it is
	 *  because a removed edge is used.
	 */
	bool elementaryUpdate(int i, int eopt = -1) {
		// The || condition is required at the begining, when all ndoes have
		// shortestPathsInfo[node][0] = -1
		if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() &&
				(/*shortestPathsInfo[i][0] != -1 ||*/ ruf.isRoot(i))) {
			if (TREEPROP_DEBUG) {
				std::cout << "elementary update of #" << i << " (isRoot:" << ruf.isRoot(i) << '\n';
			}
			const int rep = i;
			std::vector<DijkstraInfo> dijkstraPath(nbNodes());
			struct CC cc;
			std::vector<bool> ccvisited(nbNodes(), false);
			getCC(rep, ccvisited, &cc);
			const int other = Dijkstra(rep, dijkstraPath.data(), ccvisited, nbNodes());
			// other can be three things:
			// -another terminal in another CC (interesting case)
			// -another terminal in the same CC as n (same as next case)
			// -a non terminal, because Dijkstra walked all the graph
			// cout <<" "<<rep <<" "<<other<<" " <<ccvisited[other]<<endl;

			// if 'other' is a fixed-in node in another CC...
			if (getNodeVar(other).isFixed() && getNodeVar(other).isTrue() && !ccvisited[other]) {
				// cout <<"filling column #" <<rep<<" reached "<<other<<endl;
				const int repN = ruf.find(rep);
				const int repO = ruf.find(other);
				assert(repN != repO);
				// assert(repN == rep);
				// Mark the edges in the path from repN to repO

				if (shortestPathsInfo[repN][0] == -1 ||
						shortestPathsInfo[repN][0] > dijkstraPath[other].cost || eopt != -1) {
					int prev1 = other;
					int prev2 = dijkstraPath[prev1].prev;
					std::vector<int> tmp(nbEdges(), 0);
					// std::memset(shortestPathsEdges[repN],0,sizeof(Tint)*nbEdges());
					int count = 0;
					while (prev1 != rep) {
						// cout <<"while loop "<<prev1 <<" "<<prev2 <<" "<<rep << "
						// "<<dijkstraPath[prev1].edge<<endl;
						tmp[dijkstraPath[prev1].edge] = 1;
						// shortestPathsEdges[repN][dijkstraPath[prev1].edge] = 1;
						prev1 = prev2;
						prev2 = dijkstraPath[prev1].prev;
						count++;
						assert(count <= nbNodes());
					}
					for (int i = 0; i < nbEdges(); i++) {
						if (shortestPathsEdges[repN][i] == 1 && tmp[i] == 0) {
							// cout <<" added missing edge #"<<i<<endl;
							if (getEdgeVar(i).isFixed() && getEdgeVar(i).isFalse()) {
								removedEdgesFromSP[i] = 1;
								// break; //TODO: redo tests with break, only one edge is needed for the explanation
							}
						}
						shortestPathsEdges[repN][i] = tmp[i];
					}
					if (TREEPROP_DEBUG) {
						std::cout << "been here6 " << repN << " " << shortestPathsInfo[repN][1] << " " << other
											<< "prev cost: " << shortestPathsInfo[repN][0]
											<< "new cost: " << dijkstraPath[other].cost << '\n';
					}
					shortestPathsInfo[repN][0] = dijkstraPath[other].cost;
					shortestPathsInfo[repN][1] = other;
				}
			} else {
				std::memset(shortestPathsEdges[rep], 0, sizeof(Tint) * nbEdges());
				shortestPathsInfo[rep][0] = -1;
				shortestPathsInfo[rep][1] = -1;
			}
		} else {
			if (shortestPathsInfo[i][0] != -1) {
				std::memset(shortestPathsEdges[i], 0, sizeof(Tint) * nbEdges());
				shortestPathsInfo[i][0] = -1;
				shortestPathsInfo[i][1] = -1;
			}
		}

		return true;
	}

	bool updateLowerBound() {
		if (TREEPROP_DEBUG) {
			std::cout << "update all" << '\n';
		}
		lowerBound = 0;
		// For each repr of any CC:
		// Find the shortest path to any other CC
		// If no other CC, then 0
		for (int i = 0; i < nbNodes(); i++) {
			if (!elementaryUpdate(i)) {
				return false;
			}
		}
		return true;
	}

	bool propagateNewNode(int n) override {
		assert(nb_innodes > 0);
		// Tree of one node is good
		// if(nb_innodes == 1)
		//     return true;

		if (!steiner_node(n)) {
			return false;
		}

		const bool ok = TreePropagator::propagateNewNode(n);
		if (!ok) {
			return false;
		}

		const int repN = ruf.find(n);
		std::vector<DijkstraInfo> dijkstraPath(nbNodes());
		// int end = fullDijkstra(repN, dijkstraPath,nbNodes());
		struct CC cc;
		std::vector<bool> ccvisited(nbNodes(), false);
		getCC(repN, ccvisited, &cc);
		int min = -1;
		int argmin = -1;
		for (int i = 0; i < nbNodes(); i++) {
			min = (min == -1 || min > dijkstraPath[i].cost) ? dijkstraPath[i].cost : min;
			argmin = (argmin == -1 || min > dijkstraPath[i].cost) ? i : argmin;
			if (getNodeVar(i).isFixed() && (getNodeVar(i).getVal() != 0) && ruf.isRoot(i)) {
				if (i != repN && shortestPathsInfo[i][0] > dijkstraPath[i].cost) {
					// i is the rep of another cc
					assert(shortestPathsInfo[i][0] != -1 || i == repN);
					int prev1 = i;
					int prev2 = dijkstraPath[prev1].prev;
					std::memset(shortestPathsEdges[i], 0, sizeof(Tint) * nbEdges());
					int count = 0;
					while (prev1 != repN) {
						shortestPathsEdges[i][dijkstraPath[prev1].edge] = 1;
						prev1 = prev2;
						prev2 = dijkstraPath[prev1].prev;
						count++;
						assert(count <= nbNodes());
					}
					if (TREEPROP_DEBUG) {
						std::cout << "been here5 " << i << '\n';
					}
					shortestPathsInfo[i][0] = dijkstraPath[i].cost;
					shortestPathsInfo[i][1] = repN;
				}
			}
		}
		if (argmin != -1) {  // more CCs
			int prev1 = argmin;
			int prev2 = dijkstraPath[prev1].prev;
			std::memset(shortestPathsEdges[repN], 0, sizeof(Tint) * nbEdges());
			int count = 0;
			while (prev1 != repN) {
				shortestPathsEdges[repN][dijkstraPath[prev1].edge] = 1;
				prev1 = prev2;
				prev2 = dijkstraPath[prev1].prev;
				count++;
				assert(count <= nbNodes());
			}
			if (TREEPROP_DEBUG) {
				std::cout << "been here4 " << repN << '\n';
			}
			shortestPathsInfo[repN][0] = dijkstraPath[argmin].cost;
			shortestPathsInfo[repN][1] = argmin;
		}
		return true;
	}

	bool propagateNewEdge(int e) override {
		if (TREEPROP_DEBUG) {
			std::cout << "newEdge" << '\n';
		}
		const int rep0 = ruf.find(getEndnode(e, 0));
		const int rep1 = ruf.find(getEndnode(e, 1));
		bool mergeCC = false;
		if (getNodeVar(rep0).isFixed() && getNodeVar(rep0).isTrue() && getNodeVar(rep1).isFixed() &&
				getNodeVar(rep1).isTrue()) {
			mergeCC = true;
		}
		const int e0 = getEndnode(e, 0);
		const int e1 = getEndnode(e, 1);
		const bool wasE0Fixed = getNodeVar(getEndnode(e, 0)).isFixed();
		const bool wasE1Fixed = getNodeVar(getEndnode(e, 1)).isFixed();

		const bool ok = TreePropagator::propagateNewEdge(e);
		if (!ok) {
			return false;
		}

		// mandatoryWeight += weights[e];
		if (mergeCC) {
			const int newR = ruf.find(e0);
			assert(newR == e0 || newR == e1);
			const int maxR = (shortestPathsInfo[rep0][0] > shortestPathsInfo[rep1][0]) ? rep0 : rep1;
			const int minR = (maxR == rep0) ? rep1 : rep0;
			if (TREEPROP_DEBUG) {
				std::cout << "been here3 " << maxR << '\n';
			}
			std::memset(shortestPathsEdges[maxR], 0, sizeof(Tint) * nbEdges());
			shortestPathsInfo[maxR][0] = -1;
			shortestPathsInfo[maxR][1] = -1;
			int count = 0;
			for (int j = 0; j < nbNodes(); j++) {
				if (getNodeVar(j).isFixed() && getNodeVar(j).isTrue() && ruf.isRoot(j)) {
					count++;
				}
			}
			if (count > 1) {  // More than one CC
				if (TREEPROP_DEBUG) {
					std::cout << "been here2 " << newR << '\n';
				}
				std::memcpy(shortestPathsEdges[newR], shortestPathsEdges[minR], sizeof(Tint) * nbEdges());
				shortestPathsInfo[newR][0] = shortestPathsInfo[minR][0];
				shortestPathsInfo[newR][1] = shortestPathsInfo[minR][1];
			}
			if (minR != newR) {
				if (TREEPROP_DEBUG) {
					std::cout << "been here1 " << minR << '\n';
				}
				std::memset(shortestPathsEdges[minR], 0, sizeof(Tint) * nbEdges());
				shortestPathsInfo[minR][0] = -1;
				shortestPathsInfo[minR][1] = -1;
			}
		} else {
			const int newR = ruf.find(e0);
			assert(newR == e0 || newR == e1);
			if (TREEPROP_DEBUG) {
				std::cout << "maybe here?" << '\n';
			}

			if (wasE0Fixed && !wasE1Fixed) {
				assert(ruf.find(e1) == e0);
				if (newR != rep0) {
					std::memcpy(shortestPathsEdges[newR], shortestPathsEdges[rep0], sizeof(Tint) * nbEdges());
					shortestPathsInfo[newR][0] = shortestPathsInfo[rep0][0];
					shortestPathsInfo[newR][1] = shortestPathsInfo[rep0][1];
					std::memset(shortestPathsEdges[rep0], 0, sizeof(Tint) * nbEdges());
					shortestPathsInfo[rep0][0] = -1;
					shortestPathsInfo[rep0][1] = -1;
				}
			} else if (wasE1Fixed && !wasE0Fixed) {
				assert(ruf.find(e0) == e1);
				if (newR != rep1) {
					std::memcpy(shortestPathsEdges[newR], shortestPathsEdges[rep1], sizeof(Tint) * nbEdges());
					shortestPathsInfo[newR][0] = shortestPathsInfo[rep1][0];
					shortestPathsInfo[newR][1] = shortestPathsInfo[rep1][1];
					std::memset(shortestPathsEdges[rep1], 0, sizeof(Tint) * nbEdges());
					shortestPathsInfo[rep1][0] = -1;
					shortestPathsInfo[rep1][1] = -1;
				}
			} else if (!wasE0Fixed && !wasE1Fixed) {
				assert(ruf.isRoot(e0) || ruf.isRoot(e1));
				assert((ruf.isRoot(e0) && !ruf.isRoot(e1)) || (!ruf.isRoot(e0) && ruf.isRoot(e1)));
				if (!elementaryUpdate(e0)) {
					return false;
				}
				if (!elementaryUpdate(e1)) {
					return false;
				}
			} else {
				NEVER;
			}
		}
		return true;
	}

	bool propagateRemNode(int n) override {
		if (TREEPROP_DEBUG) {
			std::cout << "remNode " << n << '\n';
		}
		const bool ok = TreePropagator::propagateRemNode(n);
		if (!ok) {
			return false;
		}
		for (const int e : adj[n]) {
			for (int i = 0; i < nbNodes(); i++) {
				if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue()) {
					if (shortestPathsEdges[i][e] == 1) {
						removedEdgesFromSP[e] = 1;
						if (!elementaryUpdate(i, e)) {
							return false;
						}
					}
				}
			}
		}
		return true;
	}

	bool propagateRemEdge(int e) override {
		if (TREEPROP_DEBUG) {
			std::cout << "remEdge " << e << '\n';
		}
		const bool ok = TreePropagator::propagateRemEdge(e);
		if (!ok) {
			return false;
		}
		for (int i = 0; i < 2; i++) {
			const int node = getEndnode(e, i);
			if (!steiner_node(node)) {
				return false;
			}
		}
		for (int i = 0; i < nbNodes(); i++) {
			if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue()) {
				if (shortestPathsEdges[i][e] == 1) {
					removedEdgesFromSP[e] = 1;
					if (!elementaryUpdate(i, e)) {
						return false;
					}
				}
			}
		}

		return true;
	}

	void printEdgesMatrix() {
		for (int i = 0; i < nbNodes(); i++) {
			std::cout << ((getNodeVar(i).isFixed() && getNodeVar(i).getVal() == 1 && ruf.isRoot(i))
												? "R "
												: "  ");
		}
		std::cout << '\n';
		for (int i = 0; i < nbNodes(); i++) {
			std::cout << ((getNodeVar(i).isFixed() && getNodeVar(i).getVal() == 1 &&
										 shortestPathsInfo[i][0] != -1)
												? "R "
												: "  ");
		}
		std::cout << '\n';
		for (int i = 0; i < nbNodes(); i++) {
			std::cout << ((shortestPathsInfo[i][0] != -1) ? "R " : "  ");
		}
		std::cout << '\n';
		for (int i = 0; i < nbEdges(); i++) {
			for (int j = 0; j < nbNodes(); j++) {
				std::cout << shortestPathsEdges[j][i] << " ";
			}
			std::cout << '\n';
		}
		std::cout << '\n';
	}

	bool propagate() override {
		if (TREEPROP_DEBUG) {
			std::cout << "ppgate" << '\n';
		}

		const bool computeLBFromScratch = true;  //(newFixedN.size() > 0);
		std::unordered_set<int>::iterator it;
		for (it = newFixedN.begin(); it != newFixedN.end(); ++it) {
			const int j = *it;  // newFixedN[i];

			nb_innodes = nb_innodes + ((getNodeVar(j).isTrue()) ? 1 : 0);
			if (getNodeVar(j).isTrue()) {
				if (!TreePropagator::propagateNewNode(j)) {
					return false;
				}
			} else {
				if (!propagateRemNode(j)) {
					return false;
				}
			}
		}
		if (nb_innodes == 1) {  // One ndoe in in the entire graph
			lowerBound = 0;
			return true;
		}

		for (it = newFixedE.begin(); it != newFixedE.end(); ++it) {
			const int j = *it;  // newFixedE[i];
			if (getEdgeVar(j).isTrue()) {
				// cout<<"Added edge between "<<getEndnode(j,0)<<" and "<<getEndnode(j,1)<<endl;
				if (computeLBFromScratch) {
					if (!TreePropagator::propagateNewEdge(j)) {
						return false;
					}
				} else {
					if (!propagateNewEdge(j)) {
						return false;
					}
				}
				for (int i = 0; i < nbNodes(); i++) {
					if (shortestPathsEdges[i][j] != 0) {
						shortestPathsInfo[i][0] -= weights[j];
					}
				}

				mandatoryWeight += weights[j];
				Clause* r = nullptr;
				if (so.lazy) {
					vec<Lit> ps;
					ps.push();
					for (int i = 0; i < nbEdges(); i++) {
						if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) {
							ps.push(getEdgeVar(i).getValLit());
						}
					}
					r = Reason_new(ps);
				}
				// if (totalWeight->setMinNotR(mandatoryWeight))
				//     totalWeight->setMin(mandatoryWeight,r);
			} else {
				if (computeLBFromScratch) {
					if (!TreePropagator::propagateRemEdge(j)) {
						return false;
					}
				} else {
					if (!propagateRemEdge(j)) {
						return false;
					}
				}
			}
		}

		if (computeLBFromScratch) {
			if (!updateLowerBound()) {
				return false;
			}
		}

		lowerBound = 0;
		int ccs = 0;
		int minSp = -1;
		// cout<<"lowerBound "<<lowerBound<<endl;
		for (int i = 0; i < nbNodes(); i++) {
			if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue() && shortestPathsInfo[i][0] != -1) {
				ccs++;
				if (ccs > 1) {
					assert(shortestPathsInfo[i][0] != -1);
				}
				lowerBound += shortestPathsInfo[i][0];
				// cout<<"lowerBound "<<lowerBound<<" (added by: "<<i<<",
				// "<<shortestPathsInfo[i][0]<<")"<<endl;
				if (shortestPathsInfo[i][0] < minSp || minSp == -1) {
					minSp = shortestPathsInfo[i][0];
				}
			}
		}
		if (ccs == 1) {
			lowerBound = 0;
		} else if (ccs % 2 == 1) {
			lowerBound -= minSp;
		}
		if (lowerBound < 0) {
			lowerBound = 0;
		}
		// cout<<"lowerBound "<<lowerBound<<endl;
		// return true;
		//  int s = 0;
		//  for (int i = 0; i < nbEdges(); i++){
		//      if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()){
		//          s += weights[i];
		//      }
		//  }
		//  mandatoryWeight = s;
		// Update the mandatory weight.
		const int total = lowerBound / 2 + mandatoryWeight;
		if (TREEPROP_DEBUG) {
			std::cout << total << " " << lowerBound << " " << totalWeight->getMax() << " "
								<< mandatoryWeight << '\n';
		}

		if (total > totalWeight->getMax()) {  // Not going to be a good solution!

			// cout<<"Lower bound is "<<lowerBound<<" "<< mandatoryWeight<<" "<<total<<"
			// "<<totalWeight->getMax()<<endl;

			// Reason: given the set of removed edges, cant do better!
			if (so.lazy) {
				vec<Lit> ps;
				ps.push(totalWeight->getMaxLit());

				for (int i = 0; i < nbEdges(); i++) {
					if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) {
						ps.push(getEdgeVar(i).getValLit());
					}
					if (removedEdgesFromSP[i] == 1) {
						assert(getEdgeVar(i).isFixed() && getEdgeVar(i).isFalse());
						ps.push(getEdgeVar(i).getValLit());
						// cout <<"included edge " <<i<<endl;
					}
					/*if (getEdgeVar(i).isFixed() && getEdgeVar(i).isFalse()) {
							ps.push(getEdgeVar(i).getValLit());
							//cout <<"included edge " <<i<<endl;
							}*/
				}
				Clause* expl = Clause_new(ps);
				expl->temp_expl = 1;
				sat.rtrail.last().push(expl);
				sat.confl = expl;
			}
			if (TREEPROP_DEBUG) {
				std::cout << "                                                           SAVED" << '\n';
			}
			// cout << lb <<" " <<totalWeight->getMax()<<" " <<mandatoryWeight<<endl;
			return false;
		}  // cout << total <<" " << totalWeight->getMax()<<endl;

		return true;
	}
};

// Very dodgy/experimental way of chekcing if it is better to combine the two bounding propagators
// or have the LP alone with the tree propagations.
#define TREEPROPAGATORCLASS 0
#define MINIMUMWTREEPROPAGATORCLASS 1
#define SUPERTREEPROPCLASSCHOOSE 0

#if (SUPERTREEPROPCLASSCHOOSE == TREEPROPAGATORCLASS)
#define SUPERTREEPROPCLASS TreePropagator
#else
#define SUPERTREEPROPCLASS MinimumWTreePropagator
#endif
#define PROPAGATE_PARENT 0

#if CPLEX_AVAILABLE && LEMON_AVAILABLE
class LPLBSteinerTreePropagator : public SUPERTREEPROPCLASS {
#if (SUPERTREEPROPCLASSCHOOSE == TREEPROPAGATORCLASS)
	vec<int> weights;
	Tint mandatoryWeight;
	int totalWeightVarID;
	Tint lowerBound;
#endif

	class DualAscent {
		int root;
		UF<Tint> uf;
		vector<set<int>> mergedAdj;
		vector<vector<int>>& endnodes;
		vector<int> terminals;
		vec<int> weights;

		std::pair<int, int> findCheapest(int repT) {
			std::pair<int, int> res(-1, -1);
			if (mergedAdj[repT].size() == 0) return res;

			set<int>::iterator it = mergedAdj[repT].begin();
			int argmin = *it;
			int min = weights[argmin];
			for (; it != mergedAdj[repT].end(); ++it) {
				if (weights[*it] < min) {
					argmin = *it;
					min = weights[argmin];
				}
			}
			int u = endnodes[argmin][0];
			int v = endnodes[argmin][1];
			int repU = uf.find(u);
			if (repU != repT) {
				res.first = repU;
			} else {
				res.first = uf.find(v);
			}
			res.second = argmin;
			return res;
		}

		void normalize(int rep, int subs) {
			set<int>::iterator it;
			for (it = mergedAdj[rep].begin(); it != mergedAdj[rep].end(); ++it) {
				weights[*it] -= subs;
			}
		}

		int mergeRep(int repO, int repT) {
			// cout <<"Start merging "<<repO<<" with "<<repT<<endl;
			int nR;
			if (mergedAdj[repO].size() < mergedAdj[repT].size()) {
				uf.unite(repT, repO);
				mergedAdj[repT].insert(mergedAdj[repO].begin(), mergedAdj[repO].end());
				nR = repT;
			} else {
				uf.unite(repO, repT);
				mergedAdj[repO].insert(mergedAdj[repT].begin(), mergedAdj[repT].end());
				nR = repO;
			}
			// cout <<"Merged, newR is " << nR<<endl;
			return nR;
		}

		void clean(int newR) {
			// cout <<"Start cleaning the adj of "<< newR<<endl;
			set<int>::iterator it;
			for (it = mergedAdj[newR].begin(); it != mergedAdj[newR].end();) {
				int u = endnodes[*it][0];
				int v = endnodes[*it][1];
				// cout <<"  Considering edge "<< *it <<endl;
				if (uf.find(u) != newR || uf.find(v) != newR) {
					++it;
				} else {
					mergedAdj[newR].erase(it++);
				}
			}
		}

		vector<set<int>> cuts;

	public:
		DualAscent(int r, int n, vector<vector<int>>& adj, vector<vector<int>>& en, vector<int> ts,
							 vec<int> ws)
				: root(r), uf(n), endnodes(en), terminals(ts), weights(ws) {
			for (unsigned int i = 0; i < adj.size(); i++) {
				mergedAdj.push_back(set<int>());
				for (int j = 0; j < adj[i].size(); j++) {
					mergedAdj[i].insert(adj[i][j]);
				}
			}
		}

		void merge(int u, int v) {
			int repU = uf.find(u);
			int repV = uf.find(v);
			if (repU == repV) return;
			clean(mergeRep(repU, repV));
		}

		vector<set<int>> getCuts() { return cuts; }

		int run(bool getCuts = false) {
			cuts.clear();
			bool didSth = true;
			int lowerbound = 0;
			while (didSth) {
				didSth = false;
				for (unsigned int i = 0; i < terminals.size(); i++) {
					int repR = uf.find(root);
					int t = terminals[i];
					int repT = uf.find(t);
					if (repT == repR) {
						continue;
					}
					didSth = true;
					// Here we can extract a cut
					if (getCuts) {
						cuts.push_back(mergedAdj[repT]);
					}
					std::pair<int, int> pair = findCheapest(repT);
					int repO = pair.first;
					if (repO == -1) continue;
					int edge = pair.second;
					lowerbound += weights[edge];
					normalize(repT, weights[edge]);
					int newR = mergeRep(repO, repT);
					clean(newR);
				}
			}
			// cout <<"Lower bound: "<<lowerbound<<endl;
			return lowerbound;
		}
	};

	class LemonFlow {
		typedef lemon::ListDigraph Graph;
		typedef Graph::Arc Edge;
		typedef Graph::Node Node;
		typedef Graph::ArcMap<double> LengthMap;
		typedef Graph::NodeMap<bool> CutMap;

		Graph g;
		int nodeCount;
		int edgeCount;
		std::vector<Node> lemonNodes;
		std::vector<Edge> lemonEdges;
		std::vector<int> terminals;
		LengthMap* capacity;
		vector<vector<int>>& endnodes;
		int rootNode;

		vec<Tint> isTerminal;

	public:
		LemonFlow(int _nodeCount, int _edgeCount, bool nodes[], int root,
							vector<vector<int>>& _endnodes)
				: nodeCount(_nodeCount),
					edgeCount(_edgeCount * 2),
					lemonNodes(_nodeCount),
					lemonEdges(_edgeCount * 2),
					endnodes(_endnodes),
					rootNode(root) {
			for (int i = 0; i < nodeCount; i++) {
				lemonNodes[i] = g.addNode();
			}
			for (int e = 0; e < _edgeCount; e++) {
				int u = endnodes[e][0];
				int v = endnodes[e][1];
				lemonEdges[e] = g.addArc(lemonNodes[u], lemonNodes[v]);
				lemonEdges[e + _edgeCount] = g.addArc(lemonNodes[v], lemonNodes[u]);
			}

			capacity = new LengthMap(g);
			for (int e = 0; e < edgeCount; e++) {
				(*capacity)[lemonEdges[e]] = 0;
			}
			for (int i = 0; i < nodeCount; i++) {
				if (nodes[i]) terminals.push_back(i);
				isTerminal.push(nodes[i]);
			}
		}

		~LemonFlow() { delete capacity; }

		void updateCapacities(vector<double> array) {
			for (unsigned int e = 0; e < array.size(); e++) {
				(*capacity)[lemonEdges[e]] = array[e];
				(*capacity)[lemonEdges[e + array.size()]] = array[e];
			}
		}

		bool run(std::vector<std::vector<int>>& violatedEdges, bool print = false) {
			unsigned int before = violatedEdges.size();
			std::set<int> edgesToInvert;
			vector<int>::iterator it;
			if (print) {
				int tmp = 0;
				for (int j = 0; j < isTerminal.size(); j++) tmp += isTerminal[j];
				// cout<<"               ->Start flow from "<<rootNode<<"   ("<<tmp<<endl;
			}
			// for (it = terminals.begin(); it != terminals.end(); /*j++*/) {
			for (int j = 0; j < isTerminal.size(); j++) {
				int other = j;  //*it;
				if (!isTerminal[other] || other == rootNode) {
					//++it;
					continue;
				}
				lemon::EdmondsKarp<Graph, LengthMap> flow(g, *capacity, lemonNodes[rootNode],
																									lemonNodes[other]);
				flow.run();
				float flowVal = flow.flowValue();

				if (print) cout << "Flow from " << rootNode << " to " << other << " is " << flowVal << endl;
				if (flowVal < 1) {
					bool cut[nodeCount];
					for (int i = 0; i < nodeCount; i++) {
						cut[i] = flow.minCut(lemonNodes[i]);
					}
					std::set<int> cuttingEdges;
					for (int e = 0; e < edgeCount / 2; e++) {
						int u = endnodes[e][0];
						int v = endnodes[e][1];
						if ((cut[u] && !cut[v]) || (cut[v] && !cut[u])) {
							cuttingEdges.insert(e);
						}
					}
					std::vector<int> cuttingEdgesV(cuttingEdges.begin(), cuttingEdges.end());
					violatedEdges.push_back(cuttingEdgesV);
					//++it;
				} else {
					isTerminal[j] = 0;
					// terminals.erase(it);
					//++it;
				}
			}
			return violatedEdges.size() > before;
		}
	};

	CPXENVptr cpx_env;
	CPXLPptr lp;
	vector<LemonFlow*> flows;
	Tint flows_sz;
	struct Action {
		int type;
		double oldlo;
		double oldup;
		double newbds;
		int oldNbRows;
		int newNbRows;
	};

	Tint historyPtr;
	vector<struct Action> history;
	vector<struct Action> tmpRecord;

public:
#if (SUPERTREEPROPCLASSCHOOSE == TREEPROPAGATORCLASS)

	IntVar* totalWeight;

	LPLBSteinerTreePropagator(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id>>& _adj,
														vec<vec<int>>& _en, IntVar* _w, vec<int> _ws)
			: SUPERTREEPROPCLASS(_vs, _es, _adj, _en),
				mandatoryWeight(0),
				lowerBound(0),
				historyPtr(0),
				totalWeight(_w),
				flows_sz(0) {
		for (int i = 0; i < _ws.size(); i++) {
			weights.push(_ws[i]);
		}

		totalWeightVarID = nbNodes() + nbEdges();
		totalWeight->attach(this, totalWeightVarID, EVENT_U);

		// for (int i = 0; i < nbEdges(); i++) {
		//     mandatoryWeight += (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue())? _ws[i] : 0;
		// }

		// Can set values in constructor?
		if (mandatoryWeight > totalWeight->getMin()) {
			totalWeight->setMin(mandatoryWeight);
		}

		// Initialise the minimum to the maximum value it can ever get.
		// We will try to bring it down from now on
		int upb = 0;
		for (int i = 0; i < nbEdges(); i++) {
			if (!getEdgeVar(i).isFixed() || getEdgeVar(i).isTrue()) upb += weights[i];
		}
		totalWeight->setMaxNotR(upb);

		/*
		//Remove non terminals of deg 1
		bool changes = false;
		do{
				changes = false;
				for (int i = 0; i < nbNodes(); i++) {
						if (!isTerminal[i] && !getNodeVar(i).isFixed()) {
								int deg = 0;
								int lastSeen = -1;
								for (int j = 0; j < adj[i].size(); j++) {
										if (!getEdgeVar(adj[i][j]).isFixed() || getEdgeVar(adj[i][j]).isTrue()){
												deg++;
												lastSeen = adj[i][j];
										}
								}
								if (deg == 1 && lastSeen != -1) {
										getNodeVar(i).setVal(false);
										getEdgeVar(lastSeen).setVal(false);
										changes = true;
								} else if (deg == 0) {
										getNodeVar(i).setVal(false);
										changes = true;
								}
						}
				}
		} while(changes);
		//*/
#else
	LPLBSteinerTreePropagator(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id>>& _adj,
														vec<vec<int>>& _en, IntVar* _w, vec<int> _ws)
			: SUPERTREEPROPCLASS(_vs, _es, _adj, _en, _w, _ws), historyPtr(0), flows_sz(0) {
#endif

#if !PROPAGATE_PARENT
		priority = 5;
#endif

		int status;
		cpx_env = CPXopenCPLEX(&status);
		if (!cpx_env) {
			char errmsg[CPXMESSAGEBUFSIZE];
			CPXgeterrorstring(cpx_env, status, errmsg);
			std::cerr << "Could not open CPLEX environment.\n" << errmsg;
			exit(EXIT_FAILURE);
		}

		rassert(CPXsetintparam(cpx_env, CPX_PARAM_SCRIND, CPX_OFF) == 0);

		rassert(lp = CPXcreateprob(cpx_env, &status, "fzn-cplex"));

		std::vector<double> lb(nbEdges(), 0);
		std::vector<double> ub(nbEdges(), 1);
		std::vector<double> obj;
		for (int i = 0; i < nbEdges(); ++i) obj.push_back(weights[i]);
		rassert(CPXnewcols(cpx_env, lp, nbEdges(), &obj[0], &lb[0], &ub[0], 0, 0) == 0);

		vector<node_id> terminals;
		for (int i = 0; i < nbNodes(); i++)
			if (isTerminal[i]) terminals.push_back(i);

		int min = totalWeight->getMin();
		for (unsigned int i = 0; i < terminals.size(); ++i) {
			DualAscent da(terminals[i], nbNodes(), adj, endnodes, terminals, weights);

			for (int e = 0; e < nbEdges(); e++) {
				if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
					da.merge(getEndnode(e, 0), getEndnode(e, 1));
				}
			}

			int tmp = da.run(true);
			min = min < tmp ? min : tmp;
			vector<set<int>> daCuts = da.getCuts();
			for (unsigned int i = 0; i < daCuts.size(); i++) {
				std::vector<double> rhs;
				std::vector<char> sense;
				std::vector<int> matbeg;
				std::vector<int> matind;
				std::vector<double> matval;
				rhs.push_back(1);
				sense.push_back('G');
				matbeg.push_back(0);
				std::set<int> cuti = daCuts[i];
				std::set<int>::iterator cutit;
				for (cutit = cuti.begin(); cutit != cuti.end(); ++cutit) {
					matind.push_back(*cutit);
					matval.push_back(1);
				}

				rassert(CPXaddrows(cpx_env, lp, 0, static_cast<int>(sense.size()),
													 static_cast<int>(matind.size()), &rhs[0], &sense[0], &matbeg[0],
													 &matind[0], &matval[0], 0, 0) == 0);
			}
		}
		if (totalWeight->getMin() < min) totalWeight->setMin(min);

		for (unsigned int i = 0; i < terminals.size(); ++i)
			flows.push_back(new LemonFlow(nbNodes(), nbEdges(), isTerminal, terminals[i], endnodes));
	}

	virtual bool propagateNewNode(int n) {
#if PROPAGATE_PARENT
		if (!SUPERTREEPROPCLASS::propagateNewNode(n)) return false;
#endif
		if (/*flows.size() == 0 && */ nb_innodes >= 2) {
			int some_node = n;
			bool isTerminal[nbNodes()];
			for (int i = 0; i < nbNodes(); i++) {
				if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue()) {
					// some_node = i;
					isTerminal[i] = true;
				} else {
					isTerminal[i] = false;
				}
			}
			flows.push_back(new LemonFlow(nbNodes(), nbEdges(), isTerminal, some_node, endnodes));
			flows_sz++;
			// cout<<"Add flow from "<<some_node<<" ("<<flows_sz<<endl;
		}

		return true;
	}

	virtual bool propagateNewEdge(int e) {
#if PROPAGATE_PARENT
		if (!SUPERTREEPROPCLASS::propagateNewEdge(e)) return false;
#endif
		int indices[1] = {e};
		char lu[1] = {'B'};
		double bd[1] = {1.0};

		double oldLb[1];
		rassert(CPXgetlb(cpx_env, lp, oldLb, e, e) == 0);
		double oldUb[1];
		rassert(CPXgetub(cpx_env, lp, oldUb, e, e) == 0);

		rassert(CPXchgbds(cpx_env, lp, 1, indices, lu, bd) == 0);

		struct Action act;
		act.type = e;
		act.oldlo = oldLb[0];
		act.oldup = oldUb[0];
		act.newbds = bd[0];
		tmpRecord.push_back(act);

		mandatoryWeight += weights[e];
		Clause* r = NULL;
		if (so.lazy) {
			vec<Lit> ps;
			ps.push();
			for (int i = 0; i < nbEdges(); i++) {
				if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) ps.push(getEdgeVar(i).getValLit());
			}
			r = Reason_new(ps);
		}
		if (totalWeight->getMin() < mandatoryWeight) totalWeight->setMin(mandatoryWeight, r);

		return true;
	}

	virtual bool propagateRemEdge(int e) {
#if PROPAGATE_PARENT
		if (!SUPERTREEPROPCLASS::propagateRemEdge(e)) return false;
#endif
		int indices[1] = {e};
		char lu[1] = {'B'};
		double bd[1] = {0.0};

		double oldLb[1];
		rassert(CPXgetlb(cpx_env, lp, oldLb, e, e) == 0);
		double oldUb[1];
		rassert(CPXgetub(cpx_env, lp, oldUb, e, e) == 0);

		rassert(CPXchgbds(cpx_env, lp, 1, indices, lu, bd) == 0);
		struct Action act;
		act.type = e;
		act.oldlo = oldLb[0];
		act.oldup = oldUb[0];
		act.newbds = bd[0];
		tmpRecord.push_back(act);
		return true;
	}

	void clearPropState() {
		SUPERTREEPROPCLASS::clearPropState();
		tmpRecord.clear();
	}

	void backtrack() {
		int current = history.size();
		while (current > historyPtr) {
			struct Action act = history[current - 1];
			if (act.type >= 0) {
				int indices[1] = {act.type};
				char l[1] = {'L'};
				char u[1] = {'U'};
				double bdl[1] = {act.oldlo};
				double bdu[1] = {act.oldup};
				rassert(CPXchgbds(cpx_env, lp, 1, indices, l, bdl) == 0);
				rassert(CPXchgbds(cpx_env, lp, 1, indices, u, bdu) == 0);
			} else {
				int nbRowsNow = CPXgetnumrows(cpx_env, lp);
				if (act.oldNbRows < nbRowsNow)
					rassert(CPXdelrows(cpx_env, lp, act.oldNbRows, nbRowsNow - 1) == 0);
			}
			current--;
			history.pop_back();
		}
		if (flows_sz < flows.size()) flows.resize(flows_sz);
	}

	virtual bool propagate() {
		backtrack();

		// if (nb_innodes < 2) return SUPERTREEPROPCLASS::propagate();

		// The methods in LPLBsteinr tree wont get called because MWST avoids
		// slow computation fo the lower bound by calling the treepropagator
		// methods when a new node is in, thus skipping thise methos. We update
		// the lower bounds by hand then
		std::unordered_set<int>::iterator it;
#if SUPERTREEPROPCLASSCHOOSE == MINIMUMWTREEPROPAGATORCLASS
		for (it = newFixedE.begin(); it != newFixedE.end(); ++it) {
			int e = *it;
			if (getEdgeVar(e).isTrue()) {
				int indices[1] = {e};
				char lu[1] = {'B'};
				double bd[1] = {1.0};

				double oldLb[1];
				rassert(CPXgetlb(cpx_env, lp, oldLb, e, e) == 0);
				double oldUb[1];
				rassert(CPXgetub(cpx_env, lp, oldUb, e, e) == 0);

				rassert(CPXchgbds(cpx_env, lp, 1, indices, lu, bd) == 0);

				struct Action act;
				act.type = e;
				act.oldlo = oldLb[0];
				act.oldup = oldUb[0];
				act.newbds = bd[0];
				tmpRecord.push_back(act);
			} else {
				int indices[1] = {e};
				char lu[1] = {'B'};
				double bd[1] = {0.0};

				double oldLb[1];
				rassert(CPXgetlb(cpx_env, lp, oldLb, e, e) == 0);
				double oldUb[1];
				rassert(CPXgetub(cpx_env, lp, oldUb, e, e) == 0);

				rassert(CPXchgbds(cpx_env, lp, 1, indices, lu, bd) == 0);

				struct Action act;
				act.type = e;
				act.oldlo = oldLb[0];
				act.oldup = oldUb[0];
				act.newbds = bd[0];
				tmpRecord.push_back(act);
			}
		}
#endif

#if PROPAGATE_PARENT
		if (!SUPERTREEPROPCLASS::propagate()) {
			// Undo all in tmpRecord
			for (unsigned int i = 0; i < tmpRecord.size(); i++) {
				struct Action act = tmpRecord[i];
				if (act.type >= 0) {
					int indices[1] = {act.type};
					char l[1] = {'L'};
					char u[1] = {'U'};
					double bdl[1] = {act.oldlo};
					double bdu[1] = {act.oldup};
					rassert(CPXchgbds(cpx_env, lp, 1, indices, l, bdl) == 0);
					rassert(CPXchgbds(cpx_env, lp, 1, indices, u, bdu) == 0);
				}
			}
			return false;
		}
#endif
		if (!flows.size()) return true;

		int nbRowsBefore = CPXgetnumrows(cpx_env, lp);

		bool cplexLoop = true;
		while (cplexLoop) {
			rassert(CPXsetlogfile(cpx_env, NULL) == 0);
			// rassert(CPXwriteprob(cpx_env, lp, "mipex1.lp", NULL) == 0);
			if (CPXgetnumrows(cpx_env, lp)) {
				rassert(CPXdualopt(cpx_env, lp) == 0);
				// std::cout << "Solution status = " << CPXgetstat(cpx_env, lp) << "\n";
				/*if (CPXgetstat(cpx_env, lp) == 3) {
						for (int i = 0; i < nbEdges(); i++) {
								cout<<"\tx"<<i+1<<" = "<< (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue())<<endl;
						}

						}*/
				rassert(CPXgetstat(cpx_env, lp) == CPX_STAT_OPTIMAL);

				std::vector<double> x(nbEdges());
				rassert(CPXgetx(cpx_env, lp, &x[0], 0, nbEdges() - 1) == 0);
				for (unsigned int i = 0; i < flows.size(); i++) flows[i]->updateCapacities(x);
			}

			std::vector<std::vector<int>> cuts;
			// cout<<"Flows size: "<<flows.size()<<endl;
			int fails = 0;
			for (unsigned int i = 0; i < flows.size(); i++) {
				std::vector<std::vector<int>> localcuts;
				bool fail = flows[i]->run(localcuts);
				if (fail) {
					for (unsigned int j = 0; j < localcuts.size(); j++) cuts.push_back(localcuts[j]);
				}
				fails += fail;

				// The way this was done before:
				/*
				if (!fail) {
						//cout <<"SOLUTION "<<i<<endl;
						// for (int j = 0; j < nbEdges(); ++j)
						//     std::cout << "x" << (j+1) << " " << x[j] << "\n";
						// flows[i]->run(localcuts,true);
						cplexLoop = false;
						break; //unnecessary
				}//*/
			}
			if (fails == 0) {
				// cout <<"SOLUTION "<<i<<endl;
				//  for (int j = 0; j < nbEdges(); ++j)
				//      std::cout << "x" << (j+1) << " " << x[j] << "\n";
				//  flows[i]->run(localcuts,true);
				cplexLoop = false;
				// break; //unnecessary
			}

			for (unsigned int i = 0; i < cuts.size(); i++) {
				std::vector<double> rhs;
				std::vector<char> sense;
				std::vector<int> matbeg;
				std::vector<int> matind;
				std::vector<double> matval;

				rhs.push_back(1);
				sense.push_back('G');
				matbeg.push_back(0);

				std::vector<int> cuti = cuts[i];
				for (unsigned int e = 0; e < cuti.size(); e++) {
					matind.push_back(cuti[e]);
					matval.push_back(1);
				}

				rassert(CPXaddrows(cpx_env, lp, 0, static_cast<int>(sense.size()),
													 static_cast<int>(matind.size()), &rhs[0], &sense[0], &matbeg[0],
													 &matind[0], &matval[0], 0, 0) == 0);
			}
		}

		int nbRowsAfter = CPXgetnumrows(cpx_env, lp);
		double objval = 0;
		bool alreadyDoneExplanation = false;
		vec<Lit> ps;
		if (nbRowsBefore == 0 && nbRowsAfter == 0) {
			for (int i = 0; i < nbEdges(); i++) {
				if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) {
					objval += weights[i];
					ps.push(getEdgeVar(i).getValLit());
				}
			}
			alreadyDoneExplanation = true;
		} else {
			rassert(CPXgetobjval(cpx_env, lp, &objval) == 0);
		}
		// std::cout << "Solution value = " << objval << "\n";

		if (objval > totalWeight->getMax()) {
			// Explanations:
			if (so.lazy) {
				if (!alreadyDoneExplanation) {
					double djs[nbEdges()];
					rassert(CPXgetdj(cpx_env, lp, djs, 0, CPXgetnumcols(cpx_env, lp) - 1) == 0);
					ps.push(totalWeight->getMaxLit());
					for (int i = 0; i < nbEdges(); i++) {
						if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) {
							ps.push(getEdgeVar(i).getValLit());
						} else if (djs[i] != 0 && getEdgeVar(i).isFixed()) {
							ps.push(getEdgeVar(i).getValLit());
						}
					}
				}
				Clause* expl = Clause_new(ps);
				expl->temp_expl = 1;
				sat.rtrail.last().push(expl);
				sat.confl = expl;
			}

			for (unsigned int i = 0; i < tmpRecord.size(); i++) {
				struct Action act = tmpRecord[i];
				if (act.type >= 0) {
					int indices[1] = {act.type};
					char l[1] = {'L'};
					char u[1] = {'U'};
					double bdl[1] = {act.oldlo};
					double bdu[1] = {act.oldup};
					rassert(CPXchgbds(cpx_env, lp, 1, indices, l, bdl) == 0);
					rassert(CPXchgbds(cpx_env, lp, 1, indices, u, bdu) == 0);
				}
			}
			if (nbRowsAfter > nbRowsBefore) {
				rassert(CPXdelrows(cpx_env, lp, nbRowsBefore, nbRowsAfter - 1) == 0);
			}

			return false;
		}

		if (nbRowsAfter > nbRowsBefore) {
			struct Action act;
			act.type = -1;
			act.oldNbRows = nbRowsBefore;
			act.newNbRows = nbRowsAfter;
			tmpRecord.push_back(act);
		}
		history.insert(history.end(), tmpRecord.begin(), tmpRecord.end());
		historyPtr = history.size();

		return true;
	}
};
#endif

void steiner_tree(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id>>& _adj,
									vec<vec<int>>& _en, IntVar* _w, vec<int> _ws) {
	/*    for (int i = 0; i < _nbNodes(); i++) {
	//cout << var(_vs[i].getValLit()) << " " << i << endl;
	tr[var(_vs[i].getValLit())] = i;
	}
	for (int i = 0; i < _nbEdges(); i++) {
	//cout << var(_es[i].getValLit()) << " " << (i + _nbNodes()) << endl;
	tr[var(_es[i].getValLit())] = i + _nbNodes();
	}*/

	new TreePropagator(_vs, _es, _adj, _en);
	new IncrementalMinimumWTreePropagator(_vs, _es, _adj, _en, _w, _ws);
}
