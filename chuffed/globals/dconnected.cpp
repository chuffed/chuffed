#include <chuffed/globals/dconnected.h>

#include <cstring>
#include <iostream>
using namespace std;

#define DEBUG 0

FilteredLT::FilteredLT(GraphPropagator* _p, int _r, std::vector<std::vector<int> > _en,
											 std::vector<std::vector<int> > _in, std::vector<std::vector<int> > _ou)
		: LengauerTarjan(_r, _en, _in, _ou), p(_p), visited_innodes(0) {}

int FilteredLT::get_visited_innodes() {
	// visited_innodes = 0;
	// for (int i = 0; i < p->nbNodes(); i++) {
	//     if (p->getNodeVar(i).isFixed() && p->getNodeVar(i).isTrue())
	//         if (visited_dfs(i))
	//             visited_innodes++;
	// }
	return visited_innodes;
}

void FilteredLT::init() {
	visited_innodes = 0;
	LengauerTarjan::init();
}

void FilteredLT::DFS(int r) {
	if (DEBUG)
		cout << "DFS Visiting " << r << " " << p->getNodeVar(r).isFixed()
				 << ((p->getNodeVar(r).isFixed()) ? p->getNodeVar(r).isTrue() : -1) << endl;
	if (p->getNodeVar(r).isFixed() && p->getNodeVar(r).isTrue()) visited_innodes++;
	LengauerTarjan::DFS(r);
}

bool FilteredLT::ignore_node(int u) {
	if (p->getNodeVar(u).isFixed() && p->getNodeVar(u).isFalse()) return true;
	return false;
}

bool FilteredLT::ignore_edge(int e) {
	if (p->getEdgeVar(e).isFixed() && p->getEdgeVar(e).isFalse()) return true;
	return false;
}

bool DReachabilityPropagator::correctDominator(int r, std::vector<bool>& v, int avoid) {
	if (r == avoid) return true;
	v[r] = true;
	if (DEBUG)
		cout << "Visiting " << r << " " << avoid << " who is "
				 << (getNodeVar(r).isFixed() ? (getNodeVar(r).isTrue() ? "in" : "out") : "unfixed") << endl;
	for (int i = 0; i < ou[r].size(); i++) {
		int e = ou[r][i];
		if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) continue;
		int o = getHead(e);
		if (getNodeVar(o).isFixed() && getNodeVar(o).isFalse()) continue;
		if (o == avoid) continue;
		if (v[o]) continue;
		correctDominator(o, v, avoid);
	}
	return true;
}

void DReachabilityPropagator::add_innode(int i) {
	if (DEBUG) cout << "Adding innode " << i << endl;
	assert(getNodeVar(i).isFixed());
	assert(getNodeVar(i).isTrue());
	in_nodes_tsize++;
	in_nodes_size++;
	in_nodes_list.push_back(i);
}

void DReachabilityPropagator::update_innodes() {
	if (in_nodes_tsize < in_nodes_size) {
		in_nodes_list.resize(in_nodes_tsize);
		in_nodes_size = in_nodes_tsize;
	}
}

int DReachabilityPropagator::get_some_innode_not(int other_than) {
	for (unsigned int i = 0; i < in_nodes_list.size(); i++) {
		if (in_nodes_list[i] != other_than) return in_nodes_list[i];
	}
	return -1;
}

int DReachabilityPropagator::get_root_idx() { return root; }

bool DReachabilityPropagator::remove_deg1(int u) {
	if (DEBUG) cout << "Remove deg1 from " << u << endl;
	if (getNodeVar(u).isFixed() && getNodeVar(u).isFalse()) return true;

	if (u == get_root_idx() && in_nodes_size > 1) {
		Clause* r = NULL;
		int out_deg = 0;
		int last_seen = -1;
		vec<Lit> ps_out;
		if (so.lazy) ps_out.push();
		for (int i = 0; i < ou[get_root_idx()].size(); i++) {
			int oe = ou[get_root_idx()][i];
			if (!getEdgeVar(oe).isFixed() || getEdgeVar(oe).isTrue()) {
				out_deg++;
				last_seen = oe;
			} else if (so.lazy) {
				ps_out.push(getEdgeVar(oe).getValLit());
			}
		}
		if (out_deg == 1 && in_nodes_size > 1 && !getEdgeVar(last_seen).isFixed()) {
			if (so.lazy) {
				int other = get_some_innode_not(u);
				assert(other != -1);
				ps_out.push(getNodeVar(get_root_idx()).getValLit());
				ps_out.push(getNodeVar(other).getValLit());
				r = Reason_new(ps_out);
			}
			getEdgeVar(last_seen).setVal(true, r);
			if (!propagateNewEdge(last_seen)) return false;
			last_state_e[last_seen] = VT_IN;
			new_edge.insert(last_seen);
			if (DEBUG) cout << "Edge in " << last_seen << endl;
			// Propagate New Edge already does this.
			// We enforce the other extremity if not there yet:
			//*
			if (!getNodeVar(getHead(last_seen)).isFixed()) {
				if (so.lazy) {
					vec<Lit> ps;
					ps.push();
					ps.push(getEdgeVar(last_seen).getValLit());
					r = Reason_new(ps);
				}
				getNodeVar(getHead(last_seen)).setVal(true, r);
				last_state_n[getHead(last_seen)] = VT_IN;
				add_innode(getHead(last_seen));
				new_node.insert(getHead(last_seen));
				if (DEBUG) cout << "Node in " << getHead(last_seen) << endl;
			} else if (getNodeVar(getHead(last_seen)).isFalse()) {
				if (so.lazy) {
					vec<Lit> psfail;
					psfail.push(getEdgeVar(last_seen).getValLit());
					Clause* expl = Clause_new(psfail);
					expl->temp_expl = 1;
					sat.rtrail.last().push(expl);
					sat.confl = expl;
				}
				if (DEBUG) cout << "False " << __FILE__ << __LINE__ << endl;
				return false;
			}  //*/

			return true;
		}
	}

	if (u != get_root_idx()) {
		int in_deg = 0;
		vec<Lit> ps_in;
		vec<Lit> ps_in_fail;
		if (so.lazy) ps_in.push();

		for (int i = 0; i < in[u].size(); i++) {
			int ie = in[u][i];
			if (!getEdgeVar(ie).isFixed() || getEdgeVar(ie).isTrue()) {
				in_deg++;
			} else if (so.lazy) {
				ps_in.push(getEdgeVar(ie).getValLit());
				ps_in_fail.push(getEdgeVar(ie).getValLit());
			}
		}

		if (in_deg > 0) return true;

		if (getNodeVar(u).isFixed() && getNodeVar(u).isTrue()) {
			// Fail because no way to get to this node
			if (so.lazy) {
				ps_in_fail.push(getNodeVar(u).getValLit());
				ps_in_fail.push(getNodeVar(get_root_idx()).getValLit());
				Clause* expl = Clause_new(ps_in_fail);
				expl->temp_expl = 1;
				sat.rtrail.last().push(expl);
				sat.confl = expl;
			}
			if (DEBUG) cout << "False " << u << " " << __FILE__ << __LINE__ << endl;
			return false;
		}
		Clause* r = NULL;
		if (!getNodeVar(u).isFixed()) {
			// Force the node to be out.
			if (so.lazy) {
				ps_in.push(getNodeVar(get_root_idx()).getValLit());
				r = Reason_new(ps_in);
			}
			getNodeVar(u).setVal(false, r);
			if (!propagateRemNode(u)) return false;
			last_state_n[u] = VT_OUT;
			rem_node.insert(u);
			if (DEBUG) cout << "Node out " << u << endl;
			//*
			if (so.lazy) {
				vec<Lit> ps;
				ps.push();
				ps.push(getNodeVar(u).getValLit());
				r = Reason_new(ps);
			}  //*/
			for (int i = 0; i < ou[u].size(); i++) {
				int oe = ou[u][i];
				if (!remove_deg1(getHead(oe))) {
					if (DEBUG) cout << "False " << __FILE__ << __LINE__ << endl;
					return false;
				}
				// Done by PropagateRemNode
				//*
				if (!getEdgeVar(oe).isFixed()) {
					getEdgeVar(oe).setVal(false, r);
					last_state_e[oe] = VT_OUT;
					rem_edge.insert(oe);
					if (DEBUG) cout << "Edge out " << oe << endl;

				} else if (getEdgeVar(oe).isTrue()) {
					if (so.lazy) {
						vec<Lit> psfail;
						psfail.push(getNodeVar(u).getValLit());
						Clause* expl = Clause_new(psfail);
						expl->temp_expl = 1;
						sat.rtrail.last().push(expl);
						sat.confl = expl;
					}
					if (DEBUG) cout << "False " << __FILE__ << __LINE__ << endl;
					return false;
				}  //*/
			}
		}
	}

	return true;
}

DReachabilityPropagator::DReachabilityPropagator(int _r, vec<BoolView>& _vs, vec<BoolView>& _es,
																								 vec<vec<edge_id> >& _in, vec<vec<edge_id> >& _out,
																								 vec<vec<int> >& _en)
		: GraphPropagator(_vs, _es, _en), lt(NULL), root(_r), in_nodes_tsize(0), in_nodes_size(0) {
	adj = vector<vector<int> >(_in.size(), vector<int>());
	for (int i = 0; i < _in.size(); i++) {
		for (int j = 0; j < _in[i].size(); j++) {
			adj[i].push_back(_in[i][j]);
		}
		for (int j = 0; j < _out[i].size(); j++) {
			adj[i].push_back(_out[i][j]);
		}
	}

	for (int i = 0; i < _in.size(); i++) {
		if (DEBUG) cout << "Incident to " << i << ": ";
		in.push_back(vector<int>());
		for (int j = 0; j < _in[i].size(); j++) {
			in[i].push_back(_in[i][j]);
			if (DEBUG) cout << _in[i][j] << ", ";
		}
		if (DEBUG) cout << endl;
	}

	for (int i = 0; i < _out.size(); i++) {
		ou.push_back(vector<int>());
		if (DEBUG) cout << "Outgoing from " << i << ": ";
		for (int j = 0; j < _out[i].size(); j++) {
			ou[i].push_back(_out[i][j]);
			if (DEBUG) cout << _out[i][j] << ", ";
		}
		if (DEBUG) cout << endl;
	}

	nodes2edge = std::vector<std::vector<int> >(nbNodes());
	for (int i = 0; i < nbNodes(); i++) nodes2edge[i] = std::vector<int>(nbNodes(), -1);
	for (int e = 0; e < nbEdges(); e++) {
		nodes2edge[getTail(e)][getHead(e)] = e;
	}

	last_state_n = new Tint[nbNodes()];
	last_state_e = new Tint[nbEdges()];
	memset(last_state_n, UNK, sizeof(Tint) * nbNodes());
	memset(last_state_e, UNK, sizeof(Tint) * nbEdges());

	std::vector<std::vector<int> > en(nbEdges(), std::vector<int>());
	for (int i = 0; i < _en.size(); i++)
		for (int j = 0; j < _en[i].size(); j++) en[i].push_back(_en[i][j]);

	std::vector<std::vector<int> > in(nbNodes(), std::vector<int>());
	for (int i = 0; i < _in.size(); i++)
		for (int j = 0; j < _in[i].size(); j++) in[i].push_back(_in[i][j]);

	std::vector<std::vector<int> > ou(nbNodes(), std::vector<int>());
	for (int i = 0; i < _out.size(); i++)
		for (int j = 0; j < _out[i].size(); j++) ou[i].push_back(_out[i][j]);

	lt = new FilteredLT(this, get_root_idx(), en, in, ou);

	for (int i = 0; i < nbNodes(); i++) getNodeVar(i).attach(this, i, EVENT_LU);

	for (int j = 0; j < nbEdges(); j++) getEdgeVar(j).attach(this, nbNodes() + j, EVENT_LU);

	if (!getNodeVar(root).isFixed()) {
		getNodeVar(root).setVal(true, NULL);
	} else if (getNodeVar(root).isFalse()) {
		return;  // Will fail anyway beacause of unreachability.
	}
	last_state_n[root] = VT_IN;
	add_innode(root);

	for (int i = 0; i < nbNodes(); i++) {
		remove_deg1(i);
	}
}

DReachabilityPropagator::~DReachabilityPropagator() {
	delete last_state_n;
	delete last_state_e;
	delete lt;
}

void DReachabilityPropagator::wakeup(int i, int c) {
	update_innodes();

	bool ignore = true;
	if (DEBUG) cout << "Wake up " << i << endl;
	if (i >= 0 && i < nbNodes()) {
		assert(getNodeVar(i).isFixed());
		if (getNodeVar(i).isTrue() && last_state_n[i] != VT_IN) {
			if (DEBUG) cout << "WakeUp Add node " << i << endl;
			if (DEBUG) cout << "Adding in " << __FILE__ << __LINE__ << endl;
			add_innode(i);
			new_node.insert(i);
			ignore = false;
		} else if (getNodeVar(i).isFalse() && last_state_n[i] != VT_OUT) {
			if (DEBUG) cout << "WakeUp Rem node " << i << endl;
			rem_node.insert(i);
			ignore = false;
		} else {
			if (DEBUG) cout << "Ignoring node " << i << endl;
		}
	}

	if (i >= nbNodes() && i < nbNodes() + nbEdges()) {
		i = i - nbNodes();
		assert(getEdgeVar(i).isFixed());
		if (getEdgeVar(i).isTrue() && last_state_e[i] != VT_IN) {
			if (DEBUG) cout << "WakeUp Add edge" << i << endl;
			new_edge.insert(i);
			ignore = false;
		} else if (getEdgeVar(i).isFalse() && last_state_e[i] != VT_OUT) {
			if (DEBUG) cout << "WakeUp Rem edge " << i << endl;
			rem_edge.insert(i);
			ignore = false;
		} else {
			if (DEBUG) cout << "Ignoring edge " << i << endl;
		}
	}

	if (!ignore) {
		pushInQueue();
	} else {
	}
}

bool DReachabilityPropagator::propagate() {
	update_innodes();  // In case I have not awaken
										 // through DReachabilityPropagator::wakeup method
	if (DEBUG) cout << "PROPAGATE" << endl;

	set<int>::iterator it;

	for (it = new_edge.begin(); it != new_edge.end(); ++it) {
		if (!propagateNewEdge(*it)) {
			if (DEBUG) cout << "False " << __FILE__ << __LINE__ << endl;
			return false;
		}
		last_state_e[*it] = VT_IN;
	}

	for (it = rem_node.begin(); it != rem_node.end(); ++it) {
		if (!propagateRemNode(*it)) {
			if (DEBUG) cout << "False " << __FILE__ << __LINE__ << endl;
			return false;
		}
		last_state_n[*it] = VT_OUT;
	}

	// In this class, nothing happens here, but this way inheriting classes
	// can be executed here
	for (it = new_node.begin(); it != new_node.end(); ++it) {
		if (!propagateNewNode(*it)) {
			if (DEBUG) cout << "False " << __FILE__ << __LINE__ << endl;
			return false;
		}
		last_state_n[*it] = VT_IN;
	}

	for (it = rem_edge.begin(); it != rem_edge.end(); ++it) {
		if (!propagateRemEdge(*it)) {
			if (DEBUG) cout << "False " << __FILE__ << __LINE__ << endl;
			return false;
		}
		last_state_e[*it] = VT_OUT;
	}

	if (!new_node.empty() || !rem_edge.empty()) {
		if (DEBUG) cout << "Checking new nodes and removed edges" << endl;
		if (!_propagateReachability()) {
			if (DEBUG) cout << "False " << __FILE__ << __LINE__ << endl;
			return false;
		}
	}

	if (DEBUG) cout << "True" << __FILE__ << __LINE__ << endl;

	return true;
}

void DReachabilityPropagator::clearPropState() {
	GraphPropagator::clearPropState();
	new_node.clear();
	rem_node.clear();
	new_edge.clear();
	rem_edge.clear();
}

bool DReachabilityPropagator::propagateRemEdge(int e) {
	assert(getEdgeVar(e).isFixed());
	assert(getEdgeVar(e).isFalse());
	int hd = getHead(e);
	int tl = getTail(e);
	if (DEBUG) cout << "Removing Edge " << e << endl;
	if (tl == get_root_idx()) {
		if (!remove_deg1(tl)) return false;
	}
	return remove_deg1(hd);
}

bool DReachabilityPropagator::propagateNewEdge(int edge) {
	assert(getEdgeVar(edge).isFixed());
	assert(getEdgeVar(edge).isTrue());
	std::vector<int> added_nodes;
	bool ok = GraphPropagator::coherence_innodes(edge, added_nodes);
	if (!ok) {
		return false;
	}
	for (unsigned int i = 0; i < added_nodes.size(); i++) {
		if (DEBUG) cout << "Adding in " << __FILE__ << __LINE__ << endl;
		last_state_n[added_nodes[i]] = VT_IN;
		add_innode(added_nodes[i]);
		new_node.insert(added_nodes[i]);
	}
	return true;
}

bool DReachabilityPropagator::propagateNewNode(int node) {
	assert(getNodeVar(node).isFixed());
	assert(getNodeVar(node).isTrue());
	return true;
}

bool DReachabilityPropagator::propagateRemNode(int node) {
	assert(getNodeVar(node).isFixed());
	assert(getNodeVar(node).isFalse());
	std::vector<int> remvd_edges;
	bool ok = GraphPropagator::coherence_outedges(node, remvd_edges);
	if (!ok) return false;
	for (unsigned int i = 0; i < remvd_edges.size(); i++) {
		last_state_e[remvd_edges[i]] = VT_OUT;
		rem_edge.insert(remvd_edges[i]);
	}
	return true;
}

bool DReachabilityPropagator::_propagateReachability(bool local) {
	update_innodes();
	// cout <<"PROPAGATE REACHABILITY"<<endl;
	lt->init();
	lt->LengauerTarjan::DFS();
	int reached = lt->get_visited_innodes();
	if (DEBUG)
		cout << "Reached " << reached << " in_nodes_tsize " << in_nodes_tsize << " in_nodes.size() "
				 << in_nodes_list.size() << endl;

	if (reached < in_nodes_tsize) {
		// FAIL because of not reaching some other node
		if (so.lazy) {
			int some_node = -1;
			for (unsigned int i = 0; i < in_nodes_list.size(); i++) {
				if (!lt->visited_dfs(in_nodes_list[i])) some_node = in_nodes_list[i];
			}
			assert(some_node != -1);
			vec<Lit> psfail;
			psfail.push(getNodeVar(get_root_idx()).getValLit());
			assert(getNodeVar(some_node).isFixed() && getNodeVar(some_node).isTrue());
			psfail.push(getNodeVar(some_node).getValLit());
			vector<bool> v(nbNodes(), false);
			vector<bool> falsev(nbNodes(), false);
			reverseDFStoBorder(some_node, v, falsev, psfail);
			if (DEBUG) cout << "Expl size: " << psfail.size() << endl;
			Clause* expl = Clause_new(psfail);
			expl->temp_expl = 1;
			sat.rtrail.last().push(expl);
			sat.confl = expl;
		}
		return false;
	}
	//*
	for (int i = 0; i < nbNodes(); i++) {
		if (!lt->visited_dfs(i) && !getNodeVar(i).isFixed()) {
			Clause* r = NULL;
			if (so.lazy) {
				vec<Lit> ps;
				ps.push();
				ps.push(getNodeVar(get_root_idx()).getValLit());
				vector<bool> v(nbNodes(), false);
				vector<bool> falsev(nbNodes(), false);
				reverseDFStoBorder(i, v, falsev, ps);
				r = Reason_new(ps);
			}
			getNodeVar(i).setVal(false, r);
			if (local) {
				if (!propagateRemNode(i)) return false;
				last_state_n[i] = VT_OUT;
			}
		}
	}  //*/

	lt->find_doms();
	// for (int i = 0; i < nbNodes(); i++)
	//     cerr <<"("<<i <<","<< lt->dominator(i)<<") ";
	// cerr<<endl;

	for (unsigned int i = 0; i < in_nodes_list.size(); i++) {
		int u = in_nodes_list[i];
		assert(getNodeVar(u).isFixed());
		assert(getNodeVar(u).isTrue());
		if (DEBUG) cout << "Looking at innode? u: " << u << " " << getNodeVar(u).isFixed() << endl;
		int dom_u = lt->dominator(u);

		if (u == dom_u || dom_u == -1)  // At the root
			continue;
		if (u == get_root_idx()) continue;

		vector<bool> visited = vector<bool>(nbNodes(), false);
		if (DEBUG) {
			cout << "STARTING DFS (avoid " << dom_u << ")" << endl;
			cout << "Nodes: ";
			for (int i = 0; i < nbNodes(); i++)
				cout << i << "(" << (getNodeVar(i).isFixed() ? (getNodeVar(i).isTrue() ? "I" : "O") : "U")
						 << "),";
			cout << endl;
			cout << "Edges: ";
			for (int i = 0; i < nbEdges(); i++)
				cout << i << "[" << getTail(i) << "," << getHead(i) << "]"
						 << "(" << (getEdgeVar(i).isFixed() ? (getEdgeVar(i).isTrue() ? "I" : "O") : "U")
						 << "),";
			cout << endl;
		}
		assert(correctDominator(get_root_idx(), visited, dom_u));
		if (visited[u]) cout << dom_u << " " << u << " " << get_root_idx() << endl;
		assert(!visited[u]);

		Clause* r = NULL;

		if (!getNodeVar(dom_u).isFixed()) {
			// Fix the dominator
			//*
			if (so.lazy) explain_dominator(u, dom_u, &r);

			if (DEBUG)
				cout << "Adding innode " << __FILE__ << __LINE__ << "(" << dom_u << " dominates " << u
						 << ")" << endl;
			getNodeVar(dom_u).setVal(true, r);
			if (local) {
				add_innode(dom_u);
				if (!propagateNewNode(dom_u)) return false;
				last_state_n[dom_u] = VT_IN;
				new_node.insert(dom_u);
			}
			//*/
		}

		if (getNodeVar(dom_u).isFixed() && getNodeVar(dom_u).isTrue()) {
			// Find bridge if any and enforce its endpoints
			int in_deg = 0;
			int last_incident = -1;
			vec<Lit> ps_in;
			if (so.lazy) ps_in.push();
			for (int i = 0; i < in[u].size(); i++) {
				int ie = in[u][i];
				if (!getEdgeVar(ie).isFixed() || getEdgeVar(ie).isTrue()) {
					in_deg++;
					last_incident = ie;
				} else if (so.lazy) {
					ps_in.push(getEdgeVar(ie).getValLit());
				}
			}
			if (in_deg == 1 && !getEdgeVar(last_incident).isFixed()) {
				//*
				if (so.lazy) {
					// ps_in.push(getNodeVar(dom_u).getValLit());
					ps_in.push(getNodeVar(u).getValLit());
					r = Reason_new(ps_in);
				}
				getEdgeVar(last_incident).setVal(true, r);
				if (local) {
					if (!propagateNewEdge(last_incident)) return false;
					if (DEBUG)
						cout << "Adding inedge " << last_incident << " " << __FILE__ << __LINE__ << "(" << dom_u
								 << " dominates " << u << ")" << endl;
					new_edge.insert(last_incident);
					last_state_e[last_incident] = VT_IN;
				}
				//*/
			}
		}
	}

	return true;
}

bool DReachabilityPropagator::propagateReachability() { return _propagateReachability(false); }

void DReachabilityPropagator::reverseDFS(int u, vector<bool>& v, int skip_n) {
	if (DEBUG) cout << "Reverse DFS from " << u << endl;
	v[u] = true;
	for (int i = 0; i < in[u].size(); i++) {
		int ie = in[u][i];
		if (getEdgeVar(ie).isFixed() && getEdgeVar(ie).isFalse()) continue;
		int o = getTail(ie);
		if (o == skip_n || v[o]) {
			continue;
		}
		reverseDFS(o, v, skip_n);
	}
}

void DReachabilityPropagator::reverseDFStoBorder(int u, vector<bool>& v, vector<bool>& my_side,
																								 vec<Lit>& expl, int skip_n) {
	if (DEBUG) cout << "Reverse DFS to border from " << u << endl;
	v[u] = true;
	for (int i = 0; i < in[u].size(); i++) {
		int ie = in[u][i];
		if (getEdgeVar(ie).isFixed() && getEdgeVar(ie).isFalse() && lt->visited_dfs(getTail(ie)) &&
				!my_side[getTail(ie)]) {
			expl.push(getEdgeVar(ie).getValLit());
			if (DEBUG) cout << "Added to explanation for dom/bridge edge:" << ie << endl;
		} else {
			int o = getTail(ie);
			if (o == skip_n || v[o]) {
				continue;
			}
			reverseDFStoBorder(o, v, my_side, expl, skip_n);
		}
	}
}

void DReachabilityPropagator::explain_dominator(int u, int dom, Clause** r) {
	if (DEBUG)
		cout << "Explain dominators " << getNodeVar(get_root_idx()).isFixed() << getNodeVar(u).isFixed()
				 << endl;
	vec<Lit> ps;
	ps.push();
	ps.push(getNodeVar(get_root_idx()).getValLit());
	if (getNodeVar(u).isFixed() && getNodeVar(u).isTrue()) ps.push(getNodeVar(u).getValLit());
	vector<bool> red(nbNodes(), false);
	reverseDFS(u, red, dom);
	vector<bool> v(nbNodes(), false);
	reverseDFStoBorder(u, v, red, ps, dom);
	if (DEBUG) cout << "Size expl for dominator " << ps.size() << endl;
	*r = Reason_new(ps);
}

void DReachabilityPropagator::explain_dominator(int u, int dom, vec<Lit>& ps) {
	if (DEBUG)
		cout << "Explain dominators " << getNodeVar(get_root_idx()).isFixed() << getNodeVar(u).isFixed()
				 << endl;
	ps.push();
	ps.push(getNodeVar(get_root_idx()).getValLit());
	if (getNodeVar(u).isFixed() && getNodeVar(u).isTrue()) ps.push(getNodeVar(u).getValLit());
	vector<bool> red(nbNodes(), false);
	reverseDFS(u, red, dom);
	vector<bool> v(nbNodes(), false);
	reverseDFStoBorder(u, v, red, ps, dom);
	if (DEBUG) cout << "Size expl for dominator " << ps.size() << endl;
}

bool DReachabilityPropagator::checkFinalSatisfied() {
	vector<bool> v = vector<bool>(nbNodes(), false);
	verificationDFS(get_root_idx(), v);
	for (int i = 0; i < nbNodes(); i++) {
		if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue()) {
			assert(v[i]);
			if (!v[i]) {
				cerr << "DreachabilityPropagator not satisfied (cannot reach node " << i << ") " << __FILE__
						 << ":" << __LINE__ << endl;
				return false;
			}
		}
	}

	return true;
}

void DReachabilityPropagator::verificationDFS(int r, vector<bool>& v) {
	v[r] = true;
	for (int i = 0; i < ou[r].size(); i++) {
		int e = ou[r][i];
		if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isFalse()) continue;
		if (!v[getHead(e)]) verificationDFS(getHead(e), v);
	}
}

void dconnected(int r, vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _in,
								vec<vec<edge_id> >& _out, vec<vec<int> >& _en) {
	DReachabilityPropagator* dr = new DReachabilityPropagator(r, _vs, _es, _in, _out, _en);
	// if (so.check_prop)
	//     engine.propagators.push(dr);
	// return dr;
}

DReachabilityPropagator* dreachable(int r, vec<BoolView>& _vs, vec<BoolView>& _es,
																		vec<vec<edge_id> >& _in, vec<vec<edge_id> >& _out,
																		vec<vec<int> >& _en, BoolView b) {
	DReachabilityPropagator* dr = new DReachabilityPropagatorReif(r, _vs, _es, _in, _out, _en, b);
	// if (so.check_prop)
	//     engine.propagators.push(dr);
	return dr;
}
