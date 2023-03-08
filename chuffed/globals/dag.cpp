#include <chuffed/globals/dag.h>

#include <iostream>

using namespace std;

DAGPropagator::DAGPropagator(int _r, vec<BoolView>& _vs, vec<BoolView>& _es,
														 vec<vec<edge_id> >& _in, vec<vec<edge_id> >& _out, vec<vec<int> >& _en)
		: DReachabilityPropagator(_r, _vs, _es, _in, _out, _en) {
	if (!getNodeVar(get_root_idx()).isFixed()) {
		getNodeVar(get_root_idx()).setVal(true);
	}

	// build the Tint array

	reachability = new Tint*[nbNodes()];
	int tints = nbNodes() / sizeof(int);
	tints += (nbNodes() % sizeof(int) == 0) ? 0 : 1;

	tints = nbNodes();

	for (int i = 0; i < nbNodes(); i++) {
		reachability[i] = new Tint[tints];
		for (int j = 0; j < tints; j++) {
			reachability[i][j] = 0;
		}
		// reachability[i][i/sizeof(int)] |= (1 << sizeof(int)-(i % sizeof(int)));
		reachability[i][i] = 1;
	}

	succs = vector<TrailedSuccList>();
	preds = vector<TrailedPredList>();
	for (int i = 0; i < nbNodes(); i++) {
		succs.emplace_back(nbNodes());
		preds.emplace_back(nbNodes());
	}
}

DAGPropagator::~DAGPropagator() {
	for (int i = 0; i < nbNodes(); i++) {
		delete[] reachability[i];
	}
	delete[] reachability;
}

void DAGPropagator::connectTo(int source, int dest) {
	/*
	for (int i = 0; i < nbNodes(); i++) {
			if (reachable(i,source)) {
					for (int j = 0; j < nbNodes(); j++)
							reachability[i][j] |= reachability[dest][j];
			}
			reachability[source][i] |= reachability[dest][i];
	}*/

	if (succs[source].get(dest)) {
		return;
	}
	std::pair<node_id, node_id> dd(dest, dest);
	succs[source].add(dd);
	preds[dest].add(source);

	std::pair<int, int> d_ptc(-1, -1);
	TrailedPredList::const_iterator it_p;
	for (it_p = preds[source].begin(); it_p != preds[source].end(); ++it_p) {
		succs[*it_p].get(source, &d_ptc);  // d_ptc == how to go from p to source
		assert(d_ptc.second != -1);
		d_ptc.first = dest;       // d_ptc == go from p to dest the same...
		succs[*it_p].add(d_ptc);  // ...way you go from p tou source
		preds[dest].add(*it_p);   // p preceeds dest
	}

	TrailedSuccList::const_iterator it_s;
	for (it_s = succs[dest].begin(); it_s != succs[dest].end(); ++it_s) {
		int s = (*it_s).first;
		std::pair<int, int> s_to_d(s, dest);
		succs[source].add(s_to_d);  // go from source to s through dest
		preds[s].add(source);       // sorce preceeds s

		for (it_p = preds[source].begin(); it_p != preds[source].end(); ++it_p) {
			succs[*it_p].get(source, &d_ptc);  // d_ptc == how to go from p to source
			assert(d_ptc.second != -1);
			d_ptc.first = s;          // d_ptc == go from p to s the same...
			succs[*it_p].add(d_ptc);  // ...way you go from p to source
			preds[s].add(*it_p);      // p preceeds s
		}
	}
}

bool DAGPropagator::propagateNewEdge(int e) {
	if (!DReachabilityPropagator::propagateNewEdge(e)) {
		return false;
	}

	if (!check_cycle(e)) {
		return false;
	}

	TrailedSuccList::const_iterator succ_taile = succs[getTail(e)].end();
	connectTo(getTail(e), getHead(e));
	processed_e[e] = true;

	// Only checking the new ones
	for (; succ_taile != succs[getTail(e)].end(); succ_taile++) {
		int n = (*succ_taile).first;
		for (int i : ou[n]) {
			prevent_cycle(i);
		}
	}
	/*
	//Check all reachable
	for (int n = 0; n < nbNodes(); n++) {
			if (reachable(n,getTail(e))) {
					for (int i = 0; i < in[n].size(); i++) {
							assert(!prevent_cycle(in[n][i])); //Assert because already cehcked before
					}
			}
	}
	*/

	/*    cout <<"Start "<<e<<endl;
	for (int i = 0; i < nbNodes(); i++) {
			for (int j = 0; j < nbNodes(); j++) {
					cout << reachability[i][j]<<",";
			}
			cout <<endl;
			}*/

	return true;
}

bool DAGPropagator::propagateNewNode(int n) {
	if (!DReachabilityPropagator::propagateNewNode(n)) {
		return false;
	}

	for (int i : in[n]) {
		prevent_cycle(i);
	}
	for (int i : ou[n]) {
		prevent_cycle(i);
	}

	processed_n[n] = true;
	return true;
}

void DAGPropagator::findPathFromTo(int u, int v, vec<Lit>& path) {
	assert(u != v);
	// 1-edge paths:
	int e = findEdge(u, v);
	if (e != -1 && getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
		path.push(getEdgeVar(e).getValLit());
		return;
	}

	vec<Lit> path2;
	if (path.size() == 1) {
		path2.push();
	}

	int current = u;
	while (current != v) {
		std::pair<int, int> pair;
		bool ok = succs[current].get(v, &pair);
		assert(ok);
		edge_id e = findEdge(current, pair.second);
		assert(e != -1);
		assert(getEdgeVar(e).isFixed());
		assert(getEdgeVar(e).isTrue());
		path.push(getEdgeVar(e).getValLit());
		current = pair.second;
	}
	// Longer paths:
	/*
	bool found_v = false;
	stack<node_id> s;
	s.push(u);
	vector<bool> vis = vector<bool>(nbNodes(), false);
	vector<int> parent = vector<int>(nbNodes(), -1);
	parent[u] = u;
	while(!s.empty()) {
			int curr = s.top();
			s.pop();
			vis[curr] = true;
			for (int i = 0; i < ou[curr].size(); i++) {
					int e = ou[curr][i];
					if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isFalse())
							continue;
					int o = getHead(e);
					if (!vis[o]) {
							s.push(o);
							parent[o] = curr;
							if (o == v) {
									found_v = true;
									break;
							}
					}
			}
			if (found_v)
					break;
			assert(!found_v);
	}
	assert(parent[v] != -1);
	assert(found_v);

	int curr = v;
	while (curr != u) {
			int e = findEdge(parent[curr],curr);
			assert(e != -1);
			assert(getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue());
			//cout <<e<<" ";
			path2.push(getEdgeVar(e).getValLit());
			curr = parent[curr];
	}
	assert(path.size() == path2.size());
	*/
}

bool DAGPropagator::check_cycle(int e) {
	if (reachable(getHead(e), getTail(e))) {
		if (so.lazy) {
			/*cout <<"Edges in: ";
			for (int i = 0; i < nbEdges(); i++) {
					if(getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue())
							cout <<i<<" ";
			}
			cout <<endl;*/
			vec<Lit> psfail;
			// cout <<"Path: ";
			findPathFromTo(getHead(e), getTail(e), psfail);
			psfail.push(getEdgeVar(e).getValLit());
			// cout <<endl;
			assert(psfail.size() > 0);
			Clause* expl = Clause_new(psfail);
			expl->temp_expl = 1;
			sat.rtrail.last().push(expl);
			sat.confl = expl;
		}
		return false;
	}
	return true;
}

bool DAGPropagator::prevent_cycle(int e) {
	if (!getEdgeVar(e).isFixed()) {
		if (reachable(getHead(e), getTail(e))) {
			Clause* r = nullptr;
			if (so.lazy) {
				vec<Lit> ps;
				ps.push();
				findPathFromTo(getHead(e), getTail(e), ps);
				r = Reason_new(ps);
			}
			getEdgeVar(e).setVal(false, r);
			return true;
		}
	}
	return false;
}

bool DAGPropagator::propagate() {
	processed_e = vector<bool>(nbEdges(), false);
	processed_n = vector<bool>(nbNodes(), false);

	if (!DReachabilityPropagator::propagate()) {
		return false;
	}

	set<int>::iterator it;

	for (it = new_edge.begin(); it != new_edge.end(); ++it) {
		if (!processed_e[*it]) {
			if (!propagateNewEdge(*it)) {
				return false;
			}
		}
	}

	for (it = new_node.begin(); it != new_node.end(); ++it) {
		if (!processed_n[*it]) {
			if (!propagateNewNode(*it)) {
				return false;
			}
		}
	}

	return true;
}

bool DAGPropagator::checkFinalSatisfied() {
	if (!DReachabilityPropagator::checkFinalSatisfied()) {
		return false;
	}
	vector<int> v = vector<int>(nbNodes(), 0);
	assert(check_correctness(get_root_idx(), v));
	return check_correctness(get_root_idx(), v);
}

bool DAGPropagator::check_correctness(int r, vector<int>& v) {
	v[r] = -1;
	// cout <<"Visiting "<<r<<endl;
	for (int e : ou[r]) {
		if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) {
			int hd = getHead(e);
			assert(hd != r);
			if (v[hd] == 0) {
				if (!check_correctness(hd, v)) {
					return false;
				}
			} else if (v[hd] == -1) {
				// cout <<"I saw "<<getHead(ou[r][i])<<" "<<v[ou[r][i]]<<endl;
				return false;
			}
		}
	}
	v[r] = 1;
	return true;
}

void dag(int r, vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _in,
				 vec<vec<edge_id> >& _out, vec<vec<int> >& _en) {
	auto* dag = new DAGPropagator(r, _vs, _es, _in, _out, _en);
	// if (so.check_prop)
	//     engine.propagators.push(dag);
}
