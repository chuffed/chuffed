#include <chuffed/core/propagator.h>
#include <chuffed/globals/tree.h>
#include <chuffed/support/union_find.h>

#include <algorithm>  // std::sort
#include <iostream>
#include <set>

using namespace std;

#define MIN(a, b) (((a) < (b)) ? (a) : (b))
#define MAX(a, b) (((a) > (b)) ? (a) : (b))

#define MSTPROP_DEBUG 0

struct sorter {
	bool operator()(std::pair<int, int> i, std::pair<int, int> j) { return (i.second < j.second); }
} sorter;

typedef std::pair<int, int> iipair;
typedef std::pair<int, iipair> iiipair;
/**
 * Returns the weight of an MST (pure MST)
 */
std::pair<int, int> Kruskal_weight(std::vector<int>& weights, int n,
																	 std::vector<vector<int> >& ends) {
	std::vector<iipair> sorted;

	for (unsigned int i = 0; i < weights.size(); i++) {
		sorted.emplace_back(i, weights[i]);
	}
	std::sort(sorted.begin(), sorted.end(), sorter);

	// Minimum ST

	unsigned int i = 0;
	int in = 0;
	int cost = 0;
	UF<int> uf(n);
	while (i < sorted.size() && in < n - 1) {
		int e = sorted[i].first;
		int w = sorted[i].second;
		if (!uf.connected(ends[e][0], ends[e][1])) {
			uf.unite(ends[e][0], ends[e][1]);
			in++;
			cost += w;
		}
		i++;
	}

	// Maximum ST
	unsigned int i2 = sorted.size() - 1;
	int in2 = 0;
	int cost2 = 0;
	UF<int> uf2(n);
	while (i2 >= 0 && in2 < n - 1) {
		int e = sorted[i2].first;
		int w = sorted[i2].second;
		if (!uf2.connected(ends[e][0], ends[e][1])) {
			uf2.unite(ends[e][0], ends[e][1]);
			in2++;
			cost2 += w;
		}
		i2--;
	}

	// cout <<"Solution is: "<<cost<<endl;
	return make_pair(cost, cost2);
}

class MSTPropagator : public TreePropagator {
	std::vector<iipair> sorted;

protected:
public:
	IntVar* w;
	std::vector<int> ws;

	struct sortByW {
		MSTPropagator* p;
		bool dec;
		sortByW(MSTPropagator* _p) : p(_p), dec(false) {}
		bool operator()(int e1, int e2) const {
			if (dec) {
				return p->ws[e1] > p->ws[e2];
			}
			return p->ws[e1] < p->ws[e2];
		}
	} sort_by_w;

	MSTPropagator(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _adj,
								vec<vec<int> >& _en, IntVar* _w, vec<int>& _ws)
			: TreePropagator(_vs, _es, _adj, _en), w(_w), sort_by_w(this) {
		for (int i = 0; i < _ws.size(); i++) {
			ws.push_back(_ws[i]);
		}

		for (unsigned int i = 0; i < ws.size(); i++) {
			sorted.emplace_back(i, ws[i]);
		}
		std::sort(sorted.begin(), sorted.end(), sorter);

		// for (int i = 0; i < _en.size(); i++)
		//     for (int j = 0; j < _en[i].size(); j++)
		//         endnodes[i].push(_en[i][j]);

		std::pair<int, int> kkl = Kruskal_weight(ws, nbNodes(), endnodes);
		if (kkl.first > w->getMin()) {
			w->setMin(kkl.first);
		}
		if (kkl.second < w->getMax()) {
			w->setMax(kkl.second);
		}
		w->attach(this, nbEdges() + nbNodes(), EVENT_LU);
	}

	void wakeup(int i, int c) override {
		if (i == nbEdges() + nbNodes()) {
			pushInQueue();
		} else {
			TreePropagator::wakeup(i, c);
		}
	}

	bool propagate() override {
		if (!TreePropagator::propagate()) {
			return false;
		}

		std::vector<int> support(nbEdges(), -1);
		std::vector<int> subs(nbEdges(), -1);
		vec<Lit> expl_fail;
		int c = 0;
		// Computing the MST with the inedges
		{
			UF<int> uf(nbNodes());
			RerootedUnionFind<int> ruf(nbNodes());
			std::vector<bool> already(nbEdges(), false);
			int in = 0;
			for (int i = 0; i < nbEdges(); i++) {
				if (getEdgeVar(i).isTrue()) {
					bool ok = ruf.unite(endnodes[i][0], endnodes[i][1]);
					assert(ok);
					uf.unite(endnodes[i][0], endnodes[i][1]);
					in++;
					c += ws[i];
				}
			}

			unsigned int i = 0;
			while (i < sorted.size()) {
				int e = sorted[i].first;
				if (getEdgeVar(e).isTrue()) {
					i++;
					continue;
				}
				// cout <<"Looking at "<<e<<endl;
				int w = sorted[i].second;
				int u = endnodes[e][0];
				int v = endnodes[e][1];
				bool connected = uf.connected(u, v);

				// I wanted to connected them, but I can't bc I'm out
				if (getEdgeVar(e).isFalse() && !connected) {
					if (!already[e]) {
						expl_fail.push(getEdgeVar(e).getValLit());
						already[e] = true;
					}
				}
				// I wanted to connected them, but I can't bc They are already connected
				else if (connected) {
					vector<int> path = ruf.connectionsFromTo(u, v);
					int arg_maxw = findEdge(path[0], path[1]);
					// int below_cost = 0;
					// int above_cost = 0;
					bool heavier = false;
					//  ^ used to see if the path used mandatory edges BECAUSE e is
					// forbidden and there in no other way of connecting its endnodes

					for (int k = 0; k < path.size() - 1; k++) {
						int e_path = findEdge(path[k], path[k + 1]);
						arg_maxw = ws[e_path] > ws[arg_maxw] ? e_path : arg_maxw;
						heavier |= ws[e_path] > w;
						assert(e_path != e);
						subs[e_path] =
								(subs[e_path] == -1) ? e : ((ws[subs[e_path]] > ws[e]) ? e : subs[e_path]);
					}
					if (heavier) {
						if (getEdgeVar(e).isFalse()) {
							expl_fail.push(getEdgeVar(e).getValLit());
						}
					}
					support[e] = arg_maxw;
				}
				// I can connect them!
				if (in < nbNodes() - 1 && !getEdgeVar(e).isFixed() && !connected) {
					bool ok = ruf.unite(u, v);
					assert(ok);
					uf.unite(u, v);
					in++;
					c += w;
				}
				i++;
			}
		}
		// Lower bound:
		if (c > w->getMax()) {
			if (so.lazy) {
				explain_mandatory(expl_fail, c, subs);
				// assert(expl_fail.size() >= 1); //dont really need it
				expl_fail.push(w->getMaxLit());
				// vec<Lit> ps; fullExpl(ps);
				Clause* expl = Clause_new(expl_fail);
				expl->temp_expl = 1;
				sat.rtrail.last().push(expl);
				sat.confl = expl;
			}
			return false;
		}
		bool computed_expl = false;
		vec<Lit> ps;
		for (int e = 0; e < nbEdges(); e++) {
			if (support[e] < 0 || getEdgeVar(e).isFixed()) {
				continue;
			}

			if (c - ws[support[e]] + ws[e] > w->getMax()) {
				Clause* r = nullptr;
				if (so.lazy) {
					if (!computed_expl) {
						ps.push();
						for (int i = 0; i < expl_fail.size(); i++) {
							ps.push(expl_fail[i]);
						}
						explain_mandatory(ps, c, subs);
						ps.push(w->getMaxLit());
						computed_expl = true;
					}
					// vec<Lit> ps2; ps2.push(); fullExpl(ps2);
					r = Reason_new(ps);
				}
				getEdgeVar(e).setVal(false, r);
			}
		}
		return true;
	}

	void explain_mandatory(vec<Lit>& expl_fail, int c, std::vector<int>& substitute) {
		int add = 0;
		/*std::vector<int> in_edges;
			for (int j = 0; j < nbEdges(); j++)
			if (es[j].isFixed() && es[j].isTrue())
			in_edges.push_back(j);
		*/
		if (in_edges.empty()) {
			return;
		}
		std::vector<int> in_edges_cpy = in_edges;
		// sort_by_w.dec = true;
		sort(in_edges_cpy.begin(), in_edges_cpy.end(), sort_by_w);
		// sort_by_w.dec = false;

		// bool prevention_case = c <= w->getMax();

		int cost = c;
		for (int e : in_edges_cpy) {
			if (substitute[e] == -1 || ws[e] <= ws[substitute[e]]) {
				continue;
			}
			if (cost - ws[e] + ws[substitute[e]] > w->getMax()) {
				cost = cost - ws[e] + ws[substitute[e]];
			} else {
				expl_fail.push(getEdgeVar(e).getValLit());
				add++;
			}
		}
	}
};

MSTPropagator* mst_p;

void mst(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _adj, vec<vec<int> >& _en,
				 IntVar* _w, vec<int>& _ws) {
	mst_p = new MSTPropagator(_vs, _es, _adj, _en, _w, _ws);
}

bool sortPairKey2(std::pair<int, int> u, pair<int, int> v) { return u.second < v.second; }

class DCMSTSearch : public BranchGroup {
	IntVar* root;
	std::vector<int>& ws;
	std::vector<std::vector<int> > dist;
	vector<std::pair<int, int> > sums;
	vector<std::vector<std::pair<int, int> > > costs;

	int int_cur;
	Tint curr_root_idx;
	Tint h;

	DCMSTSearch(vec<Branching*>& _x, VarBranch vb, bool t)
			: BranchGroup(_x, vb, t), ws(mst_p->ws), dist(mst_p->nbNodes()) {
		root = (IntVar*)(x[0]);

		int max_w = ws[0];
		for (int i = 0; i < mst_p->nbEdges(); i++) {
			if (ws[i] > max_w) {
				max_w = ws[i];
			}
		}

		for (int i = 0; i < mst_p->nbNodes(); i++) {
			for (int j = 0; j < mst_p->nbNodes(); j++) {
				if (i == j) {
					dist[i].push_back(0);
				} else {
					dist[i].push_back(max_w + 1);
				}
			}
		}

		for (int i = 0; i < mst_p->nbEdges(); i++) {
			dist[mst_p->getEndnode(i, 0)][mst_p->getEndnode(i, 1)] = ws[i];
			dist[mst_p->getEndnode(i, 1)][mst_p->getEndnode(i, 0)] = ws[i];
		}

		for (int i = 0; i < mst_p->nbNodes(); i++) {
			for (int j = 0; j < mst_p->nbNodes(); j++) {
				for (int k = 0; k < mst_p->nbNodes(); k++) {
					if (dist[i][j] > dist[i][k] + dist[k][j]) {
						dist[i][j] = dist[i][k] + dist[k][j];
					}
				}
			}
		}

		if (((IntVar*)x[0])->getMax() == mst_p->nbNodes()) {
			//            cout << "Even" <<endl;
			for (int i = 0; i < mst_p->nbNodes(); i++) {
				int s = 0;
				for (int j = 0; j < mst_p->nbNodes(); j++) {
					s += dist[i][j];
				}
				sums.emplace_back(i, s);
			}

			sort(sums.begin(), sums.end(), sortPairKey2);
			// for (int i = 0; i < sums.size(); i++) {
			//     cout <<sums[i].first<<",";
			// }
			// cout<<endl;

			for (int i = 0; i < mst_p->nbNodes(); i++) {
				vector<std::pair<int, int> > cost;
				for (int j = 0; j < mst_p->nbNodes(); j++) {
					cost.emplace_back(j, dist[i][j]);
				}
				sort(cost.begin(), cost.end(), sortPairKey2);
				reverse(cost.begin(), cost.end());
				costs.push_back(cost);
			}
		} else {
			//     cout <<"Odd"<<endl;
			std::vector<std::pair<int, int> > tmp;
			for (int i = 0; i < mst_p->nbNodes(); i++) {
				int s = 0;
				for (int j = 0; j < mst_p->nbNodes(); j++) {
					s += dist[i][j];
				}
				tmp.emplace_back(i, s);
			}
			for (int e = 0; e < mst_p->nbEdges(); e++) {
				int i = mst_p->getEndnode(e, 0);
				int j = mst_p->getEndnode(e, 1);
				// Is v the MIN or the SUM?? Its not clear from the paper that
				// describes the searchs trategy....
				int v = MIN(tmp[i].second, tmp[j].second);
				sums.emplace_back(e, v);
				vector<std::pair<int, int> > cost;
				for (int k = 0; k < mst_p->nbNodes(); k++) {
					cost.emplace_back(k, MIN(dist[i][k], dist[j][k]));
				}
				sort(cost.begin(), cost.end(), sortPairKey2);
				reverse(cost.begin(), cost.end());
				costs.push_back(cost);
			}
			sort(sums.begin(), sums.end(), sortPairKey2);
		}
		cur = 0;

		last_dec_level = engine.decisionLevel();
		max_h = ((IntVar*)x[1])->getMax();
	}

public:
	static DCMSTSearch* search;
	static DCMSTSearch* getDCMSTSearch(vec<Branching*>& _x, VarBranch vb, bool t) {
		if (search == nullptr) {
			search = new DCMSTSearch(_x, vb, t);
		}
		return search;
	}

	struct Action {
		int idx;
		int h;
		int act;
	};

	bool finished() override {
		if (fin != 0) {
			return true;
		}
		for (int i = 0; i < x.size(); i++) {
			if (!x[i]->finished()) {
				// cout <<"Not finished with "<<i<<endl;
				return false;
			}
		}
		fin = 1;
		return true;
	}

	int max_h;
	std::vector<struct Action> decisions;
	std::vector<std::pair<int, int> > to_look;
	int last_dec_level;
	bool backtrack() {
		// cout <<"dec level "<< engine.decisionLevel()<<endl;
		// cout <<"sz vs sz_t "<<sz<<" "<<(int)sz_t<<endl;
		// cout <<"last dec level" <<last_dec_level<<endl;
		if (last_dec_level >= engine.decisionLevel()) {             // sz > sz_t) {
			int remove = -(engine.decisionLevel() - last_dec_level);  // sz - sz_t - 1;
			// cout <<"Removing "<<remove<<endl;
			for (int i = 0; i < remove; i++) {
				decisions.pop_back();
			}
			last_dec_level = engine.decisionLevel();
			return true;
		}
		last_dec_level = engine.decisionLevel();
		return false;
	}

	struct Action nextAction(struct Action prev) const {
		struct Action next = {-1, -1, -1};
		int h = prev.h;
		if (prev.idx + 1 == (int)to_look.size()) {
			h++;
		}
		if (h > max_h) {  // Should have finished
			// assert(finished());
			return next;
		}

		next.idx = (prev.idx + 1) % to_look.size();
		next.h = h;
		next.act = 0;
		return next;
	}

	bool applyAction(struct Action t, DecInfo** di) {
		if (t.act == -1) {
			// Finish!
			assert(finished());
			*di = nullptr;
			return true;
		}
		int v = to_look[t.idx].first;
		// cout <<"v "<<v<<endl;
		if (t.act == 0) {
			// cout <<"MIN"<< ((IntVar*)x[v+1])->getMin();
			// if (((IntVar*)x[v+1])->isFixed())
			//     cout <<"fixed ";
			if (!((IntVar*)x[v + 1])->isFixed() && ((IntVar*)x[v + 1])->indomain(t.h)) {
				*di = new DecInfo(x[v + 1], t.h, 0);
				// cout << ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>Node  "<< v+1 << " wont take value
				// "<<t.h << endl;
				return true;
			}
			return false;
		}
		if (t.act == 1) {
			if (!((IntVar*)x[v + 1])->isFixed() && ((IntVar*)x[v + 1])->indomain(t.h)) {
				*di = new DecInfo(x[v + 1], t.h, 1);
				// cout << ">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>Node  "<< v+1 << " will take value
				// "<<t.h << endl;
				return true;
			}
			return false;
		}
		assert(false);
		return false;  // Never
	}
	//* Naive version below. This uses a list of actions to
	// Restore the sate and know here I am in the loop at all times.
	DecInfo* branch() override {
		// cout <<"Enter branch"<<endl;
		DecInfo* di = nullptr;
		if (!((IntVar*)x[0])->finished()) {
			for (auto& sum : sums) {
				if (((IntVar*)x[0])->indomain(sum.first + 1)) {
					di = new DecInfo(x[0], sum.first + 1, 1);
					// cout <<"New root "<<i<<" "<<sums[i].first<<" "<<(x[0]) <<endl;
					// for (int j = 0; j < costs[sums[i].first].size(); j++) {
					//     cout <<  (costs[sums[i].first][j].first) <<",";
					// }
					// cout<<endl;
					to_look = costs[sum.first];
					decisions.clear();
					last_dec_level = engine.decisionLevel() - 1;
					// cout <<"foudn new root"<<endl;
					return di;
				}
			}
			return nullptr;
		}
		if (finished()) {
			return nullptr;
		}
		struct Action nttd = {0, 0, -1};
		if (backtrack()) {
			// cout <<">>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>BT"<<endl;
			assert(!decisions.empty() || engine.decisionLevel() == 0);
			if (engine.decisionLevel() == 0) {
				assert(last_dec_level == 0);
				decisions.clear();
				// Will go to decisions.empty()
			} else {
				struct Action failed = decisions.back();
				// if (failed.act != 0)
				//     cout <<"failed.act "<<failed.act<<endl;
				assert(failed.act == 0 || so.lazy);
				nttd.idx = failed.idx;
				nttd.h = failed.h;
				nttd.act = 1;
				// cout << "bt nttd "<<nttd.idx<<" "<<nttd.h<<" "<<nttd.act<<endl;
				decisions.pop_back();
			}
		}

		if (decisions.empty()) {
			nttd.idx = 0;
			nttd.h = 1;
			nttd.act = 0;
		} else if (nttd.act == -1) {
			nttd = nextAction(decisions.back());
		}
		// cout << "nttd "<<nttd.idx<<" "<<nttd.h<<" "<<nttd.act<<endl;
		while (!applyAction(nttd, &di)) {
			// cout <<"Could not apply"<<endl;
			nttd = nextAction(nttd);
			// cout << "nxt nttd "<<nttd.idx<<" "<<nttd.h<<" "<<nttd.act<<endl;
		}
		// cout << "di "<<di<<endl;
		if (di != nullptr) {
			decisions.push_back(nttd);
			assert(nttd.h < max_h + 1);
		}

		assert(di != nullptr || finished());
		return di;
	}  //*/

	/*Slower way of doing it, always goes through the entire loop.
		//The code above uses a list of actions to know where I am in the loop
		//and continue.
	DecInfo* branch() {
			DecInfo* di = NULL;
			if (!((IntVar*)x[0])->finished()) {
					for (unsigned int i = 0; i < sums.size(); i++) {
							if (((IntVar*)x[0])->indomain(sums[i].first+1)) {
									di = new DecInfo(x[0],sums[i].first+1,1);
									return di;
							}
					}
					return NULL;
			}
			if (finished())
					return NULL;

			for (int h = 1; h < max_h; h++) {
					for (int i = 0; i < costs[0].size(); i++) {
							int v = costs[((IntVar*)x[0])->getVal()-1][i].first;
							if (!((IntVar*)x[v+1])->isFixed() && ((IntVar*)x[v+1])->indomain(h)) {
									di = new DecInfo(x[v+1],h,0);
							}
					}
			}

			return di;
			}*/
};
DCMSTSearch* DCMSTSearch::search = nullptr;
