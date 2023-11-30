#include "chuffed/globals/bounded_path.h"

#include "chuffed/branching/branching.h"
#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/core/propagator.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/core/sat.h"
#include "chuffed/globals/globals.h"
#include "chuffed/globals/graph.h"
#include "chuffed/support/misc.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/bool-view.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/vars.h"

#include <cassert>
#include <cstring>
#include <iostream>
#include <utility>
#include <vector>

#define DEBUG 0

// #define KF
#define DPLB 1
// #define BASIC_EXPL

#define NB_CLUSTERS 5
#define CLUSTER_LIMIT 20

#define GiveFailureExplanation(v) \
	Clause* __expl = Clause_new(v); \
	__expl->temp_expl = 1;          \
	sat.rtrail.last().push(__expl); \
	sat.confl = __expl;

#define ReasonNew(v) Reason_new(v);
// #define ReasonNew(v)               __reason_new(this); //DEBUG

// Clause* __reason_new(BoundedPathPropagator* p) {
//     vec<Lit> x = p->fullExpl(false);
//     return Reason_new(x);
// }
// Clause* __clause_new(BoundedPathPropagator* p) {
//     vec<Lit> x = p->fullExpl(true);
//     return Clause_new(x);
// }

void BoundedPathPropagator::constructGraph(vec<vec<edge_id> >& _in, vec<vec<edge_id> >& _out,
																					 vec<vec<int> >& /*en*/) {
	adj = std::vector<std::vector<int> >(_in.size(), std::vector<int>());
	for (int i = 0; i < _in.size(); i++) {
		for (int j = 0; j < _in[i].size(); j++) {
			adj[i].push_back(_in[i][j]);
		}
		for (int j = 0; j < _out[i].size(); j++) {
			adj[i].push_back(_out[i][j]);
		}
	}

	in = std::vector<std::vector<int> >(nbNodes(), std::vector<int>());
	for (int i = 0; i < _in.size(); i++) {
		for (int j = 0; j < _in[i].size(); j++) {
			in[i].push_back(_in[i][j]);
		}
	}

	ou = std::vector<std::vector<int> >(nbNodes(), std::vector<int>());
	for (int i = 0; i < _out.size(); i++) {
		for (int j = 0; j < _out[i].size(); j++) {
			ou[i].push_back(_out[i][j]);
		}
	}

	nodes2edge = std::vector<std::vector<int> >(nbNodes());
	for (int i = 0; i < nbNodes(); i++) {
		nodes2edge[i] = std::vector<int>(nbNodes(), -1);
	}
	for (int e = 0; e < nbEdges(); e++) {
		nodes2edge[getTail(e)][getHead(e)] = e;
	}

	last_state_e = new Tint[nbEdges()];
	memset(last_state_e, UNK, sizeof(Tint) * nbEdges());

	was_shortest = new Tint[nbEdges()];
	memset(was_shortest, 0, sizeof(Tint) * nbEdges());

	for (int j = 0; j < nbEdges(); j++) {
		getEdgeVar(j).attach(this, j, EVENT_LU);
		if (getHead(j) == getTail(j)) {
			if (!getEdgeVar(j).isFixed()) {
				getEdgeVar(j).setVal(false);
			}
		}
	}

	last_state_n = new Tint[nbNodes()];
	memset(last_state_n, UNK, sizeof(Tint) * nbNodes());
	for (int j = 0; j < nbNodes(); j++) {
		getNodeVar(j).attach(this, nbEdges() + j, EVENT_LU);
	}

	if (!getNodeVar(source).isFixed()) {
		getNodeVar(source).setVal(true, nullptr);
	}
	if (!getNodeVar(dest).isFixed()) {
		getNodeVar(dest).setVal(true, nullptr);
	}
}

void BoundedPathPropagator::constructWeights(vec<int>& _ws, IntVar* /*_w*/) {
	_ws.copyTo(ws);
	for (int j = 0; j < nbEdges(); j++) {
		getEdgeVar(j).attach(this, j, EVENT_LU);
		if (ws[j] < 0) {
			if (!getEdgeVar(j).isFixed()) {
				getEdgeVar(j).setVal(false);
			}
		}
	}
	w->attach(this, -1, EVENT_LU);
}
void BoundedPathPropagator::constructWeights(vec<vec<int> >& _wst, IntVar* /*_w*/) {
	_wst.copyTo(wst);
	w->attach(this, -1, EVENT_LU);
}

void BoundedPathPropagator::constructBasicExplanations() {
	// Leave a space at the beginning for the literal fo the maximim weight.
	//* OLD EXPLANATIONS
#ifdef BASIC_EXPL
	fail_expl.push();
	prop_expl.push();
	prop_expl.push();
	explanation_size = 1;
	explanation_tsize = 1;
#endif
	//*/
	// Can't do until init.c has run
	// fail_expl[0] = w->getMaxLit();
	// prop_expl[1] = w->getMaxLit();
}

void BoundedPathPropagator::rootLevelPropagation() {
	forward_sp->run();
	if (forward_sp->distTo(dest) > w->getMin()) {
		if (DEBUG) {
			std::cout << "Setting Minimum to " << forward_sp->distTo(dest) << '\n';
		}
		w->setMin(forward_sp->distTo(dest), nullptr);
	}
	if (DEBUG) {
		std::cout << "Forward Dijkstra " << forward_sp->distTo(dest) << '\n';
	}
	if (DEBUG) {
		std::cout << "Min: " << w->getMin() << '\n';
	}
	if (DEBUG) {
		std::cout << "Max: " << w->getMax() << '\n';
	}
	backward_sp->run();
	initial_dist_from_dest = std::vector<int>(nbNodes(), -1);
	for (int i = 0; i < nbNodes(); i++) {
		initial_dist_from_dest[i] = backward_sp->distTo(i);
	}

	if (DPLB) {
		dkm = new ImplementedDynamicKMeans(NB_CLUSTERS, nbNodes(), nbEdges(), this);
		mandatory_sp->set_clustering(dkm);
		initial_mandatory_sp->set_clustering(dkm);
		const bool set_target = false;
		if (DEBUG) {
			std::cout << "Running DPLB in constructor" << '\n';
		}
		const int lb = initial_mandatory_sp->run(nullptr, set_target);
		if (lb > w->getMin()) {
			if (DEBUG) {
				std::cout << "Setting Minimum to " << forward_sp->distTo(dest) << '\n';
			}
			w->setMin(lb, nullptr);
		}
		if (DEBUG) {
			std::cout << "Done " << lb << '\n';
		}
	}
}

BoundedPathPropagator::BoundedPathPropagator(int _s, int _d, vec<BoolView>& _vs, vec<BoolView>& _es,
																						 vec<vec<edge_id> >& _in, vec<vec<edge_id> >& _out,
																						 vec<vec<int> >& _en, vec<int>& _ws, IntVar* _w)
		: GraphPropagator(_vs, _es, _en),
			forward_sp(nullptr),
			backward_sp(nullptr),
			explain_sp(nullptr),
			dkm(nullptr),
			source(_s),
			dest(_d),
			w(_w),
			explanation_tsize(0),
			explanation_size(0),
			in_nodes_tsize(0),
			in_nodes_size(0) {
	priority = 5;

	constructGraph(_in, _out, _en);
	constructWeights(_ws, _w);

	std::vector<std::vector<int> > en(nbEdges(), std::vector<int>());
	for (int i = 0; i < _en.size(); i++) {
		for (int j = 0; j < _en[i].size(); j++) {
			en[i].push_back(_en[i][j]);
		}
	}

	std::vector<int> weights(nbEdges(), -1);
	for (int i = 0; i < nbEdges(); i++) {
		weights[i] = ws[i];
	}
	kosaraju = new FilteredKosarajuSCC(this, nbNodes(), ou, in, en);

	forward_sp = new FilteredDijkstra(this, source, en, in, ou, weights);
	explain_sp = new ExplainerDijkstra(this, source, en, in, ou, weights);
	mandatory_explainer_sp = new ExplainerDijkstraMandatory(this, source, dest, en, in, ou, weights);
	mandatory_explainer_sp->init();

	for (int i = 0; i < nbEdges(); i++) {
		const int tmp = en[i][0];
		en[i][0] = en[i][1];
		en[i][1] = tmp;
	}
	backward_sp = new FilteredDijkstra(this, dest, en, ou, in, weights);
	backward_sp_tmp = new FilteredDijkstra(this, dest, en, ou, in, weights);
	mandatory_sp = new FilteredDijkstraMandatory(this, dest, source, en, ou, in, weights);
	mandatory_sp->init();
	initial_mandatory_sp = new FilteredDijkstraMandatory(this, dest, source, en, ou, in, weights);
	initial_mandatory_sp->init();

	rootLevelPropagation();
	constructBasicExplanations();
}

BoundedPathPropagator::BoundedPathPropagator(int _s, int _d, vec<BoolView>& _vs, vec<BoolView>& _es,
																						 vec<vec<edge_id> >& _in, vec<vec<edge_id> >& _out,
																						 vec<vec<int> >& _en, vec<vec<int> >& _wst, IntVar* _w)
		: GraphPropagator(_vs, _es, _en),
			forward_sp(nullptr),
			backward_sp(nullptr),
			explain_sp(nullptr),
			dkm(nullptr),
			source(_s),
			dest(_d),
			w(_w),
			explanation_tsize(0),
			explanation_size(0),
			in_nodes_tsize(0),
			in_nodes_size(0) {
	std::cerr << "Do not use BoundedPathPropagator for time-depending paths" << '\n';

	priority = 5;

	constructGraph(_in, _out, _en);
	constructWeights(_wst, _w);

	std::vector<std::vector<int> > en(nbEdges(), std::vector<int>());
	for (int i = 0; i < _en.size(); i++) {
		for (int j = 0; j < _en[i].size(); j++) {
			en[i].push_back(_en[i][j]);
		}
	}

	std::vector<std::vector<int> > weights(nbEdges(), std::vector<int>());
	for (int i = 0; i < nbEdges(); i++) {
		for (int j = 0; j < _wst[i].size(); j++) {
			weights[i].push_back(_wst[i][j]);
		}
	}
	kosaraju = new FilteredKosarajuSCC(this, nbNodes(), ou, in, en);

	forward_sp = new FilteredDijkstra(this, source, en, in, ou, weights);
	explain_sp = new ExplainerDijkstra(this, source, en, in, ou, weights);
	mandatory_explainer_sp = new ExplainerDijkstraMandatory(this, source, dest, en, in, ou, weights);
	mandatory_explainer_sp->init();

	for (int i = 0; i < nbEdges(); i++) {
		const int tmp = en[i][0];
		en[i][0] = en[i][1];
		en[i][1] = tmp;
	}
	backward_sp = new FilteredDijkstra(this, dest, en, ou, in, weights);
	backward_sp_tmp = new FilteredDijkstra(this, dest, en, ou, in, weights);
	mandatory_sp = new FilteredDijkstraMandatory(this, dest, source, en, ou, in, weights);
	mandatory_sp->init();
	initial_mandatory_sp = new FilteredDijkstraMandatory(this, dest, source, en, ou, in, weights);
	initial_mandatory_sp->init();
	rootLevelPropagation();
	constructBasicExplanations();

	std::vector<std::vector<int> > arrivalTime =
			std::vector<std::vector<int> >(wst.size(), std::vector<int>(wst[0].size(), -1));
	for (int i = 0; i < wst.size(); i++) {
		for (int j = 0; j < wst[i].size(); j++) {
			arrivalTime[i][j] = wst[i][j] + j;
		}
	}

	std::vector<std::vector<int> > latest =
			std::vector<std::vector<int> >(wst.size(), std::vector<int>());
	for (unsigned int i = 0; i < latest.size(); i++) {
		latest[i] = std::vector<int>(arrivalTime[i][arrivalTime[i].size() - 1] + 1, -1);
		for (unsigned int x = 0; x < arrivalTime[i].size(); x++) {
			int v = arrivalTime[i][x];
			int v2 = latest[i].size();
			if (x < arrivalTime[i].size() - 1) {
				v2 = arrivalTime[i][x + 1];
			}
			if (v < 0) {
				v = 0;
			}
			if (v2 < 0) {
				v2 = 0;
			}
			for (int k = v; k < v2; k++) {
				latest[i][k] = latest[i][k] > (int)x ? latest[i][k] : (int)x;
			}
		}
	}

	std::cout << "Done " << wst.size() << " " << wst[0].size() << '\n';
}

BoundedPathPropagator::~BoundedPathPropagator() {
	delete last_state_n;
	delete last_state_e;
	delete forward_sp;
	delete backward_sp;
	delete backward_sp_tmp;
	delete mandatory_sp;
	delete explain_sp;
	delete dkm;
}

void BoundedPathPropagator::wakeup(int i, int /*c*/) {
	priority = 5;
	// assert(prop_expl.size() == fail_expl.size() + 1);
	update_explanation();
	update_innodes();
	// assert(prop_expl.size() == fail_expl.size() + 1);
	if (i == -1) {
		// Changes in max distance.
		pushInQueue();
	} else if (i >= 0 && i < nbEdges()) {
		if (getEdgeVar(i).isFalse() && last_state_e[i] != VT_OUT) {
			rem_edge.insert(i);
			if (was_shortest[i] != 0) {
				addToExplanation(i);
				pushInQueue();
			}
		}

	} else {
		const int u = i - nbEdges();
		if (getNodeVar(u).isTrue() && last_state_n[u] != VT_IN) {
			last_state_n[u] = VT_IN;
			in_nodes_tsize++;
			in_nodes_size++;
			in_nodes_list.push_back(u);
		}
	}
}

void BoundedPathPropagator::addToExplanation(int e) {
	if (DEBUG) {
		std::cout << "Adding to explanation " << e << '\n';
	}
	fail_expl.push(getEdgeVar(e).getValLit());
	prop_expl.push(getEdgeVar(e).getValLit());
	explanation_size = fail_expl.size();
	explanation_tsize = explanation_size;
}

void BoundedPathPropagator::update_explanation() {
	if (explanation_tsize < explanation_size) {
		fail_expl.resize(explanation_tsize);
		prop_expl.resize(explanation_tsize + 1);
		explanation_size = explanation_tsize;
	}
}

void BoundedPathPropagator::update_innodes() {
	if (in_nodes_tsize < in_nodes_size) {
		in_nodes_list.resize(in_nodes_tsize);
		in_nodes_size = in_nodes_tsize;
	}
}

void BoundedPathPropagator::computeReason(Clause*& r) {
	if (so.lazy) {
		if (r == nullptr) {
			prop_expl[1] = w->getMaxLit();
			r = ReasonNew(prop_expl);
		}
	} else {
		r = nullptr;
	}
}

bool BoundedPathPropagator::falseOrFail(int e, Clause*& r) {
	const int hd = getHead(e);
	const int tl = getTail(e);
#ifdef BASIC_EXPL
	//* OLD EXPLANATIONS:
	if (!getEdgeVar(e).isFixed()) {
		computeReason(r);
		getEdgeVar(e).setVal(false, r);
	} else if (getEdgeVar(e).isTrue()) {
		if (so.lazy) {
			fail_expl[0] = w->getMaxLit();
			int old_s = fail_expl.size();
			fail_expl.push(getEdgeVar(e).getValLit());
			GiveFailureExplanation(fail_expl);
			fail_expl.resize(old_s);
		}
		return false;
	}
	return true;
#endif
	//*/
	// cout<<"False or fail on edge "<<e<<" ("<<getTail(e)<<","<<getHead(e)<<")"<<endl;
	if (!getEdgeVar(e).isFixed()) {
		if (so.lazy) {
			std::vector<Lit> lits;
			lits.emplace_back();
			backward_sp_tmp->set_source(tl);
			backward_sp_tmp->run();
			explain_sp->reset(w->getMax() - backward_sp->distTo(hd) - ws[e], backward_sp_tmp, lits);
			explain_sp->set_explaining(tl);
			explain_sp->run();
			// assert(check_expl(explain_sp->getExpl(),w->getMax() - backward_sp->distTo(hd) - ws[e],tl));
			const int relaxed_dist = w->getMax() - explain_sp->distTo(tl) - ws[e];
			explain_sp->set_source(hd);
			explain_sp->reset(relaxed_dist, backward_sp);
			explain_sp->set_explaining(dest);
			explain_sp->run();
			explain_sp->set_source(source);
			// assert(check_expl(explain_sp->getExpl(),relaxed_dist,hd,true));
			lits = explain_sp->getLits();
			lits.push_back(w->getMaxLit());
			r = ReasonNew(lits);
		}
		getEdgeVar(e).setVal(false, r);
		rem_edge.insert(e);
		last_state_e[e] = VT_OUT;
	} else if (getEdgeVar(e).isTrue()) {
		if (so.lazy) {
			std::vector<Lit> lits;
			backward_sp_tmp->set_source(tl);
			backward_sp_tmp->run();
			explain_sp->reset(w->getMax() - backward_sp->distTo(hd) - ws[e], backward_sp_tmp, lits);
			explain_sp->set_explaining(tl);
			explain_sp->run();
			explain_sp->set_source(hd);
			explain_sp->reset(w->getMax() - explain_sp->distTo(tl) - ws[e], backward_sp);
			explain_sp->set_explaining(dest);
			explain_sp->run();
			explain_sp->set_source(source);
			lits = explain_sp->getLits();
			lits.push_back(w->getMaxLit());
			lits.push_back(getEdgeVar(e).getValLit());
			GiveFailureExplanation(lits);
		}
		return false;
	}
	return true;
}

bool BoundedPathPropagator::propagate_scc_order() {
	kosaraju->run();
	kosaraju->set_levels(source, dest);

	for (int e = 0; e < nbEdges(); e++) {
		if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
			continue;
		}
		const int hd = getHead(e);
		const int tl = getTail(e);
		if (kosaraju->scc_of(hd) == kosaraju->scc_of(tl)) {
			continue;
		}
		const int lhd = kosaraju->level_of_scc(kosaraju->scc_of(hd));
		const int ltl = kosaraju->level_of_scc(kosaraju->scc_of(tl));
		if (lhd > ltl + 1 || (lhd == ltl + 1 && !kosaraju->scc_mand(kosaraju->scc_of(tl)))) {
			Clause* r = nullptr;
			// Forbid edge
			if (so.lazy) {
				vec<Lit> ps;
				if (!getEdgeVar(e).isFixed()) {
					ps.push();
				}
				/*int scc = kosaraju->mand_scc_level(ltl);
				int other = kosaraju->node_from_mandscc(scc);
				scc = kosaraju->mand_scc_level(lhd);
				int mhd = kosaraju->node_from_mandscc(scc);
				ps.push(getNodeVar(other).getValLit());
				ps.push(getNodeVar(mhd).getValLit());
				stack<int> s;
				s.push(mhd);
				vector<bool> blue(nbNodes(), false);
				vector<bool> pink(nbNodes(), false);
				while (!s.empty()) {
						int top = s.top();
						s.pop();
						blue[top] = true;
						for(unsigned int i = 0; i < ou[top].size(); ++i) {
								int ep = ou[top][i];
								int v = getHead(e);
								if ((getEdgeVar(ep).isFixed() && getEdgeVar(ep).isFalse()) ||
										(getNodeVar(v).isFixed() && getNodeVar(v).isFalse())) {
										continue;
								}
								blue[v] = true;
								if (!blue[v])
										s.push(v);
						}
				}
				s.push(other);
				while (!s.empty()) {
						int top = s.top();
						s.pop();
						pink[top] = true;
						for(unsigned int i = 0; i < ou[top].size(); ++i) {
								int ep = ou[top][i];
								int v = getHead(e);
								if (getEdgeVar(ep).isFixed() && getEdgeVar(ep).isFalse()
										&& blue[v]) {
										ps.push(getEdgeVar(e).getValLit());
										continue;
								}
								pink[v] = true;
								if (!pink[v])
										s.push(v);
						}
				}
				*/

				for (int i = 0; i < nbEdges(); i++) {
					if (getEdgeVar(i).isFixed()) {
						ps.push(getEdgeVar(i).getValLit());
					}
				}

				for (int i = 0; i < nbNodes(); i++) {
					if (getNodeVar(i).isFixed()) {
						ps.push(getNodeVar(i).getValLit());
					}
				}

				if (!getEdgeVar(e).isFixed()) {
					r = ReasonNew(ps);
				} else {
					GiveFailureExplanation(ps);
				}
			}
			if (!getEdgeVar(e).isFixed()) {
				getEdgeVar(e).setVal(false, r);
			} else {
				return false;
			}
		}
	}
	return true;
}

// This assumes that all the nodes are reachable!!!
bool BoundedPathPropagator::propagate() {
	update_explanation();
	update_innodes();

	const bool ok = propagate_dijkstra();
	if (!ok) {
		return false;
	}

	// if (!propagate_scc_order())
	//     return false;

	if (!DPLB) {
		return true;
	}

	static double delta = 500;

	if (in_nodes_list.size() >= 3) {
		const bool set_target = false;

		if (delta < 0.5) {
			dkm->set_nb_clusters(dkm->nb_clusters() + 1);
		}
		if (delta > 8.0) {
			dkm->set_nb_clusters(dkm->nb_clusters() - 1);
		}
		if (dkm->nb_clusters() <= 0) {
			dkm->set_nb_clusters(NB_CLUSTERS);
		}
		if (dkm->nb_clusters() >= CLUSTER_LIMIT) {
			dkm->set_nb_clusters(CLUSTER_LIMIT);
		}

		bool ok;
		const double st = wallClockTime();

		if (DEBUG) {
			std::cout << "Running DPLB" << '\n';
		}

		const int lb = mandatory_sp->run(&ok, set_target);
		delta = wallClockTime() - st;

		if (DEBUG) {
			std::cout << "Achieved lb: " << lb << " " << w->getMax() << " " << delta << '\n';
		}

		/*if(!ok) {//No benefit at all...
				fail_expl[0] = getNodeVar(dest).getValLit();
				int old_s = fail_expl.size();
				for (unsigned int i = 0; i < in_nodes_list.size(); i++)
						fail_expl.push(getNodeVar(in_nodes_list[i]).getValLit());
				Clause *expl = Clause_new(fail_expl);
				fail_expl.resize(old_s);
				expl->temp_expl = 1;
				sat.rtrail.last().push(expl);
				sat.confl = expl;
				fail_expl[0] = w->getMaxLit();
				return false;
				}*/

		if (lb > w->getMax()) {
			if (so.lazy) {
#ifdef BASIC_EXPL
				//* OLD EXPLANATIONS
				fail_expl[0] = w->getMaxLit();
				int old_s = fail_expl.size();
				for (unsigned int i = 0; i < in_nodes_list.size(); i++)
					fail_expl.push(getNodeVar(in_nodes_list[i]).getValLit());
				GiveFailureExplanation(fail_expl);
				fail_expl.resize(old_s);
#else
				// NEW EXPLANATIONS
				mandatory_explainer_sp->reset(w->getMax(), mandatory_sp);  //,delta*200000.0);
				bool ok2;
				mandatory_explainer_sp->set_target(mandatory_sp->get_target());
#ifdef DIJKSTRAMANDATORY_ALLOW_CYCLE
				mandatory_explainer_sp->run(&ok2, true, mandatory_sp->get_start_point());
#else
				mandatory_explainer_sp->run(&ok2, true);
#endif
				std::vector<Lit> lits = mandatory_explainer_sp->getLits();
				for (const int i : in_nodes_list) {
					lits.push_back(getNodeVar(i).getValLit());
				}

				lits.push_back(w->getMaxLit());
				GiveFailureExplanation(lits);
#endif
			}
			return false;
		}
		if (false && lb > w->getMin()) {
			// This, for some reason I dont know yet, always makes the code run
			// slower. Correct, but slower... -> Because it makes me run
			// the explanation, which is slow, every time!
			Clause* min_r = nullptr;
			if (so.lazy) {
				mandatory_explainer_sp->reset(lb, mandatory_sp);
				bool ok2;
				mandatory_explainer_sp->run(&ok2);
				const std::vector<int> edges = mandatory_explainer_sp->getExpl();
				// assert(_check_expl_mand(edges,w->getMax()));
				vec<Lit> lits;
				lits.push();
				for (const int edge : edges) {
					lits.push(getEdgeVar(edge).getValLit());
				}
				for (const int i : in_nodes_list) {
					lits.push(getNodeVar(i).getValLit());
				}
				lits.push(w->getMaxLit());
				min_r = ReasonNew(lits);
			}
			w->setMin(lb, min_r);
		}
	}

	return true;
}

bool BoundedPathPropagator::propagate_dijkstra() {
	Clause* r = nullptr;

	backward_sp->run();

	if (backward_sp->distTo(source) > w->getMax()) {
		if (so.lazy) {
#ifdef BASIC_EXPL
			fail_expl[0] = w->getMaxLit();
			GiveFailureExplanation(fail_expl);
#else
			std::vector<Lit> lits;
			explain_sp->reset(w->getMax(), backward_sp, lits);
			explain_sp->run();
			lits = explain_sp->getLits();
			lits.push_back(w->getMaxLit());
			GiveFailureExplanation(lits);
#endif
		}
		return false;
	}
	if (backward_sp->distTo(dest) == -1) {
		return true;
		assert(false);
		// The path propagator must run before!
	}
	// return true;
	forward_sp->run();

	int max_d = 0;     // Distance to furthest in-node
	int arg_max = -1;  // Furthest in-node

	std::vector<node_id> removed_nodes;

	bool recompute = false;
	int prev_node = -1;
	for (int u = 0; u < nbNodes(); u++) {
#ifndef BASIC_EXPL
		assert(!(getNodeVar(u).isFixed() && getNodeVar(u).isTrue()) || forward_sp->distTo(u) != -1);
		assert(!(getNodeVar(u).isFixed() && getNodeVar(u).isTrue()) || backward_sp->distTo(u) != -1);
#endif
		if (recompute) {
			if (prev_node != -1 && !forward_sp->is_leaf(prev_node)) {
				forward_sp->run();
			}
			if (prev_node != -1 && !backward_sp->is_leaf(prev_node)) {
				backward_sp->run();
			}
			recompute = false;
		}
		prev_node = u;

#ifndef BASIC_EXPL
		//* NEW EXPLANATIONS
		if (forward_sp->distTo(u) > w->getMax()) {
			if (!getNodeVar(u).isFixed()) {
				if (so.lazy) {
					std::vector<Lit> lits;
					lits.emplace_back();
					backward_sp_tmp->set_source(u);
					backward_sp_tmp->run();
					explain_sp->reset(w->getMax(), backward_sp_tmp, lits);
					explain_sp->set_explaining(u);
					explain_sp->run();
					lits = explain_sp->getLits();
					lits.push_back(w->getMaxLit());
					r = ReasonNew(lits);
				}
				getNodeVar(u).setVal(false, r);
				last_state_n[u] = VT_OUT;
				if (!GraphPropagator::coherence_outedges(u)) {
					return false;
				}
				removed_nodes.push_back(u);
				recompute = true;
			} else if (getNodeVar(u).isTrue()) {
				if (so.lazy) {
					std::vector<Lit> lits;
					backward_sp_tmp->set_source(u);
					backward_sp_tmp->run();
					explain_sp->reset(w->getMax(), backward_sp_tmp, lits);
					explain_sp->set_explaining(u);
					explain_sp->run();
					lits = explain_sp->getLits();
					lits.push_back(w->getMaxLit());
					lits.push_back(getNodeVar(u).getValLit());
					GiveFailureExplanation(lits);
				}
				return false;
			}
		} else if (backward_sp->distTo(u) > w->getMax()) {
			if (!getNodeVar(u).isFixed()) {
				if (so.lazy) {
					std::vector<Lit> lits;
					lits.emplace_back();
					explain_sp->set_source(u);
					explain_sp->reset(w->getMax(), backward_sp, lits);
					explain_sp->set_explaining(dest);
					explain_sp->run();
					explain_sp->set_source(source);
					lits = explain_sp->getLits();
					lits.push_back(w->getMaxLit());
					r = ReasonNew(lits);
				}
				getNodeVar(u).setVal(false, r);
				last_state_n[u] = VT_OUT;
				if (!GraphPropagator::coherence_outedges(u)) {
					return false;
				}
				removed_nodes.push_back(u);
				recompute = true;
			} else if (getNodeVar(u).isTrue()) {
				if (so.lazy) {
					std::vector<Lit> lits;
					explain_sp->set_source(u);
					explain_sp->reset(w->getMax(), backward_sp, lits);
					explain_sp->set_explaining(dest);
					explain_sp->run();
					explain_sp->set_source(source);
					lits = explain_sp->getLits();
					lits.push_back(w->getMaxLit());
					lits.push_back(getNodeVar(u).getValLit());
					GiveFailureExplanation(lits);
				}
				return false;
			}
		} else
#endif
				if (forward_sp->distTo(u) + backward_sp->distTo(u) > w->getMax()) {

			if (!getNodeVar(u).isFixed()) {
				if (so.lazy) {
#ifdef BASIC_EXPL
					computeReason(r);
					prop_expl[0] = w->getMaxLit();
					r = ReasonNew(prop_expl);
#else
					std::vector<Lit> lits;
					lits.emplace_back();
					backward_sp_tmp->set_source(u);
					backward_sp_tmp->run();
					explain_sp->reset(w->getMax() - backward_sp->distTo(u), backward_sp_tmp, lits);
					explain_sp->set_explaining(u);
					explain_sp->run();
					// assert(check_expl(explain_sp->getExpl(),w->getMax() - backward_sp->distTo(u),u));
					explain_sp->set_source(u);
					const int relaxed_dist = w->getMax() - explain_sp->distTo(u);
					explain_sp->reset(relaxed_dist, backward_sp);
					explain_sp->set_explaining(dest);
					explain_sp->run();
					explain_sp->set_source(source);
					// assert(check_expl(explain_sp->getExpl(),relaxed_dist,u,true));
					lits = explain_sp->getLits();
					lits.push_back(w->getMaxLit());
					r = ReasonNew(lits);
#endif
				}
				getNodeVar(u).setVal(false, r);
				last_state_n[u] = VT_OUT;
				if (!GraphPropagator::coherence_outedges(u)) {
					return false;
				}
				removed_nodes.push_back(u);
				recompute = true;

			} else if (getNodeVar(u).isTrue()) {
				if (so.lazy) {
#ifdef BASIC_EXPL
					fail_expl[0] = w->getMaxLit();
					int old_s = fail_expl.size();
					fail_expl.push(getNodeVar(u).getValLit());
					GiveFailureExplanation(fail_expl);
					fail_expl.resize(old_s);
#else
					std::vector<Lit> lits;
					backward_sp_tmp->set_source(u);
					backward_sp_tmp->run();
					explain_sp->reset(w->getMax() - backward_sp->distTo(u), backward_sp_tmp, lits);
					explain_sp->set_explaining(u);
					explain_sp->run();
					// assert(check_expl(explain_sp->getExpl(),w->getMax() - backward_sp->distTo(u),u));
					explain_sp->set_source(u);
					const int relaxed_dist = w->getMax() - explain_sp->distTo(u);
					explain_sp->reset(relaxed_dist, backward_sp);
					explain_sp->set_explaining(dest);
					explain_sp->run();
					explain_sp->set_source(source);
					// assert(check_expl(explain_sp->getExpl(),relaxed_dist,u,true));
					lits = explain_sp->getLits();
					lits.push_back(w->getMaxLit());
					lits.push_back(getNodeVar(u).getValLit());
					GiveFailureExplanation(lits);
#endif
				}
				return false;
			}
		} else {
			if (getNodeVar(u).isFixed() && getNodeVar(u).isTrue()) {
				if (max_d < forward_sp->distTo(u) + backward_sp->distTo(u)) {
					max_d = forward_sp->distTo(u) + backward_sp->distTo(u);
					arg_max = u;
				}
			}
		}  //*/
	}

	//*
	for (const int u : removed_nodes) {
		std::vector<int> removed_e;
		coherence_outedges(u, removed_e);
		for (const int i : removed_e) {
			last_state_e[i] = VT_OUT;
		}
	}  //*/
	// return true;

	assert(arg_max >= 0);
	// cout <<"LB: "<<max_d<<" "<<in_nodes_list.size()<<endl;
	//  Raise the minimum to the distance to the furthest node
	//  And use that node as part of the explanation
	if (max_d > w->getMin()) {
		Clause* min_r = nullptr;
		if (so.lazy) {
#ifdef BASIC_EXPL
			prop_expl[1] = getNodeVar(arg_max).getValLit();
			min_r = ReasonNew(prop_expl);
			prop_expl[1] = w->getMaxLit();
#else
			std::vector<Lit> lits;
			lits.push_back(w->getMaxLit());
			backward_sp_tmp->set_source(arg_max);
			backward_sp_tmp->run();
			explain_sp->reset(max_d - backward_sp->distTo(arg_max), backward_sp_tmp, lits);
			explain_sp->set_explaining(arg_max);
			explain_sp->run();
			const int relaxed_dist = max_d - explain_sp->distTo(arg_max);
			explain_sp->set_source(arg_max);
			explain_sp->reset(relaxed_dist, backward_sp);
			explain_sp->set_explaining(dest);
			explain_sp->run();
			explain_sp->set_source(source);
			lits = explain_sp->getLits();
			lits.push_back(w->getMaxLit());
			lits.push_back(getNodeVar(arg_max).getValLit());
			min_r = ReasonNew(lits);
#endif
		}
		w->setMin(max_d, min_r);
	}

	// return true;
	for (int e = 0; e < nbEdges(); e++) {
		if (getTail(e) == getHead(e)) {
			continue;
		}

		if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) {
			continue;
		}

		const int hd = getHead(e);
		const int tl = getTail(e);

		// We know how long it takes to get from the head of this edge
		// to de destination: hd_to_d = backward_sp->distTo(hd).
		// We know how long it takes to get from the source to the tail
		// of this edge: s_to_tl = forward_sp->distTo(tl).
		// How long would it take to get fromt he source to the destination
		// if we used this edge:
		// s_to_d_through_e = s_to_tl + ws[e] + hd_to_d

		const int hd_to_d = backward_sp->distTo(hd);
		if (hd_to_d == -1) {  // Destination can't reach this node
			if (!falseOrFail(e, r)) {
				std::cerr << "Error " << __FILE__ << " " << __LINE__ << '\n';
				return false;
			}
			continue;
		}
		const int s_to_tl = forward_sp->distTo(tl);
		if (s_to_tl == -1) {  // Source can't reach this node
			if (!falseOrFail(e, r)) {
				std::cerr << "Error " << __FILE__ << " " << __LINE__ << '\n';
				return false;
			}
			continue;
		}
		const int s_to_d_through_e = s_to_tl + ws[e] + hd_to_d;

		// if (backward_sp->isInShortestPath(tl,hd) ||
		//     forward_sp->isInShortestPath(tl,hd))
		//     was_shortest[e] |= 1;
		if (s_to_d_through_e > w->getMax()) {
			// Cannot get from s to d in time through e.
			if (!falseOrFail(e, r)) {
				return false;
			}
			last_state_e[e] = VT_OUT;
		} else {
			// Can use e to go form s to d and still get to d in time.
			was_shortest[e] |= 1;
		}
	}
	return true;
}

struct kkl_sorter {
	bool operator()(std::pair<std::pair<int, int>, int> i, std::pair<std::pair<int, int>, int> j) {
		return (i.second < j.second);
	}
} kkl_sorter;

void BoundedPathPropagator::clearPropState() {
	GraphPropagator::clearPropState();
	rem_edge.clear();
	new_edges.clear();
}

bool BoundedPathPropagator::checkFinalSatisfied() {
	int sum = 0;
	for (int i = 0; i < nbEdges(); i++) {
		if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) {
			sum += ws[i];
		}
	}
	assert(sum == w->getVal());
	return sum == w->getVal();
}

BoundedPathPropagator* bounded_path_p = nullptr;

void bp_path_helper(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es,
										vec<vec<edge_id> >& _in, vec<vec<edge_id> >& _out, vec<vec<int> >& _en) {
	if (_vs[from].setValNotR(true)) {
		_vs[from].setVal(true, nullptr);
	}
	if (_vs[to].setValNotR(true)) {
		_vs[to].setVal(true, nullptr);
	}

#ifndef KF
	path(from, to, _vs, _es, _in, _out, _en);
#endif
#ifdef KF
	std::map<node_id, vec<edge_id> > adj;
	for (int i = 0; i < _in.size(); i++) {
		for (int j = 0; j < _in[i].size(); j++) {
			adj[i].push(_in[i][j]);
		}
		for (int j = 0; j < _out[i].size(); j++) {
			adj[i].push(_out[i][j]);
		}
	}
	GraphPropagator* gp = new GraphPropagator(_vs, _es, _en);
	gp->attachToAll();
#endif
}
void bounded_path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _in,
									vec<vec<edge_id> >& _out, vec<vec<int> >& _en, vec<int>& _ws, IntVar* w) {
	bp_path_helper(from, to, _vs, _es, _in, _out, _en);
	bounded_path_p = new BoundedPathPropagator(from, to, _vs, _es, _in, _out, _en, _ws, w);
	// if (so.check_prop)
	//     engine.propagators.push(bounded_path_p);
}

// //Experimental, needs testing!!!
// void bounded_path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es,
//                   vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
//         vec< vec<int> >& _en, vec<vec< int> >& _ws, IntVar* w) {

//     bp_path_helper(from,to,_vs,_es,_in,_out,_en);

//     bounded_path_p = new BoundedPathPropagator(from, to ,_vs,_es,_in,_out,_en,_ws,w);
//     if (so.check_prop)
//         engine.propagators.push(bounded_path_p);
// }

class ShortestPathSearch : public BranchGroup {
	std::vector<int> decisions;
	int last_dec_level;

	ShortestPathSearch(vec<Branching*>& _x, VarBranch vb, bool t) : BranchGroup(_x, vb, t) {
		last_dec_level = engine.decisionLevel();
		decisions.push_back(bounded_path_p->source);
	}

public:
	static ShortestPathSearch* search;
	static ShortestPathSearch* getShortestPathSearch(vec<Branching*>& _x, VarBranch vb, bool t) {
		if (search == nullptr) {
			search = new ShortestPathSearch(_x, vb, t);
		}
		return search;
	}

	bool backtrack() {
		if (last_dec_level >= engine.decisionLevel()) {
			const int remove = -(engine.decisionLevel() - last_dec_level);
			// cout <<"Backtracked "<<remove<<endl;
			for (int i = 0; i < remove; i++) {
				decisions.pop_back();
			}
			last_dec_level = engine.decisionLevel();
			return true;
		}
		last_dec_level = engine.decisionLevel();
		return false;
	}

	DecInfo* branch() override {
		if (finished()) {
			return nullptr;
		}
		backtrack();
		DecInfo* di = nullptr;
		int curr = decisions[decisions.size() - 1];
		// In backward_sp the parenthood relation is inverted.
		// If we want to fix edge from curr to the shortest place next to curr
		// we are looking for edge e' in backward_sp a <---e'--- b
		// The actual edge is the other way around: tail ---e---> head
		// where a is curr and b is the other end of e (which is the parent of
		// a through e')
		// cout <<"Curr"<<curr<<endl;
		int head = bounded_path_p->backward_sp->parentOf(curr);
		if (head != -1) {
			int tail = curr;
			int edge = bounded_path_p->nodes2edge[tail][head];
			while (edge >= 0 && x[edge]->finished() && curr != head) {
				curr = head;
				head = bounded_path_p->backward_sp->parentOf(curr);
				tail = curr;
				edge = bounded_path_p->nodes2edge[tail][head];
			}
			if (edge >= 0 && !x[edge]->finished()) {
				di = new DecInfo(nullptr, toInt(bounded_path_p->getEdgeVar(edge).getLit(true)));
				decisions.push_back(curr);
			}
		}

		if (di == nullptr) {
			for (int i = 0; i < x.size(); i++) {
				if (!x[i]->finished()) {
					// di = new DecInfo(x[i],0,1);
					di = new DecInfo(nullptr, toInt(bounded_path_p->getEdgeVar(i).getLit(false)));
					decisions.push_back(curr);  // bounded_path_p->getTail(i));
					return di;
				}
			}
		}
		// assert(di != NULL);
		//((BoolView*)x[edge])->setVal(true,NULL);//set(1,1);
		return di;
	}
};
ShortestPathSearch* ShortestPathSearch::search = nullptr;

/*
void branch(vec<Branching*> x, VarBranch var_branch, ValBranch val_branch) {
		if (var_branch == SHORTEST_PATH_ORDER) {
				engine.branching->add(ShortestPathSearch::getShortestPathSearch(x, var_branch, true));
				return;
		}

		engine.branching->add(new BranchGroup(x, var_branch, true));
		if (val_branch == VAL_DEFAULT) return;
		PreferredVal p;
		switch (val_branch) {
		case VAL_MIN: p = PV_MIN; break;
		case VAL_MAX: p = PV_MAX; break;
		case VAL_SPLIT_MIN: p = PV_SPLIT_MIN; break;
		case VAL_SPLIT_MAX: p = PV_SPLIT_MAX; break;
		default: NEVER;
		}
		for (int i = 0; i < x.size(); i++) ((Var*) x[i])->setPreferredVal(p);
}
//*/
