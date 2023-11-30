#ifndef DIRECTED_REACHABILITY_H
#define DIRECTED_REACHABILITY_H

#include "chuffed/globals/graph.h"
#include "chuffed/support/lengauer_tarjan.h"
#include "chuffed/support/union_find.h"

#include <map>
#include <queue>
#include <set>
#include <stack>
#include <utility>
#include <vector>

class FilteredLT : public LengauerTarjan {
	GraphPropagator* p;
	int visited_innodes{0};

protected:
	void DFS(int r) override;

public:
	FilteredLT(GraphPropagator* _p, int _r, std::vector<std::vector<int> > _en,
						 std::vector<std::vector<int> > _in, std::vector<std::vector<int> > _ou);
	int get_visited_innodes() const;
	void init() override;
	bool ignore_node(int u) override;
	bool ignore_edge(int e) override;
};

class DReachabilityPropagator : public GraphPropagator {
private:
	FilteredLT* lt{nullptr};

	int root;
	std::vector<std::vector<int> > nodes2edge;

	Tint in_nodes_tsize;
	int in_nodes_size{0};

	virtual bool remove_deg1(int u);

protected:
	virtual bool correctDominator(int r, std::vector<bool>& v, int avoid);  // DEBUG
	std::vector<int> in_nodes_list;

	enum VType { VT_IN, VT_OUT, UNK };
	Tint* last_state_n;
	Tint* last_state_e;

	std::set<int> new_node;
	std::set<int> rem_node;
	std::set<int> new_edge;
	std::set<int> rem_edge;

	std::vector<std::vector<edge_id> > in;
	std::vector<std::vector<edge_id> > ou;

	int get_some_innode_not(int other_than);
	int get_root_idx() const;
	void add_innode(int i);
	void update_innodes();

	void verificationDFS(int r, std::vector<bool>& v);

	virtual bool _propagateReachability(bool local = true);  // Make sure its a local call
public:
	DReachabilityPropagator(int _r, vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _in,
													vec<vec<edge_id> >& _out, vec<vec<int> >& _en);
	~DReachabilityPropagator() override;
	void wakeup(int i, int c) override;
	bool propagate() override;
	void clearPropState() override;

	virtual bool propagateNewEdge(int edge);
	virtual bool propagateRemEdge(int edge);
	virtual bool propagateRemNode(int node);
	virtual bool propagateNewNode(int node);

	virtual bool propagateReachability();

	virtual bool checkFinalSatisfied();

	FilteredLT* getDominatorsAlgorithm() { return lt; }
	void explain_dominator(int u, int dom, Clause** r);
	void explain_dominator(int u, int dom, vec<Lit>& ps);
	void reverseDFS(int u, std::vector<bool>& v, int skip_n = -1);
	void reverseDFStoBorder(int u, std::vector<bool>& v, std::vector<bool>& my_side, vec<Lit>& expl,
													int skip_n = -1);

	virtual inline int findEdge(int u, int v) {
		assert(u >= 0 && u < nbNodes());
		assert(v >= 0 && v < nbNodes());
		return nodes2edge[u][v];
	}
};

class DReachabilityPropagatorReif : public DReachabilityPropagator {
	BoolView b;

public:
	DReachabilityPropagatorReif(int _r, vec<BoolView>& _vs, vec<BoolView>& _es,
															vec<vec<edge_id> >& _in, vec<vec<edge_id> >& _out,
															vec<vec<int> >& _en, BoolView _b)
			: DReachabilityPropagator(_r, _vs, _es, _in, _out, _en), b(std::move(_b)) {
		b.attach(this, -1, EVENT_LU);
	}

	void wakeup(int i, int c) override {
		if (i == -1) {
			pushInQueue();
		} else {
			this->DReachabilityPropagator::wakeup(i, c);
		}
	}

	bool propagate() override {
		if (b.isFixed() && b.isTrue()) {
			return this->DReachabilityPropagator::propagate();
		}
		return true;
	}
};

#endif
