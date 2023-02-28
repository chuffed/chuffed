#ifndef DTREE_H
#define DTREE_H

#include <chuffed/globals/dconnected.h>
#include <chuffed/support/union_find.h>

#include <map>

class DTreePropagator : public DReachabilityPropagator {
	UF<Tint> uf;
	RerootedUnionFind<Tint> ruf;

	std::vector<bool> processed_e;
	std::vector<bool> processed_n;

	void explain_cycle(int u, int v, vec<Lit>& path);

protected:
	// FOR DEBUG ONLY
	bool test_ruf() {
		for (int i = 0; i < nbEdges(); i++) {
			if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) {
				if (!ruf.connected(getHead(i), getTail(i))) return false;
			}
		}
		return true;
	};

public:
	DTreePropagator(int _r, vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _in,
									vec<vec<edge_id> >& _out, vec<vec<int> >& _en);

	virtual ~DTreePropagator();

	virtual bool propagateNewEdge(int edge);
	virtual bool propagateNewNode(int node);

	virtual bool check_cycle(int e);
	virtual void prevent_cycle(int e);

	virtual bool propagate();

	virtual bool checkFinalSatisfied();
};

class DTreeParenthoodPropagator : public DTreePropagator {
	vec<IntVar*> parents;
	vec<BoolView> equalities;
	Tint* dom_size;
	std::map<int, std::pair<int, int> > event2parrel;  // parenthood relation
	int first_event;
	int last_event;
	std::set<int> parenthood_fixed;
	std::set<int> parenthood_abandon;

public:
	DTreeParenthoodPropagator(int _r, vec<BoolView>& _vs, vec<BoolView>& _es, vec<IntVar*>& parents,
														vec<vec<edge_id> >& _in, vec<vec<edge_id> >& _out, vec<vec<int> >& _en);

	virtual ~DTreeParenthoodPropagator();

	virtual bool propagateRemEdge(int edge);
	virtual bool propagateNewEdge(int edge);
	virtual bool propagateRemParent(int edge);
	virtual bool propagateNewParent(int edge);

	virtual bool propagate();
	virtual void wakeup(int i, int c);

	virtual void clearPropState();

	virtual bool checkFinalSatisfied();
};

class PathDeg1 : public GraphPropagator {
	std::vector<std::vector<int> > in;
	std::vector<std::vector<int> > ou;

	std::vector<int> new_edges;

public:
	PathDeg1(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _in,
					 vec<vec<edge_id> >& _out, vec<vec<int> >& _en);

	virtual void wakeup(int i, int c);
	virtual void clearPropState();

	virtual bool propagate();
};

#endif
