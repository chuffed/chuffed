#ifndef TREE_PROPAGATOR_H
#define TREE_PROPAGATOR_H

#include <chuffed/globals/graph.h>
#include <chuffed/support/union_find.h>

#include <map>
#include <queue>
#include <set>
#include <stack>
#include <unordered_set>
#include <vector>

#define OTHER(o1, o2, a) ((a == o1) ? o2 : o1)

// #define INFINITY 10000

typedef int edge_id;
typedef int node_id;

struct partialExpl {
	edge_id bridge;
	node_id cause1;
	node_id cause2;
	partialExpl() : cause2(-1) {}
};

class TreePropagator : public GraphPropagator {
public:
	struct CC {
		int count;
		std::vector<int> nodesIds;
		CC() : count(0) {}
	};

	static std::vector<TreePropagator*> tree_propagators;

protected:
	std::vector<std::vector<std::vector<int> > > nodes2edge;

	// fancy unionfind
	UF<Tint> uf;
	RerootedUnionFind<Tint> ruf;
	Tint nb_innodes;
	Tint nb_avn;
	std::unordered_set<int> newFixedN;
	std::unordered_set<int> newFixedE;
	bool* isTerminal;

	std::vector<int> in_edges;
	Tint in_edges_tsize;
	int in_edges_size;

	enum VType { VT_IN, VT_OUT, UNK };
	std::vector<Tint> last_state_n;
	std::vector<Tint> last_state_e;

	edge_id findEdge(int u, int v, int idx = 0);
	void moveInEdgeToFront(int e);
	void _findAndBuildBridges(int u, int& count, std::stack<edge_id>& s, int depth[], int low[],
														std::vector<bool>& visited, int parent[], std::stack<node_id>& hits,
														std::vector<std::pair<edge_id, node_id> >& semiExpl,
														std::vector<partialExpl>& bridgeExpl,
														std::vector<partialExpl>& articuExpl);

	int articulations(int n, std::vector<bool>& visited, int& count);
	bool reachable(int n, std::vector<bool>& blue, bool doDFS = false);
	void unite(int u, int v);
	bool cycle_detect(int edge);
	void precycle_detect(int unk_edge);
	int newNodeCompleteCheckup_Count;
	bool newNodeCompleteCheckup;

	// std::vector<CC> keys;

public:
	TreePropagator(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _adj,
								 vec<vec<int> >& _en);
	virtual ~TreePropagator();
	virtual void wakeup(int i, int c);
	virtual bool propagate();
	virtual void clearPropState();

	// Walks only on fixed edges == 1
	void getCC(int node, std::vector<bool>& visited, CC* cc);
	void getAvailableCC(int node, std::vector<bool>& visited, CC* cc);
	virtual bool propagateNewNode(int node);
	virtual bool propagateRemNode(int node);
	virtual bool propagateNewEdge(int edge);
	virtual bool propagateRemEdge(int edge);
	void getUnkEdgesInCC(int r, std::vector<bool>& visited, std::unordered_set<edge_id>& unk);
	void DFSBlue(int r, std::vector<bool>& visited, int& count);
	void DFSPink(int r, std::vector<bool>& visited, std::vector<bool>& blue,
							 std::unordered_set<int>& badEdges);
	void walkIsland(int r, std::vector<bool>& visited, int avoidBridge, bool isArt = false,
									int parent = -1);
	void walkBrokenBridges(int r, std::vector<bool>& reachable, std::vector<bool>& walked,
												 std::vector<bool>& visited, int avoidBridge, std::vector<edge_id>& bridges,
												 bool isArt = false, int parent = -1);

	virtual bool checkFinalSatisfied();

	// virtual void getKeys(KSP* starting, vec<KSP*>& probs);
	// virtual void updateUF(KSP& ksp);
	// void _updateUF(KSP& ksp, int n, int& d,
	//                std::vector<bool>& visited,
	//                std::vector<int>& parent,
	//                std::vector<int>& depth,
	//                std::vector<int>& low,
	//                std::stack<int>& seen
	//                );
};

class ConnectedPropagator : public TreePropagator {
protected:
	bool cycle_detect(int edge) { return true; }
	void precycle_detect(int unk_edge) {}

public:
	ConnectedPropagator(vec<BoolView>& _vs, vec<BoolView>& _es, vec<vec<edge_id> >& _adj,
											vec<vec<int> >& _en)
			: TreePropagator(_vs, _es, _adj, _en) {}
	virtual bool checkFinalSatisfied() { return true; /*TODO*/ }
};

#endif
