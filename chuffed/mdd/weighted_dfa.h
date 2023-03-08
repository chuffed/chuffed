#ifndef WEIGHTED_DFA_H_
#define WEIGHTED_DFA_H_

#include <chuffed/mdd/opcache.h>
#include <chuffed/support/vec.h>

#include <memory>
#include <unordered_map>
#include <vector>

// Code for manipulating a weighted DFA.
// Converts a weighted DFA to a structurally hashed
// layered graph.

// Caveats:
// Does nothing to ensure that there are no long edges.
// Similarly, it does not ensure that the levels are
// increasing.

// TODO: Add a normalization step, so that:
// x1: [0, 3 -> y]
// x2: [0, 2 -> y]
// are mapped to the same node.
class EVLayerGraph;

class EVEdge;

class EVNode {
public:
	EVNode(EVLayerGraph* _g, int _idx) : g(_g), idx(_idx) {}
	EVEdge operator[](int idx) const;

	int var() const;
	int id() const;
	int size() const;

	EVLayerGraph* g;
	int idx;
};

inline bool operator==(const EVNode& x, const EVNode& y) { return x.g == y.g && x.idx == y.idx; }
inline bool operator!=(const EVNode& x, const EVNode& y) { return !(x == y); }

EVNode& operator++(EVNode& x);

class EVEdge {
public:
	EVEdge(int _val, int _weight, const EVNode& _dest) : val(_val), weight(_weight), dest(_dest) {}

	int val;
	int weight;
	EVNode dest;
};

class EVLayerGraph {
	// Local structs
	//==============
	typedef struct {
		int id;
		int next;
		int flag;
	} TravInfo;

	// Globally visible structs
	//=========================
public:
	typedef struct {
		int val;
		int weight;
		int dest;
	} EInfo;

	typedef struct {
		unsigned int var;
		unsigned int sz;

		EInfo edges[1];
	} NodeInfo;

	typedef NodeInfo* NodeRef;
	typedef int NodeID;

	// Need to set up a nice interface for traversal.
	class IterNode {
	public:
		IterNode(EVLayerGraph* _graph, int _idx) : graph(_graph), idx(_idx) {}

		EVLayerGraph* graph;
		int idx;
	};

	// Local structs
	//==============
protected:
	struct eqnode {
		bool operator()(const NodeRef a1, const NodeRef a2) const {
			if (a1->var != a2->var) {
				return false;
			}
			if (a1->sz != a2->sz) {
				return false;
			}

			for (unsigned int ii = 0; ii < a1->sz; ii++) {
				if (a1->edges[ii].val != a2->edges[ii].val || a1->edges[ii].dest != a2->edges[ii].dest ||
						a1->edges[ii].weight != a2->edges[ii].weight) {
					return false;
				}
			}
			return true;
		}
	};

	struct hashnode {
		unsigned int operator()(NodeRef a1) const;
	};

	typedef std::unordered_map<const NodeRef, NodeID, hashnode, eqnode> NodeCache;

	// Public Methods
public:
	EVLayerGraph();  // Do we need the number of variables as a parameter?
	~EVLayerGraph();

	NodeID insert(int level, vec<EInfo>& edges);

	// Initialize the traversal info stuff.
	// Returns the size of the computed subgraph.
	int traverse(NodeID idx);
	EVNode travBegin() { return EVNode(this, status[0].next); }
	EVNode travEnd() { return EVNode(this, -1); }

	const static int EVFalse;
	const static int EVTrue;

protected:
	static inline NodeRef allocNode(int sz);
	static inline void deallocNode(NodeRef node);

	int nvars;

	OpCache opcache;
	NodeCache cache;

	int intermed_maxsz;
	NodeRef intermed;

public:
	std::vector<NodeRef> nodes;

	// Traversal information.
	std::vector<TravInfo> status;
};

// Transition for a cost-regular constraint.
typedef struct {
	int weight;
	int dest;
} WDFATrans;

inline void create_edges(EVLayerGraph& graph, vec<EVLayerGraph::EInfo>& edges,
												 const vec<EVLayerGraph::NodeID>& previous_layer, const WDFATrans* T,
												 int dom, int nstates, int soff);
EVLayerGraph::NodeID wdfa_to_layergraph(EVLayerGraph& graph, int nvars, int dom, WDFATrans* T,
																				int nstates, int q0, vec<int>& accepts);

#endif
