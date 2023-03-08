#ifdef __APPLE__
#include <memory>
#define MEMCPY std::memcpy
#else
#include <cstring>
#define MEMCPY memcpy
#endif

#include <chuffed/mdd/weighted_dfa.h>

#include <algorithm>

#include <thirdparty/MurmurHash3/MurmurHash3.h>

#define OPCACHE_SZ 100000

const int EVLayerGraph::EVFalse = (-1);
const int EVLayerGraph::EVTrue = (0);

struct edge_leq {
	bool operator()(const EVLayerGraph::EInfo& e1, const EVLayerGraph::EInfo& e2) {
		if (e1.val != e2.val) {
			return e1.val < e2.val;
		}

		if (e1.dest == e2.dest) {
			return e1.dest < e2.dest;
		}

		return e1.weight < e2.weight;
	}
} edge_leq;

EVLayerGraph::EVLayerGraph() : opcache(OpCache(OPCACHE_SZ)), intermed_maxsz(2) {
	// Initialize \ttt
	nodes.push_back(nullptr);  // true node
	TravInfo tinfo = {0, -1, 1};
	status.push_back(tinfo);

	intermed = allocNode(intermed_maxsz);
}

EVLayerGraph::~EVLayerGraph() {
	deallocNode(intermed);
	for (unsigned int i = 2; i < nodes.size(); i++) {
		deallocNode(nodes[i]);
	}
}

EVLayerGraph::NodeID EVLayerGraph::insert(int level, vec<EInfo>& edges) {
	// Ensure there's adequate space in the intermed node.
	if (intermed_maxsz < edges.size()) {
		while (intermed_maxsz < edges.size()) {
			intermed_maxsz *= 2;
		}

		deallocNode(intermed);
		intermed = allocNode(intermed_maxsz);
	}

	// Normalize the edges, and copy them to the checker.
	std::sort(((EInfo*)edges), ((EInfo*)edges) + edges.size(), edge_leq);

	int jj = 0;
	int ii;
	// Copy the first non-F edge to the intermed node.
	for (ii = 0; ii < edges.size(); ii++) {
		if (edges[ii].dest != EVFalse) {
			intermed->edges[jj++] = edges[ii++];
			break;
		}
	}
	// Copy the remaining non-dominated edges.
	for (; ii < edges.size(); ii++) {
		if (edges[ii].dest == EVFalse) {
			continue;
		}
		if (intermed->edges[jj - 1].val != edges[ii].val ||
				intermed->edges[jj - 1].dest != edges[ii].dest) {
			intermed->edges[jj++] = edges[ii];
		}
	}

	// If there are no edges, it's F.
	if (jj == 0) {
		return EVFalse;
	}

	intermed->var = level;
	intermed->sz = jj;

	// Check if the normalized node is already in the table.
	auto res = cache.find(intermed);

	// If so, return it.
	if (res != cache.end()) {
		return (*res).second;
	}

	// Otherwise, add it.
	NodeRef node = allocNode(intermed->sz);

	MEMCPY(node, intermed, sizeof(NodeInfo) + (((int)intermed->sz) - 1) * (sizeof(EInfo)));

	int nID = nodes.size();
	cache[node] = nID;
	nodes.push_back(node);
	TravInfo tinfo = {0, 0, 0};
	status.push_back(tinfo);

	return nID;
}

// Set up the traversal information from a given node.
int EVLayerGraph::traverse(NodeID idx) {
	vec<int> queue;
	int qhead = 0;

	status[0].flag = 1;
	status[0].id = 0;
	int prev = 0;

	queue.push(idx);
	status[idx].flag = 1;
	status[idx].id = queue.size();
	status[prev].next = idx;
	prev = idx;

	while (qhead < queue.size()) {
		int nodeIdx = queue[qhead];

		NodeRef node(nodes[nodeIdx]);
		for (unsigned int ei = 0; ei < node->sz; ei++) {
			int dest = node->edges[ei].dest;
			if (status[dest].flag == 0) {
				status[dest].flag = 1;
				queue.push(dest);
				status[dest].id = queue.size();
				status[prev].next = dest;
				prev = dest;
			}
		}
		qhead++;
	}
	status[prev].next = -1;

	for (qhead = 0; qhead < queue.size(); qhead++) {
		status[queue[qhead]].flag = 0;
	}

	// Return the number of nodes.
	return queue.size() + 1;
}

EVLayerGraph::NodeRef EVLayerGraph::allocNode(int sz) {
	return ((NodeRef)malloc(sizeof(NodeInfo) + (sz - 1) * sizeof(EInfo)));
}

inline void EVLayerGraph::deallocNode(EVLayerGraph::NodeRef node) { free(node); }

inline void create_edges(EVLayerGraph& graph, vec<EVLayerGraph::EInfo>& edges,
												 const vec<EVLayerGraph::NodeID>& previous_layer, const WDFATrans* T,
												 int dom, int nstates, int soff) {
	edges.clear();
	for (int xi = 0; xi < dom; xi++) {
		int tidx = soff + xi;
		const WDFATrans& trans(T[tidx]);
		int destination = trans.dest;
		if (destination > 0)  // a valid transition
		{
			destination--;
			EVLayerGraph::NodeID dest = previous_layer[destination];
			if (dest != EVLayerGraph::EVFalse) {
				EVLayerGraph::EInfo edge = {xi + 1, trans.weight, previous_layer[destination]};
				edges.push(edge);
			}
		}
	}
}

EVLayerGraph::NodeID wdfa_to_layergraph(EVLayerGraph& graph, int nvars, int dom, WDFATrans* T,
																				int nstates, int q0, vec<int>& accepts) {
	vec<EVLayerGraph::NodeID> layers[2];
	int curr = 0;
	int prev = 1;

	// At the bottem level, only accept states can reach T
	for (int si = 0; si < nstates; si++) {
		layers[curr].push(EVLayerGraph::EVFalse);
	}

	for (int ai = 0; ai < accepts.size(); ai++) {
		layers[curr][accepts[ai] - 1] = EVLayerGraph::EVTrue;
	}

	vec<EVLayerGraph::EInfo> edges;

	for (int vv = nvars - 1; vv > 0; vv--) {
		// Alternate the levels
		curr = 1 - curr;
		prev = 1 - prev;
		layers[curr].clear();

		for (int si = 0; si < nstates; si++) {
			int soff = si * dom;
			create_edges(graph, edges, layers[prev], T, dom, nstates, soff);
			layers[curr].push(graph.insert(vv, edges));
		}
	}

	int soff = (q0 - 1) * dom;
	prev = 1 - prev;
	create_edges(graph, edges, layers[prev], T, dom, nstates, soff);
	int root = graph.insert(0, edges);
	return root;
}

EVEdge EVNode::operator[](int eidx) const {
	EVLayerGraph::EInfo edge(g->nodes[idx]->edges[eidx]);
	return EVEdge(edge.val, edge.weight, EVNode(g, edge.dest));
}

int EVNode::id() const { return g->status[idx].id; }

int EVNode::var() const { return g->nodes[idx]->var; }

int EVNode::size() const { return g->nodes[idx]->sz; }

EVNode& operator++(EVNode& x) {
	x.idx = x.g->status[x.idx].next;
	return x;
}

unsigned int EVLayerGraph::hashnode::operator()(const NodeRef a1) const {
	unsigned int hash = 5381;

	hash = ((hash << 5) + hash) + a1->var;
	hash = ((hash << 5) + hash) + a1->sz;
#if 0
    for(unsigned int ii = 0; ii < a1->sz; ii++)
    {
        hash = ((hash << 5) + hash) + a1->edges[ii].val;
        hash = ((hash << 5) + hash) + a1->edges[ii].weight;
        hash = ((hash << 5) + hash) + a1->edges[ii].dest;
    }
    return (hash & 0x7FFFFFFF);
#else
	uint32_t ret;
	MurmurHash3_x86_32(&(a1->edges), sizeof(EInfo) * a1->sz, hash, &ret);
	return ret;
#endif
}