#include "chuffed/mdd/mdd_to_lgraph.h"

#include "chuffed/mdd/MDD.h"
#include "chuffed/mdd/weighted_dfa.h"
#include "chuffed/support/vec.h"

#include <algorithm>
#include <vector>

// Convert a MDD into a edge-valued layer graph according to an array of costs.
EVLayerGraph::NodeID mdd_to_layergraph(EVLayerGraph& graph, MDD& r, vec<int>& costs) {
	MDDTable& t(*r.table);
	MDDNodeInt root = r.val;
	root = t.expand(0, root);

	const std::vector<MDDNode>& nodes(t.getNodes());
	std::vector<int>& status(t.getStatus());

	// Mark T and F as seen.
	status[0] = 1;
	status[1] = 1;

	vec<int> node_queue;

	status[root] = 1;
	node_queue.push(root);

	// Compute the set of edges.
	// We're assuming they're collected in topological order.
	int qhead = 0;
	while (qhead < node_queue.size()) {
		const int nID = node_queue[qhead];

		MDDNode nodeptr = nodes[nID];
		for (unsigned int j = 0; j < nodeptr->sz; j++) {
			if (status[nodeptr->edges[j].dest] == 0) {
				node_queue.push(nodeptr->edges[j].dest);
				status[nodeptr->edges[j].dest] = 1;
			}
		}
		qhead++;
	}

	// Assign the terminal states.
	status[0] = EVLayerGraph::EVFalse;
	status[1] = EVLayerGraph::EVTrue;

	// Scan the nodes in reverse topological order, and
	// construct the corresponding ev-node.
	for (qhead = node_queue.size() - 1; qhead >= 0; qhead--) {
		const int nID = node_queue[qhead];
		MDDNode nodeptr = nodes[nID];
		const int vv = nodeptr->var;

		vec<EVLayerGraph::EInfo> edges;
		for (unsigned int j = 0; j < nodeptr->sz; j++) {
			if (nodeptr->edges[j].val > costs.size()) {
				break;
			}

			if (nodeptr->edges[j].dest != MDDFALSE) {
				const EVLayerGraph::NodeID dest = status[nodeptr->edges[j].dest];
				const unsigned int start = std::max(0, nodeptr->edges[j].val);
				const unsigned int end = (j + 1 < nodeptr->sz && nodeptr->edges[j + 1].val <= costs.size())
																		 ? nodeptr->edges[j + 1].val
																		 : costs.size();
				for (unsigned int k = start; k < end; k++) {
					const EVLayerGraph::EInfo einfo = {static_cast<int>(k), costs[k], dest};
					edges.push(einfo);
				}
			}
		}
		status[nID] = graph.insert(vv, edges);
	}

	const EVLayerGraph::NodeID ret = status[root];

	// Clear the status flags.
	status[0] = 0;
	status[1] = 0;
	for (qhead = 0; qhead < node_queue.size(); qhead++) {
		status[node_queue[qhead]] = 0;
	}

	return ret;
}
