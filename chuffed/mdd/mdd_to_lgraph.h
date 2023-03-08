#ifndef MDD_TO_LAYERGRAPH_H_
#define MDD_TO_LAYERGRAPH_H_
#include <chuffed/mdd/MDD.h>
#include <chuffed/mdd/weighted_dfa.h>

EVLayerGraph::NodeID mdd_to_layergraph(EVLayerGraph& graph, MDD& r, vec<int>& costs);

#endif
