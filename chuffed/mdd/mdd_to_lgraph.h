#ifndef __MDD_TO_LAYERGRAPH_H__
#define __MDD_TO_LAYERGRAPH_H__
#include <chuffed/mdd/MDD.h>
#include <chuffed/mdd/weighted_dfa.h>

EVLayerGraph::NodeID mdd_to_layergraph(EVLayerGraph& graph, MDD& r, vec<int>& costs);

#endif
