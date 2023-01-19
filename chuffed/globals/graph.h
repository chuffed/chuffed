#ifndef GRAPH_PROPAGATOR_H
#define GRAPH_PROPAGATOR_H

#include <chuffed/core/propagator.h>
#include <chuffed/support/union_find.h>
#include <map>
#include <set>
#include <stack>
#include <queue>
#include <vector>



typedef int edge_id;
typedef int node_id;



class GraphPropagator : public Propagator{
public:
    vec< BoolView > vs;
    vec< BoolView > es;


    std::vector<std::vector<int> > nodes2edge;
    std::vector< std::vector<node_id> > endnodes;
    virtual void fullExpl(vec<Lit>& ps); //DEBUG
    virtual void fullExpl(std::vector<Lit>& ps); //DEBUG
    virtual std::vector<Lit> fullExpl(bool fail);

    std::vector< std::vector<edge_id> > adj;

    bool coherence_innodes(int edge);
    bool coherence_outedges(int node);
    bool coherence_innodes(int edge, std::vector<node_id>& added_n);
    bool coherence_outedges(int node, std::vector<edge_id>& remvd_e);



public:
    GraphPropagator(vec<BoolView>& _vs, vec<BoolView>& _es, 
                    vec< vec<int> >& _en);
    virtual void clearPropState();
    virtual ~GraphPropagator();


    virtual void attachToAll();
    virtual void wakeup(int i, int c);
    virtual bool propagate();
    

    inline BoolView& getNodeVar(int u) {
        assert(u >= 0);
        assert(u < vs.size());
        return vs[u];
    }

    inline BoolView& getEdgeVar(int e) {
        assert(e >= 0);
        assert(e < es.size());
        return es[e];
    }

    inline int nbNodes() {
        return vs.size();
    }

    inline int nbEdges() {
        return es.size();
    }

    inline int getHead(int e) {
        assert(e >= 0);
        assert(e < es.size());
        return endnodes[e][1];
    }

    inline int getTail(int e) {
        assert(e >= 0);
        assert(e < es.size());
        return endnodes[e][0];
    }

    inline int getEndnode(int e, int n) {
        assert(e >= 0);
        assert(e < es.size());
        assert(n >= 0 && n < 2);
        return endnodes[e][n];
    }

    inline int getOtherEndnode(int e, int u) {
        assert(e >= 0);
        assert(e < es.size());
        return endnodes[e][0] == u ? endnodes[e][1] : endnodes[e][0];
    }

    inline bool isSelfLoop(int e) {
        return getEndnode(e,0) == getEndnode(e,1);
    }

    inline std::vector<int> getAdjacentEdges(int u) {
        return adj[u];
    }

    std::string available_to_dot();
    std::string all_to_dot();

    std::string available_to_dot(int* arr);
    std::string all_to_dot(int* arr);
};


#endif
