#include "graph.h"
#include <iostream>
using namespace std;

#define GRAPHPROP_DEBUG 0


void GraphPropagator::fullExpl(vec<Lit>& ps) {
    for (int i = 0; i < nbNodes(); i++)
        if (getNodeVar(i).isFixed())
            ps.push(getNodeVar(i).getValLit());
    for (int i = 0; i < nbEdges(); i++)
        if (getEdgeVar(i).isFixed())
            ps.push(getEdgeVar(i).getValLit());
                
}
void GraphPropagator::fullExpl(vector<Lit>& ps) {
    for (int i = 0; i < nbNodes(); i++)
        if (getNodeVar(i).isFixed())
            ps.push_back(getNodeVar(i).getValLit());
    for (int i = 0; i < nbEdges(); i++)
        if (getEdgeVar(i).isFixed())
            ps.push_back(getEdgeVar(i).getValLit());
                
}

vector<Lit> GraphPropagator::fullExpl(bool fail) {
    vector<Lit> ps;
    if (!fail) ps.push_back(Lit());
    for (int i = 0; i < nbNodes(); i++)
        if (getNodeVar(i).isFixed())
            ps.push_back(getNodeVar(i).getValLit());
    for (int i = 0; i < nbEdges(); i++)
        if (getEdgeVar(i).isFixed())
            ps.push_back(getEdgeVar(i).getValLit());
    return ps;
}


GraphPropagator::GraphPropagator(vec<BoolView>& _vs, vec<BoolView>& _es,
                                 vec< vec<int> >& _en)
    : vs(_vs),es(_es){
    endnodes = std::vector< std::vector<int> >(_en.size(),std::vector<int>());
    for (int i = 0; i < _en.size(); i++) {
        for (int j = 0; j < _en[i].size(); j++) //when directed:  
            endnodes[i].push_back(_en[i][j]); //[0] ---> [1] 
    }
    if (DEBUG)
        for (int i = 0; i < nbEdges(); i++)
            cout << i<<" "<<_en[i][0]<<" "<<_en[i][1]<<endl;

    priority = 1;
}

GraphPropagator::~GraphPropagator() {

}

void GraphPropagator::attachToAll() {
    //Do not use in inheriting classes!!
    for (int j = 0; j < nbNodes(); j++) {
        getNodeVar(j).attach(this, j,EVENT_LU);
    }
    for (int j = 0; j < nbEdges(); j++) {
        getEdgeVar(j).attach(this, j,EVENT_LU);
    }
}

void GraphPropagator::wakeup(int i, int c) {
    pushInQueue();
}

bool GraphPropagator::propagate() {
    for (int i = 0; i < nbNodes(); i++) {
        if (getNodeVar(i).isFixed() && getNodeVar(i).isFalse())
            if(!coherence_outedges(i))
                return false;
    }
    for (int i = 0; i < nbEdges(); i++) {
        if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue())
            if(!coherence_innodes(i))
                return false;
    }
    return true;
}


bool GraphPropagator::coherence_outedges(int node) {
    vector<int> useless;
    return coherence_outedges(node,useless);
}

/**
 * Forces the incident edges to 'node' to be out-edges when 'node' is an outnode
 * return true if no conflict, false otherwise (explanation built inside)
 */
bool GraphPropagator::coherence_outedges(int node, vector<edge_id>& remvd_e) {
    for (int i = 0; i < adj[node].size(); i++){
        edge_id edge = adj[node][i];
        //Edge with missing an endnode
        if (es[edge].isFixed() && es[edge].getVal() == 1){
            if(so.lazy) {
                vec<Lit> ps;
                ps.push(es[edge].getValLit());
                ps.push(vs[node].getValLit());
                Clause *expl = Clause_new(ps);
                expl->temp_expl = 1;
                sat.rtrail.last().push(expl);
                sat.confl = expl;
            }
            return false;
        } 
        //Edge that must be removed
        if (!es[edge].isFixed()){
            Clause* r = NULL;
            if(so.lazy){
                r = Reason_new(2);
                (*r)[1] = vs[node].getValLit();
            }
            if (GRAPHPROP_DEBUG) 
                cout << "COHERENCE (E) "<<edge<<endl;
            es[edge].setVal2(false,r);
            remvd_e.push_back(edge);
        }
    }
    return true;
}

bool GraphPropagator::coherence_innodes(int edge) {
    vector<int> useless;
    return coherence_innodes(edge,useless);
}

/**
 * Forces the endnodes of 'edge' to be innodes when 'edge' is an inedge
 * return true if no conflict, false otherwise (explanation built inside)
 */
bool GraphPropagator::coherence_innodes(int edge, vector<node_id>& added_n) {
    for (int i = 0; i < endnodes[edge].size(); i++) {
        int u = endnodes[edge][i];
        if (vs[u].isFixed() && vs[u].getVal() == 0){
            if (so.lazy) {
                vec<Lit> ps;
                ps.push(es[edge].getValLit());
                ps.push(vs[u].getValLit());
                Clause *expl = Clause_new(ps);
                expl->temp_expl = 1;
                sat.rtrail.last().push(expl);
                sat.confl = expl;
            }
            return false;
        }
        if (!vs[u].isFixed()) {
            Clause* r = NULL;
            if(so.lazy){
                r = Reason_new(2);
                (*r)[1] = es[edge].getValLit();
            }
            if (GRAPHPROP_DEBUG) 
                cout << "COHERENCE (N) "<<u<<endl;
            vs[u].setVal2(true,r);
            added_n.push_back(u);
        }
    }
    return true;
}

void GraphPropagator::clearPropState() {
    Propagator::clearPropState();
}


std::string GraphPropagator::available_to_dot() {
    string res = "graph {\n";
    for (int n = 0; n < nbNodes(); n++) {
        if (getNodeVar(n).isFixed() && getNodeVar(n).isTrue())
            res += " " + to_string(n) + " [color = red];\n";
    }
    for (int e = 0; e < nbEdges(); e++) {
        if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isTrue()) {
            res += " " + to_string(getTail(e)) + " -- " + to_string(getHead(e));
            if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) 
                res += " [color = red] ";
        res += "[label = \""+to_string(e)+"\"]";
            res += ";\n";
        }
    }
    res +="}";
    
    return res;
}

std::string GraphPropagator::all_to_dot() {
    string res = "graph {\n";
    for (int n = 0; n < nbNodes(); n++) {
        if (getNodeVar(n).isFixed() && getNodeVar(n).isTrue())
            res += " " + to_string(n) + " [color = red];\n";
        if (getNodeVar(n).isFixed() && getNodeVar(n).isFalse())
            res += " " + to_string(n) + " [color = yellow];\n";
    }
    for (int e = 0; e < nbEdges(); e++) {
        res += " " + to_string(getTail(e)) + " -- " + to_string(getHead(e));
        if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) 
            res += " [color = red] ";
        else if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) 
            res += " [color = yellow] ";
        res += "[label = \""+to_string(e)+"\"]";
        res += ";\n";
    }
    res +="}";
    
    return res;
}

std::string GraphPropagator::available_to_dot(int* arr) {
    string res = "graph {\n";
    for (int n = 0; n < nbNodes(); n++) {
        if (getNodeVar(n).isFixed() && getNodeVar(n).isTrue())
            res += " " + to_string(n) + " [color = red];\n";
    }
    for (int e = 0; e < nbEdges(); e++) {
        if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isTrue()) {
            res += " " + to_string(getTail(e)) + " -- " + to_string(getHead(e));
            if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) 
                res += " [color = red] ";
        res += "[label = \""+to_string(arr[e])+"\"]";
            res += ";\n";
        }
    }
    res +="}";
    
    return res;
}

std::string GraphPropagator::all_to_dot(int* arr) {
    string res = "graph {\n";
    for (int n = 0; n < nbNodes(); n++) {
        if (getNodeVar(n).isFixed() && getNodeVar(n).isTrue())
            res += " " + to_string(n) + " [color = red];\n";
        if (getNodeVar(n).isFixed() && getNodeVar(n).isFalse())
            res += " " + to_string(n) + " [color = yellow];\n";
    }
    for (int e = 0; e < nbEdges(); e++) {
        res += " " + to_string(getTail(e)) + " -- " + to_string(getHead(e));
        if (getEdgeVar(e).isFixed() && getEdgeVar(e).isTrue()) 
            res += " [color = red] ";
        else if (getEdgeVar(e).isFixed() && getEdgeVar(e).isFalse()) 
            res += " [color = yellow] ";
        res += "[label = \""+to_string(arr[e])+"\"]";
        res += ";\n";
    }
    res +="}";
    
    return res;
}
