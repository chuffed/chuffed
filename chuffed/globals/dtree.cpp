#include <chuffed/globals/dtree.h>

#include <stack>
#include <iostream>

using namespace std;

#define DEBUG 0


DTreePropagator::DTreePropagator(int _r, vec<BoolView>& _vs, vec<BoolView>& _es,
                    vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
                    vec< vec<int> >& _en) 
    : DReachabilityPropagator(_r,_vs,_es,_in,_out,_en),
      uf(nbNodes()),ruf(nbNodes()){
    priority = 1;


    for (unsigned int i = 0; i < in[get_root_idx()].size(); i++){
        int e = in[get_root_idx()][i];
        if (getEdgeVar(e).setValNotR(false)) {
            getEdgeVar(e).setVal(false,NULL);
        }
    }
}

DTreePropagator::~DTreePropagator() {

}

bool DTreePropagator::propagateNewEdge(int e) {
    if (!DReachabilityPropagator::propagateNewEdge(e))
        return false;
    
    if (!check_cycle(e)) {
        return false;
    }

    int hd = getHead(e);
    /*
    //Only one incident edge.
    Clause* r = NULL;
    for (int i = 0; i < in[hd].size(); i++) {
        int incident = in[hd][i];
        if (incident == e)
            continue;
        if (getEdgeVar(incident).isFixed() && getEdgeVar(incident).isTrue()) {
            //Fail: 2 incident edges
            if (so.lazy) {
                vec<Lit> ps;
                ps.push(getEdgeVar(e).getValLit());
                Clause *expl = Clause_new(ps);
                expl->temp_expl = 1;
                sat.rtrail.last().push(expl);
                sat.confl = expl;
            }
            return false;
        } else if (!getEdgeVar(incident).isFixed()) {
            //Make it false: only 1 incident edge
            if (so.lazy) {
                vec<Lit> ps; ps.push();
                ps.push(getEdgeVar(e).getValLit());
                r = Reason_new(ps);
            }
            getEdgeVar(incident).setVal(false,r);
        }
    }
    */

    uf.unite(getTail(e),getHead(e));
    assert(uf.connected(getTail(e),getHead(e)));
    ruf.unite(getTail(e),getHead(e));
    assert(ruf.connected(getTail(e),getHead(e)));

    //TODO: this could be done slightly faster with a DFS
    for (int i = 0; i < nbNodes(); i++) {
        if (uf.connected(hd,i)) {
            for (unsigned int j = 0; j < in[i].size(); j++)
                prevent_cycle(in[i][j]);
            for (unsigned int j = 0; j < ou[i].size(); j++)
                prevent_cycle(ou[i][j]);//*/
        }
    }



    processed_e[e] = true;
    /*
    int tl = getTail(e);
    for (int i = 0; i < ou[tl].size(); i++) {
        int oe = ou[tl][i];
        if (e == oe)
            continue;
        if (!getEdgeVar(oe).isFixed()) {
            Clause* r =NULL;
            if (so.lazy) {
                vec<Lit> ps; ps.push();
                ps.push(getEdgeVar(e).getValLit());
                r = Reason_new(ps);
            }
            getEdgeVar(oe).setVal(false,r);
        } else if (getEdgeVar(oe).isTrue()) {
            if (so.lazy) {
                vec<Lit> pathe;
                pathe.push(getEdgeVar(e).getValLit());
                pathe.push(getEdgeVar(oe).getValLit());
                Clause *expl = Clause_new(pathe);
                expl->temp_expl = 1;
                sat.rtrail.last().push(expl);
                sat.confl = expl;
            }
            return false;
        }
    }
    for (int i = 0; i < in[hd].size(); i++) {
        int ie = in[hd][i];
        if (e == ie)
            continue;
        if (!getEdgeVar(ie).isFixed()) {
            Clause* r =NULL;
            if (so.lazy) {
                vec<Lit> ps; ps.push();
                ps.push(getEdgeVar(e).getValLit());
                r = Reason_new(ps);
            }
            getEdgeVar(ie).setVal(false,r);
        } else if (getEdgeVar(ie).isTrue()) {
            if (so.lazy) {
                vec<Lit> pathe;
                pathe.push(getEdgeVar(e).getValLit());
                pathe.push(getEdgeVar(ie).getValLit());
                Clause *expl = Clause_new(pathe);
                expl->temp_expl = 1;
                sat.rtrail.last().push(expl);
                sat.confl = expl;
            }
            return false;
        }
    }

    //*/


    return true;
}

bool DTreePropagator::propagateNewNode(int n) {
    if (!DReachabilityPropagator::propagateNewNode(n))
        return false;

    for (unsigned int i = 0; i < in[n].size(); i++) {
        prevent_cycle(in[n][i]);
    }
    for (unsigned int i = 0; i < ou[n].size(); i++) {
        prevent_cycle(ou[n][i]);
    }

    processed_n[n] = true;
    
    return true;
}

void DTreePropagator::explain_cycle(int u, int v, vec<Lit>& pathe) {
    assert(u!=v);
    vector<int> pathn = ruf.connectionsFromTo(u,v);
    assert(pathn.size() > 0);
    for (int k = 0; k < pathn.size() - 1; k++) {
        int de = findEdge(pathn[k],pathn[k+1]);
        if (de == -1 || !getEdgeVar(de).isFixed() || getEdgeVar(de).isFalse())
            de = findEdge(pathn[k+1],pathn[k]);
        assert(de != -1);
        assert(getEdgeVar(de).isFixed());
        assert(getEdgeVar(de).isTrue());
        pathe.push(getEdgeVar(de).getValLit());
    }
}

bool DTreePropagator::check_cycle(int e) {
    if (uf.connected(getTail(e),getHead(e)) && getTail(e) != getHead(e)) {
        //Explain
        if (so.lazy) {
            vec<Lit> pathe;
            explain_cycle(getTail(e),getHead(e),pathe);
            assert(pathe.size() > 0);
            pathe.push(getEdgeVar(e).getValLit());
            //fullExpl(pathe);
            Clause *expl = Clause_new(pathe);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;
        }

        return false;
    }
    
    return true;
}

void DTreePropagator::prevent_cycle(int e) {
    if(!getEdgeVar(e).isFixed()) {
        if (uf.connected(getTail(e),getHead(e)) && getTail(e) != getHead(e)) {
            Clause* r= NULL;
            if (so.lazy) {
                vec<Lit> pathe;
                pathe.push();
                //fullExpl(pathe);
                explain_cycle(getTail(e),getHead(e),pathe);
                assert(pathe.size() > 1);
                r = Reason_new(pathe);
            }
            getEdgeVar(e).setVal(false,r);
            //last_state_e[e] = OUT; //Can't cause a failure in reachability
            rem_edge.insert(e);
        }
    }
}

bool DTreePropagator::propagate() {
    processed_n = vector<bool>(nbNodes(),false);
    processed_e = vector<bool>(nbEdges(),false);
    if (!DReachabilityPropagator::propagate()) {
        return false;
    }

    assert(test_ruf());

    //Update de Union-Finds.
    set<int>::iterator it;
    for (it = new_edge.begin(); it != new_edge.end(); ++it) {
        if (!processed_e[*it]) {
            if(!propagateNewEdge(*it)){
                return false;
            }
            processed_e[*it] = true;
            last_state_e[*it] = IN;
        }
    }
    
    for (it = new_node.begin(); it != new_node.end(); ++it) {
        if (!processed_n[*it]) {
            if(!propagateNewNode(*it)){
                return false;
            }
            processed_n[*it] = true;
            last_state_n[*it] = IN;
        }
    }
    assert(test_ruf());
    return true;
}

bool DTreePropagator::checkFinalSatisfied() {
    stack<node_id> s;
    s.push(get_root_idx());
    vector<bool> vis = vector<bool>(nbNodes(), false);
    while(!s.empty()) {
        int curr = s.top(); 
        s.pop();
        vis[curr] = true;
        for (unsigned int i = 0; i < ou[curr].size(); i++) {
            int e = ou[curr][i];
            if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isFalse())
                continue;
            int o = getHead(e);
            if (!vis[o]) {
                s.push(o);
            } else {
                if(DEBUG) {
                    cout <<"Edges in: ";
                    for (int i = 0; i < nbEdges(); i++) {
                        if(getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue())
                            cout <<i<<" ";
                    }
                    cout <<endl;
                }
                assert(false);
                cerr<< "DTreePropagator not satisfied "<<__FILE__<<":"<<__LINE__<<endl;
                return false;
            }
        }
    }
    return true;
}



DTreeParenthoodPropagator::DTreeParenthoodPropagator(int _r, vec<BoolView>& _vs,
                                                     vec<BoolView>& _es,
                                                     vec<IntVar*>& _parents,
                                                     vec< vec<edge_id> >& _in, 
                                                     vec< vec<edge_id> >& _out,
                                                     vec< vec<int> >& _en) 
    : DTreePropagator(_r,_vs,_es,_in,_out,_en),parents(_parents) {

    assert(parents.size() == nbNodes());

    first_event = nbNodes()+nbEdges()+1;
    int count = first_event;
    for (int i = 0; i < nbNodes(); i++) {
        parents[i]->specialiseToEL();
        for (int val = 0; val < nbNodes(); val++) {
            equalities.push(parents[i]->getLit(val,1)); //parents[i] == val
            equalities.last().attach(this, count, EVENT_LU);
#if __cplusplus <= 199711L
            event2parrel[count] = std::make_pair<int,int>(i,val);
#else
            event2parrel[count] = std::make_pair(i,val);
#endif
            count++;
        }
    }
    last_event = count;

    assert(equalities.size() == nbNodes() * nbNodes());

    //Figure out the domains of the int vars
    dom_size = new Tint[nbNodes()];
    for (int i = 0; i < nbNodes() ; i++) {
        int in_deg = 0;
        if(parents[i]->setMaxNotR(nbNodes()-1))
            parents[i]->setMax(nbNodes()-1);
        if (parents[i]->setMinNotR(0))
            parents[i]->setMin(0);
        for (int j = 0; j < nbNodes(); j++) {
            int e = findEdge(j,i);
            if (e != -1) {
                if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isTrue()) {
                    in_deg++;
                } else {
                    if (i != j && parents[i]->remValNotR(j))
                        parents[i]->remVal(j,NULL);
                }
            } else {
                if (i != j && parents[i]->remValNotR(j))
                    parents[i]->remVal(j,NULL);
            }
        }
        dom_size[i] = parents[i]->size();
        assert(dom_size[i] > 0);
    }
    if (DEBUG) {
        cout <<"Parents: ";
        for(int i = 0; i < nbNodes(); i++){
            cout <<" (";
            IntVar::const_iterator it = parents[i]->begin();
            for ( ; it != parents[i]->end(); it++) {
                cout << *it<<",";
            }
            cout <<") ";
        }
        cout<<endl;
    }
}

DTreeParenthoodPropagator::~DTreeParenthoodPropagator() {
    delete dom_size;
}

bool DTreeParenthoodPropagator::propagateNewEdge(int e) {
    assert(getEdgeVar(e).isFixed());
    assert(getEdgeVar(e).isTrue());
    //Check if tail of e can be parent of head of e
    //make it so if ok
    if (!DTreePropagator::propagateNewEdge(e))
        return false;

    if (parents[getHead(e)]->indomain(getTail(e))) {
        Clause* r = NULL;
        if (!parents[getHead(e)]->isFixed()) {
            if (so.lazy) {
                vec<Lit> ps; ps.push();
                ps.push(getEdgeVar(e).getValLit());
                r = Reason_new(ps);
            }
            parents[getHead(e)]->setVal(getTail(e),r);
        }
        dom_size[getHead(e)] = parents[getHead(e)]->size();
    } else {
        if (so.lazy) {
            vec<Lit> psfail; 
            psfail.push(getEdgeVar(e).getValLit());
            psfail.push(equalities[getHead(e)*nbNodes()+getTail(e)].getValLit()); //not(parent of tl is hd)
            Clause *expl = Clause_new(psfail);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;   
        }
        return false;
    }
    return true;
    
}

bool DTreeParenthoodPropagator::propagateRemEdge(int e) {
    assert(getEdgeVar(e).isFixed());
    assert(getEdgeVar(e).isFalse());

    if (!DTreePropagator::propagateRemEdge(e))
        return false;

    //If tail of e is the only possible parent of head of e
    //fail (unless head of e is the root)
    //Otherwise remove that value and that's it.
    if (parents[getHead(e)]->indomain(getTail(e))) {
        if (getHead(e) == getTail(e))
            return true;
        Clause* r = NULL;
        if (so.lazy) {
            vec<Lit> ps; ps.push();
            ps.push(getEdgeVar(e).getValLit());
            r = Reason_new(ps);
        }
        parents[getHead(e)]->remVal(getTail(e),r);
        if(DEBUG) cout <<"This guy "<<getHead(e)<<" cannot have "<<getTail(e)
                       <<" as a parent, because I removed edge"<<e<<endl; 
        assert(parents[getHead(e)]->size() > 0);
        dom_size[getHead(e)] = parents[getHead(e)]->size();
    }

    return true;
}


bool DTreeParenthoodPropagator::propagateNewParent(int e) {
    int par = getTail(e);
    int chi = getHead(e);

    Clause* r = NULL;
    //If the nodes is not in the tree, it's it's own parent
    //and need no selfloop. It requires that the node actually
    //does not have a parent.
    if (par == chi) {
        if (so.lazy) {
            vec<Lit> ps; ps.push();
            //Because I am my own parent, every edge is false (except self loop)
            ps.push(parents[chi]->getLit(par,1));
            r = Reason_new(ps);
        }
        for (unsigned int i = 0; i < in[chi].size(); i++) {
            int edge = in[chi][i];
            if (getTail(edge) == getHead(edge)) //selfloop
                continue;
            if (!getEdgeVar(edge).isFalse()) { //get out
                getEdgeVar(edge).setVal(false,r);
            } else if (getEdgeVar(edge).isTrue()){ //It actually has a legit parent
                 if (so.lazy) {
                     vec<Lit> ps;
                     //The fact that the parent of chi is not the 
                     //tail of edge, when in the graph 'edge' exists
                     ps.push(parents[chi]->getLit(getTail(edge),0));
                     ps.push(getEdgeVar(edge).getValLit());
                     Clause *expl = Clause_new(ps);
                     expl->temp_expl = 1;
                     sat.rtrail.last().push(expl);
                     sat.confl = expl;
                 }       
                 return false;
            }
        }
        return true;
    }

    //Edge from a node to a different node: (i.e. par != chi)

    if (!getEdgeVar(e).isFixed()) {
        if (so.lazy) {
            vec<Lit> ps; ps.push();
            ps.push(parents[chi]->getLit(par,1));
            r = Reason_new(ps);
        }
        getEdgeVar(e).setVal(true,r);
    } else if (getEdgeVar(e).isFalse()) {
        if (so.lazy) {
            vec<Lit> ps;
            ps.push(getEdgeVar(e).getValLit());   // par-->chi is out
            ps.push(parents[chi]->getLit(par,0)); //not(parents[chi] != par)
            Clause *expl = Clause_new(ps);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;   
        }
        return false;
    }

    return true;
}

bool DTreeParenthoodPropagator::propagateRemParent(int e) {
    int par = getTail(e);
    int chi = getHead(e);

    Clause* r = NULL;
    if (!getEdgeVar(e).isFixed()) {
        if (so.lazy) {
            vec<Lit> ps; ps.push();
            ps.push(parents[chi]->getLit(par,0));
            r = Reason_new(ps);
        }
        getEdgeVar(e).setVal(false,r);
    } else if (getEdgeVar(e).isTrue()) {
        if(so.lazy) {
            vec<Lit> ps; 
            ps.push(getEdgeVar(e).getValLit());   // par-->chi is in
            ps.push(parents[chi]->getLit(par,1)); //not(parents[chi] == par)
            Clause *expl = Clause_new(ps);
            expl->temp_expl = 1;
            sat.rtrail.last().push(expl);
            sat.confl = expl;   
        }
        return false;
    }

    return true;
}

void DTreeParenthoodPropagator::wakeup(int i, int c) {
    priority = 1;
    bool ignore = true;
    if (first_event <= i && i <= last_event) {
        int idx = i - first_event; //Corresponding BoolView
        assert(idx >= 0);
        assert(idx < nbNodes()*nbNodes());
        pair<int,int> hd_tl = event2parrel[i]; //head and tail of edge
        int hd = hd_tl.first;
        int tl = hd_tl.second;
        int e = findEdge(tl,hd);
        //No need to propagate that an edges that does not exist, does not exist
        //or that I already propagated
        if (e != -1 && dom_size[hd] != parents[hd]->size()) {
            assert(equalities[idx].isFixed());
            if (equalities[idx].isTrue()) {
                parenthood_fixed.insert(e);
                ignore = false;
            } else if (equalities[idx].isFalse() ){
                parenthood_abandon.insert(e);
                ignore = false;
            }
        }
        if (!ignore)
            pushInQueue();
    } else {
        DTreePropagator::wakeup(i,c);
    }
}

bool DTreeParenthoodPropagator::propagate() {
    set<int>::iterator it;
    //*
    for (it = parenthood_fixed.begin(); it != parenthood_fixed.end(); ++it) {
        if(!propagateNewParent(*it)){
            if(DEBUG) cout <<"False "<<__FILE__<<__LINE__<<endl;
            return false;
        }
        dom_size[getHead(*it)] = parents[getHead(*it)]->size();
        if (last_state_e[*it] != IN) {
            assert(getHead(*it) == getTail(*it) || getEdgeVar(*it).isFixed());
            assert(getHead(*it) == getTail(*it) || getEdgeVar(*it).isTrue());
            if (getEdgeVar(*it).isFixed() && getEdgeVar(*it).isTrue())
                new_edge.insert(*it);
        }
    }

    for (it = parenthood_abandon.begin(); it != parenthood_abandon.end(); ++it) {
        if(!propagateRemParent(*it)){
            if(DEBUG) cout <<"False "<<__FILE__<<__LINE__<<endl;
            return false;
        }
        dom_size[getHead(*it)] = parents[getHead(*it)]->size();
        if (last_state_e[*it] != OUT) {
            assert(getEdgeVar(*it).isFixed());
            assert(getEdgeVar(*it).isFalse());
            rem_edge.insert(*it);
        }
    }
    //*/

    if (!DTreePropagator::propagate()) {
        if(DEBUG) cout <<"False "<<__FILE__<<__LINE__<<endl;
        return false;
    }

    return true;
}

bool DTreeParenthoodPropagator::checkFinalSatisfied() {
    if (!DTreePropagator::checkFinalSatisfied())
        return false;

    for (int i = 0; i < nbNodes(); i++) {
        assert(parents[i]->isFixed());
        if (!parents[i]->isFixed()) {
            if(DEBUG) {
                cout <<parents[0]->size()<<endl;
                for(int i = 0; i < nbNodes(); i++){
                    cout <<" (";
                    IntVar::const_iterator it = parents[i]->begin();
                    for ( ; it != parents[i]->end(); it++) {
                        cout << *it<<",";
                    }
                    cout <<") ";
                }
            }
            assert(false);
            return false;
        }
        int hd = i;
        int tl = parents[i]->getVal();
        int e = findEdge(tl,hd);
        if (hd == get_root_idx()){
            assert(tl == hd);
            if (tl != hd)
                return false;
            continue;
        } else if (getNodeVar(hd).isFalse()) {
            assert(tl == hd);
            if (tl != hd)
                return false;
            continue;
        } else if (e == -1) {
            assert(e != -1);
            return false;
        }
        assert(getEdgeVar(e).isFixed());
        if(!getEdgeVar(e).isFixed())
            return false;
        assert(getEdgeVar(e).isTrue());
        if(!getEdgeVar(e).isTrue())
            return false;
    }

    return true;
}

void DTreeParenthoodPropagator::clearPropState() {
    DTreePropagator::clearPropState();
    parenthood_fixed.clear();
    parenthood_abandon.clear();
}



// DTreeParenthoodPropagator::DTreeParenthoodPropagator(int _r, vec<BoolView>& _vs,
//                                                      vec<BoolView>& _es,
//                                                      vec<IntVar*>& _parents,
//                                                      vec< vec<edge_id> >& _in, 
//                                                      vec< vec<edge_id> >& _out,
//                                                      vec< vec<int> >& _en) 
//     : DTreePropagator(_r,_vs,_es,_in,_out,_en),parents(_parents) {

//     assert(parents.size() == nbNodes());

//     first_event = nbNodes()+nbEdges()+1;
//     int count = first_event;
//     for (int i = 0; i < nbNodes(); i++) {
//         parents[i]->specialiseToEL();
//         for (int val = 0; val < nbNodes(); val++) {
//             equalities.push(parents[i]->getLit(val,1)); //parents[i] == val
//             equalities.last().attach(this, count, EVENT_LU);
//             event2parrel[count] = std::make_pair<int,int>(i,val);
//             count++;
//         }
//     }
//     last_event = count;

//     assert(equalities.size() == nbNodes() * nbNodes());

//     //Figure out the domains of the int vars
//     dom_size = new Tint[nbNodes()];
//     for (int i = 0; i < nbNodes() ; i++) {
//         int in_deg = 0;
//         if(parents[i]->setMaxNotR(nbNodes()-1))
//             parents[i]->setMax(nbNodes()-1);
//         if (parents[i]->setMinNotR(0))
//             parents[i]->setMin(0);
//         for (int j = 0; j < nbNodes(); j++) {
//             int e = findEdge(j,i);
//             if (e != -1) {
//                 if (!getEdgeVar(e).isFixed() || getEdgeVar(e).isTrue()) {
//                     in_deg++;
//                 } else {
//                     if (i != j && parents[j]->remValNotR(i))
//                         parents[j]->remVal(i,NULL);
//                 }
//             } else {
//                 if (i != j && parents[j]->remValNotR(i))
//                     parents[j]->remVal(i,NULL);
//             }
//             dom_size[j] = parents[j]->size();
//         }
//         dom_size[i] = parents[i]->size();
//         assert(dom_size[i] > 0);
//         //assert(dom_size[i] == 1);
//         //assert(parents[i]->indomain(i));
//     }
//     if (DEBUG) {
//         cout <<"Parents: ";
//         for(int i = 0; i < nbNodes(); i++){
//             cout <<" (";
//             IntVar::const_iterator it = parents[i]->begin();
//             for ( ; it != parents[i]->end(); it++) {
//                 cout << *it<<",";
//             }
//             cout <<") ";
//         }
//         cout<<endl;
//     }
// }

// DTreeParenthoodPropagator::~DTreeParenthoodPropagator() {
//     delete dom_size;
// }

// bool DTreeParenthoodPropagator::propagateNewEdge(int e) {
//     assert(getEdgeVar(e).isFixed());
//     assert(getEdgeVar(e).isTrue());
//     //Check if tail of e can be parent of head of e
//     //make it so if ok
//     if (!DTreePropagator::propagateNewEdge(e))
//         return false;

//     if (parents[getTail(e)]->indomain(getHead(e))) {
//         Clause* r = NULL;
//         if (!parents[getHead(e)]->isFixed()) {
//             if (so.lazy) {
//                 vec<Lit> ps; ps.push();
//                 ps.push(getEdgeVar(e).getValLit());
//                 r = Reason_new(ps);
//             }
//             parents[getTail(e)]->setVal(getHead(e),r);
//         }
//         dom_size[getTail(e)] = parents[getTail(e)]->size();
//     } else {
//         if (so.lazy) {
//             vec<Lit> psfail; 
//             psfail.push(getEdgeVar(e).getValLit());
//             //psfail.push(parents[getTail(e)]->getLit(getHead(e),1));
//             psfail.push(equalities[getTail(e)*nbNodes()+getHead(e)].getValLit()); //not(parent of tl is hd)
//             Clause *expl = Clause_new(psfail);
//             expl->temp_expl = 1;
//             sat.rtrail.last().push(expl);
//             sat.confl = expl;   
//         }
//         return false;
//     }
//     return true;
    
// }

// bool DTreeParenthoodPropagator::propagateRemEdge(int e) {
//     assert(getEdgeVar(e).isFixed());
//     assert(getEdgeVar(e).isFalse());

//     if (!DTreePropagator::propagateRemEdge(e))
//         return false;

//     //If tail of e is the only possible parent of head of e
//     //fail (unless head of e is the root)
//     //Otherwise remove that value and that's it.
//     if (parents[getTail(e)]->indomain(getHead(e))) {
//         if (getHead(e) == getTail(e))
//             return true;
//         Clause* r = NULL;
//         if (so.lazy) {
//             vec<Lit> ps; ps.push();
//             ps.push(getEdgeVar(e).getValLit());
//             r = Reason_new(ps);
//         }
//         parents[getTail(e)]->remVal(getHead(e),r);
//         if(DEBUG) cout <<"This guy "<<getHead(e)<<" cannot have "<<getTail(e)
//                        <<" as a parent, because I removed edge"<<e<<endl; 
//         assert(parents[getTail(e)]->size() > 0);
//         dom_size[getTail(e)] = parents[getTail(e)]->size();
//     }

//     return true;
// }


// bool DTreeParenthoodPropagator::propagateNewParent(int e) {
//     assert(parents[getTail(e)]->getVal() == getHead(e));
//     Clause* r = NULL;
//     if (!getEdgeVar(e).isFixed()) {
//         if (so.lazy) {
//             vec<Lit> ps; ps.push();
//             //ps.push(parents[getTail(e)]->getLit(getHead(e),1));
//             ps.push(equalities[getTail(e)*nbNodes()+getHead(e)].getValLit());
//             r = Reason_new(ps);
//         }
//         getEdgeVar(e).setVal(true,r);
//         new_edge.insert(e);
//         if (!propagateNewEdge(e))
//             return false;
//     } else if (getEdgeVar(e).isFalse()) {
//         if (so.lazy) {
//             vec<Lit> ps;
//             ps.push(getEdgeVar(e).getValLit());
//             ps.push(equalities[getTail(e)*nbNodes()+getHead(e)].getValLit()); //not(parent of tl is hd)
//             Clause *expl = Clause_new(ps);
//             expl->temp_expl = 1;
//             sat.rtrail.last().push(expl);
//             sat.confl = expl;   
//         }
//         return false;
//     }

//     return true;
// }

// bool DTreeParenthoodPropagator::propagateRemParent(int e) {
//     assert(!parents[getTail(e)]->indomain(getHead(e)));
//     Clause* r = NULL;
//     if (!getEdgeVar(e).isFixed()) {
//         if (so.lazy) {
//             vec<Lit> ps; ps.push();
//             ps.push(equalities[getTail(e)*nbNodes()+getHead(e)].getValLit());
//             r = Reason_new(ps);
//         }
//         getEdgeVar(e).setVal(false,r);
//         rem_edge.insert(e);
//     } else if (getEdgeVar(e).isTrue()) {
//         if(so.lazy) {
//             vec<Lit> ps; 
//             ps.push(getEdgeVar(e).getValLit());
//             ps.push(equalities[getTail(e)*nbNodes()+getHead(e)].getValLit()); //not(parent of tl is hd)
//             Clause *expl = Clause_new(ps);
//             expl->temp_expl = 1;
//             sat.rtrail.last().push(expl);
//             sat.confl = expl;   
//         }
//         return false;
//     }

//     return true;
// }

// void DTreeParenthoodPropagator::wakeup(int i, int c) {
//     bool ignore = true;
//     if (first_event <= i && i <= last_event) {
//         int idx = i - first_event; //Corresponding BoolView
//         assert(idx >= 0);
//         assert(idx < nbNodes()*nbNodes());
//         pair<int,int> hd_tl = event2parrel[i]; //head and tail of edge
//         int hd = hd_tl.first;
//         int tl = hd_tl.second;
//         int e = findEdge(hd,tl);
//         //No need to propagate that an edges that does not exist, does not exist
//         //or that I already propagated
//         if (e != -1 && dom_size[hd] != parents[hd]->size()) {
//             assert(equalities[idx].isFixed());
//             if (equalities[idx].isTrue()) {
//                 assert(parents[getTail(e)]->getVal() == getHead(e));
//                 parenthood_fixed.insert(e);
//                 ignore = false;
//             } else if (equalities[idx].isFalse()){
//                 parenthood_abandon.insert(e);
//                 ignore = false;
//             }
//         }
//         if (!ignore)
//             pushInQueue();
//     } else {
//         DTreePropagator::wakeup(i,c);
//     }
// }

// bool DTreeParenthoodPropagator::propagate() {
//     set<int>::iterator it;
//     //*
//     for (it = parenthood_fixed.begin(); it != parenthood_fixed.end(); ++it) {
//         if(!propagateNewParent(*it)){
//             if(DEBUG) cout <<"False "<<__FILE__<<__LINE__<<endl;
//             return false;
//         }
//         dom_size[getHead(*it)] = parents[getHead(*it)]->size();
//         if (last_state_e[*it] != IN) {
//             assert(getEdgeVar(*it).isFixed());
//             assert(getEdgeVar(*it).isTrue());
//             new_edge.insert(*it);
//         }
//     }

//     for (it = parenthood_abandon.begin(); it != parenthood_abandon.end(); ++it) {
//         if(!propagateRemParent(*it)){
//             if(DEBUG) cout <<"False "<<__FILE__<<__LINE__<<endl;
//             return false;
//         }
//         dom_size[getHead(*it)] = parents[getHead(*it)]->size();
//         if (last_state_e[*it] != OUT) {
//             assert(getEdgeVar(*it).isFixed());
//             assert(getEdgeVar(*it).isFalse());
//             rem_edge.insert(*it);
//         }
//     }
//     //*/

//     if (!DTreePropagator::propagate()) {
//         if(DEBUG) cout <<"False "<<__FILE__<<__LINE__<<endl;
//         return false;
//     }

//     return true;
// }

// bool DTreeParenthoodPropagator::checkFinalSatisfied() {
//     if (!DTreePropagator::checkFinalSatisfied())
//         return false;

//     for (int i = 0; i < nbNodes(); i++) {
//         assert(parents[i]->isFixed());
//         if (!parents[i]->isFixed()) {
//             if(DEBUG) {
//                 cout <<parents[0]->size()<<endl;
//                 for(int i = 0; i < nbNodes(); i++){
//                     cout <<" (";
//                     IntVar::const_iterator it = parents[i]->begin();
//                     for ( ; it != parents[i]->end(); it++) {
//                         cout << *it<<",";
//                     }
//                     cout <<") ";
//                 }
//             }
//             assert(false);
//             return false;
//         }
//         int hd = i;
//         int tl = parents[i]->getVal();
//         int e = findEdge(tl,hd);
//         if (hd == get_root_idx()){
//             assert(tl == hd);
//             if (tl != hd)
//                 return false;
//             continue;
//         } else if (getNodeVar(hd).isFalse()) {
//             assert(tl == hd);
//             if (tl != hd)
//                 return false;
//             continue;
//         } else if (e == -1) {
//             assert(e != -1);
//             return false;
//         }
//         assert(getEdgeVar(e).isFixed());
//         if(!getEdgeVar(e).isFixed())
//             return false;
//         assert(getEdgeVar(e).isTrue());
//         if(!getEdgeVar(e).isTrue())
//             return false;
//     }

//     return true;
// }

// void DTreeParenthoodPropagator::clearPropState() {
//     DTreePropagator::clearPropState();
//     parenthood_fixed.clear();
//     parenthood_abandon.clear();
// }


PathDeg1::PathDeg1(vec<BoolView>& _vs, vec<BoolView>& _es, 
                   vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
                   vec< vec<int> >& _en) 
    : GraphPropagator(_vs,_es,_en) {

    for (int i = 0; i < _in.size(); i++) {
        in.push_back(vector<int>() );
        for (int j = 0; j < _in[i].size(); j++) {
            in[i].push_back(_in[i][j]);
        }
    }

    for (int i = 0; i < _out.size(); i++) {
        ou.push_back(vector<int>() );
        for (int j = 0; j < _out[i].size(); j++) {
            ou[i].push_back(_out[i][j]);
        }
    }

    for (int j = 0; j < nbEdges(); j++)
        getEdgeVar(j).attach(this, j,EVENT_LU);
}

void PathDeg1::wakeup(int i, int c) {
    if (getEdgeVar(i).isFixed() && getEdgeVar(i).isTrue()) {
        new_edges.push_back(i);
        pushInQueue();
    }
}

void PathDeg1::clearPropState() {
    GraphPropagator::clearPropState();
    new_edges.clear();
}

bool PathDeg1::propagate() {
    for (unsigned int i = 0; i < new_edges.size(); i++) {
        int e = new_edges[i];
        for (unsigned int j = 0; j < ou[getTail(e)].size(); j++) {
            if (ou[getTail(e)][j] == e) continue;
            if(!getEdgeVar(ou[getTail(e)][j]).isFixed()) {
                Clause* r = NULL;
                if (so.lazy) {
                    vec<Lit> ps; ps.push();
                    ps.push(getEdgeVar(e).getValLit());
                    r = Reason_new(ps);
                }
                getEdgeVar(ou[getTail(e)][j]).setVal(false,r);
            } else if (getEdgeVar(ou[getTail(e)][j]).isTrue()) {
                if(so.lazy) {
                    vec<Lit> ps; 
                    ps.push(getEdgeVar(e).getValLit());
                    ps.push(getEdgeVar(ou[getTail(e)][j]).getValLit());
                    Clause *expl = Clause_new(ps);
                    expl->temp_expl = 1;
                    sat.rtrail.last().push(expl);
                    sat.confl = expl;
                }
                return false;
            }
        }
        for (unsigned int j = 0; j < in[getHead(e)].size(); j++) {
            if (in[getHead(e)][j] == e) continue;
            if(!getEdgeVar(in[getHead(e)][j]).isFixed()) {
                Clause* r = NULL;
                if (so.lazy) {
                    vec<Lit> ps; ps.push();
                    ps.push(getEdgeVar(e).getValLit());
                    r = Reason_new(ps);
                }
                getEdgeVar(in[getHead(e)][j]).setVal(false,r);
            } else if (getEdgeVar(in[getHead(e)][j]).isTrue()) {
                if(so.lazy) {
                    vec<Lit> ps; 
                    ps.push(getEdgeVar(e).getValLit());
                    ps.push(getEdgeVar(in[getHead(e)][j]).getValLit());
                    Clause *expl = Clause_new(ps);
                    expl->temp_expl = 1;
                    sat.rtrail.last().push(expl);
                    sat.confl = expl;
                }
                return false;
            }
        }
    }
    return true;
}




void dtree(int r, vec<BoolView>& _vs, vec<BoolView>& _es,
           vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
           vec< vec<int> >& _en) {
    
    DTreePropagator* dt = new DTreePropagator(r,_vs,_es,_in,_out,_en);
    //if (so.check_prop)
    //    engine.propagators.push(dt);
    //return dt;
}

void reversedtree(int r, vec<BoolView>& _vs, vec<BoolView>& _es,
                  vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
                  vec< vec<int> >& _en) {
    
    vec< vec<int> > endnodes;
    for (int i = 0 ; i < _en.size(); i++) {
        endnodes.push(vec<int>());
        endnodes[i].push(_en[i][1]);
        endnodes[i].push(_en[i][0]);
    }
    DTreePropagator* dt = new DTreePropagator(r,_vs,_es,_out,_in,endnodes);
    //if (so.check_prop)
    //    engine.propagators.push(dt);
    //return dt;
}

void dptree(int r, vec<BoolView>& _vs, vec<BoolView>& _es,
            vec<IntVar*> _par,
            vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
            vec< vec<int> >& _en) {
    
    Propagator* dt = new DTreeParenthoodPropagator(r,_vs,_es,_par,_in,_out,_en);
    //if (so.check_prop)
    //    engine.propagators.push(dt);
}

void reversedptree(int r, vec<BoolView>& _vs, vec<BoolView>& _es,
                   vec<IntVar*> _par,
                   vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
                   vec< vec<int> >& _en) {
    vec< vec<int> > endnodes;
    for (int i = 0 ; i < _en.size(); i++) {
        endnodes.push(vec<int>());
        endnodes[i].push(_en[i][1]);
        endnodes[i].push(_en[i][0]);
    }
    Propagator* dt = new DTreeParenthoodPropagator(r,_vs,_es,_par,_out,_in,endnodes);
    //if (so.check_prop)
    //    engine.propagators.push(dt);
}



//For teh tests against CPBioNet
/*
#include <time.h>      
void path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
              vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
              vec< vec<int> >& _en) {

    srand (time(NULL));


    from = rand() % _vs.size();
    to = rand() % _vs.size();

    for (int j = 0; j < 5; j++) {
        int other = rand() % _vs.size();
        while (_in[other].size() + _out[other].size() <= 10) 
            other = rand() % _vs.size();
        if (_vs[other].setValNotR(true))
            _vs[other].setVal(true,NULL);
    }
    if(false) {
        for ( int i = 0; i < _vs.size(); i++) {
            if (_in[i].size() + _out[i].size() <= 2){
                if (_vs[i].setValNotR(true))
                    _vs[i].setVal(true,NULL);
                continue;
            }
        }
    }
    
    if (_vs[from].setValNotR(true))
        _vs[from].setVal(true,NULL);
    if (_vs[to].setValNotR(true))
        _vs[to].setVal(true,NULL);

    dtree(from,_vs,_es,_in,_out,_en);
    reversedtree(to,_vs,_es,_in,_out,_en);
}
//*/


//*
void path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
              vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
              vec< vec<int> >& _en) {

    if (_vs[from].setValNotR(true))
        _vs[from].setVal(true,NULL);
    if (_vs[to].setValNotR(true))
        _vs[to].setVal(true,NULL);

    //new PathDeg1(_vs,_es,_in,_out,_en);
    //dreachable(from,_vs,_es,_in,_out,_en);
    dtree(from,_vs,_es,_in,_out,_en);
    reversedtree(to,_vs,_es,_in,_out,_en);
}
//*/

#if 0
//Experimental. Needs testing!!!
void pathsucc(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, 
              vec<IntVar*> _par,
              vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out, 
              vec< vec<int> >& _en) {
    assert(false);
    cerr<< "Warning: Do not use the pathsucc constraint"<<endl;
    if (_vs[from].setValNotR(true))
        _vs[from].setVal(true,NULL);
    if (_vs[to].setValNotR(true))
        _vs[to].setVal(true,NULL);
    //dreachable(from,_vs,_es,_in,_out,_en);
    //dtree(from,_vs,_es,_in,_out,_en);
    //reversedptree(to,_vs,_es,_par,_in,_out,_en);
    //reversedtree(to,_vs,_es,_in,_out,_en);
    //dptree(from,_vs,_es,_par,_in,_out,_en);
}
#endif
