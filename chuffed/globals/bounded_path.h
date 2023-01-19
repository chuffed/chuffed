#ifndef BOUNDED_PATH_H
#define BOUNDED_PATH_H

#include <chuffed/globals/graph.h>
#include <chuffed/support/union_find.h>
#include <chuffed/support/lengauer_tarjan.h>
#include <map>
#include <iostream>
#include <set>
#include <stack>
#include <queue>
#include <vector>

#include <chuffed/support/dijkstra.h>
#include <chuffed/support/dynamic_kmeans.h>

class ShortestPathSearch;

class BoundedPathPropagator : public GraphPropagator{

    friend ShortestPathSearch;

    class FilteredKosarajuSCC : public KosarajuSCC {
        BoundedPathPropagator* pp;
    public:
        FilteredKosarajuSCC(BoundedPathPropagator* _pp,
                            int v, std::vector< std::vector<int> > outgoing,
                            std::vector< std::vector<int> > ingoing,
                            std::vector< std::vector<int> > ends) 
            : KosarajuSCC(v,outgoing,ingoing,ends), pp(_pp){}
        virtual bool ignore_edge(int e) {
            if (pp->getEdgeVar(e).isFixed() && pp->getEdgeVar(e).isFalse())
                return true;
            return false;
        }
        virtual bool ignore_node(int u) {
            if (pp->getNodeVar(u).isFixed() && pp->getNodeVar(u).isFalse())
                return true;
            return false;
        }
        virtual bool mandatory_node(int u) {
            return pp->getNodeVar(u).isFixed() && pp->getNodeVar(u).isTrue();
        }
    };
    FilteredKosarajuSCC* kosaraju;

    class FilteredDijkstra : public Dijkstra {
    protected:
        BoundedPathPropagator* p;
    public:
        FilteredDijkstra(BoundedPathPropagator* _btp, int _s,
                         std::vector< std::vector<int> > _en, 
                         std::vector< std::vector<int> > _in, 
                         std::vector< std::vector<int> > _ou,
                         std::vector<int>& _ws)
            : Dijkstra(_s,_en,_in,_ou,_ws), p(_btp) {}
        FilteredDijkstra(BoundedPathPropagator* _btp, int _s,
                         std::vector< std::vector<int> > _en, 
                         std::vector< std::vector<int> > _in, 
                         std::vector< std::vector<int> > _ou,
                         std::vector<std::vector<int> >& _ws)
            : Dijkstra(_s,_en,_in,_ou,_ws), p(_btp) {}
        virtual bool ignore_edge(int e) {
            if (p->getEdgeVar(e).isFixed() && p->getEdgeVar(e).isFalse())
                    return true;
            return false;
        }

        virtual bool ignore_node(int u) {
            if (p->getNodeVar(u).isFixed() && p->getNodeVar(u).isFalse())
                return true;
            return false;
        }
        virtual void enqueue(Dijkstra::tuple node) {
            if (node.node != p->dest && node.node != p->source && node.node != source)
                Dijkstra::enqueue(node);
        }
        
    };
    FilteredDijkstra* forward_sp;
    FilteredDijkstra* backward_sp;
    std::vector<int> initial_dist_from_dest;
    FilteredDijkstra* backward_sp_tmp; //This one is used when the source changes

    class ExplainerDijkstra : public FilteredDijkstra {
        std::vector<edge_id> explanation;
        std::vector<Lit> lits;
        int lim;
        FilteredDijkstra* back;
        int explaining;
    public:
        ExplainerDijkstra(BoundedPathPropagator* _btp, int _s,
                          std::vector< std::vector<int> > _en, 
                          std::vector< std::vector<int> > _in, 
                          std::vector< std::vector<int> > _ou,
                          std::vector<int>& _ws) 
            : FilteredDijkstra(_btp,_s,_en,_in,_ou,_ws), back(NULL),
              explaining(-1) {}
        ExplainerDijkstra(BoundedPathPropagator* _btp, int _s,
                          std::vector< std::vector<int> > _en, 
                          std::vector< std::vector<int> > _in, 
                          std::vector< std::vector<int> > _ou,
                          std::vector<std::vector<int> >& _ws) 
            : FilteredDijkstra(_btp,_s,_en,_in,_ou,_ws), back(NULL),
              explaining(-1) {}
        bool debug;
        void reset(int limit, FilteredDijkstra* _back, int ex = -1) {
            explanation.clear();
            lim = limit;
            back = _back;
            explaining = ex;
            debug= false;
        }
        void reset(int limit, FilteredDijkstra* _back, std::vector<Lit> _lits, int ex = -1) {
            explanation.clear();
            lits = _lits;
            lim = limit;
            back = _back;
            explaining = ex;
            debug= false;
        }
        std::vector<edge_id>& getExpl() {return explanation;}
        std::vector<Lit> getLits() {return lits;}
        void debug_toggle() {
            debug = !debug;
        }       
        void set_explaining(int ex) {
            explaining = ex;
        }
        virtual bool ignore_node(int n) {return false;}
        virtual bool ignore_edge(int e) {
            if (p->getEdgeVar(e).isFixed() && p->getEdgeVar(e).isFalse()) {
                if(verbose)std::cout<<">>Looking at: "<<p->getTail(e) <<" to "<<p->getHead(e)<<std::endl; 

                //Useless edges to be in the explanation:
                if (p->getHead(e) == p->source) 
                    return true;
                if (p->getTail(e) == p->dest)
                    return true;

                int d_hd = back->distTo(p->getHead(e)); //Includes time spent in hd
                if (d_hd == -1) { 
                    return false;  //Can cros the ones that are unreachable from the other end.
                }

                int d_tl = this->distTo(p->getTail(e)); //inlcudes time spent in tl
                int w_e = weight(e);
                if (w_e < 0 || p->isSelfLoop(e)) { 
                    return true; 
                }

                if (d_tl + w_e + d_hd <= lim) {
                    if (distTo(p->getHead(e)) != -1 && 
                        d_tl + w_e >= distTo(p->getHead(e))) //Not needed in expl.
                        return true;
                    //explanation.push_back(e);
                    lits.push_back(p->getEdgeVar(e).getValLit());
                    return true;
                }   
            }
            return false;
        }

        virtual void enqueue(Dijkstra::tuple node) {
            if (node.node != p->dest && node.node != p->source && node.node != source && node.node != explaining)
                FilteredDijkstra::enqueue(node);
        }
        
    };
    ExplainerDijkstra* explain_sp;
    ExplainerDijkstra* bexplain_sp;

    class FilteredDijkstraMandatory : public DijkstraMandatory {
    protected:
        BoundedPathPropagator* p;
    public:
        FilteredDijkstraMandatory(BoundedPathPropagator* _btp, int _s, int _d,
                                  std::vector< std::vector<int> > _en, 
                                  std::vector< std::vector<int> > _in, 
                                  std::vector< std::vector<int> > _ou,
                                  std::vector<int>& _ws)
            : DijkstraMandatory(_s,_d,_en,_in,_ou,_ws), p(_btp) {}
        FilteredDijkstraMandatory(BoundedPathPropagator* _btp, int _s, int _d,
                                  std::vector< std::vector<int> > _en, 
                                  std::vector< std::vector<int> > _in, 
                                  std::vector< std::vector<int> > _ou,
                                  std::vector<std::vector<int> >& _ws)
            : DijkstraMandatory(_s,_d,_en,_in,_ou,_ws), p(_btp) {}

        virtual bool ignore_node(int n) {
            if (p->getNodeVar(n).isFixed() && p->getNodeVar(n).isFalse())
                return true;
            return false;
        }

        virtual bool ignore_edge(int e) {
            if (p->getEdgeVar(e).isFixed() && p->getEdgeVar(e).isFalse())
                return true;
            return false;
        }

        virtual bool mandatory_node(int u) {
            if (p->getNodeVar(u).isFixed() && p->getNodeVar(u).isTrue())
                return true;
            return false;
        }
        virtual bool mandatory_edge(int e) {
            if (p->getEdgeVar(e).isFixed() && p->getEdgeVar(e).isTrue())
                return true;
            return false;
        }
        virtual std::vector<int>& mandatory_nodes() {
            return p->in_nodes_list;
        }
        virtual bool ignore_node_scc(int u) {
#ifdef BASIC_EXPL
            return ignore_node(u);
#else
            return false;
#endif
        }
        virtual bool ignore_edge_scc(int e) {
#ifdef BASIC_EXPL
            return ignore_edge(e);
#else
            return false;
#endif
        }

    };
    FilteredDijkstraMandatory* mandatory_sp;
    FilteredDijkstraMandatory* initial_mandatory_sp;


    class ExplainerDijkstraMandatory : public FilteredDijkstraMandatory {
        std::vector<edge_id> explanation;
        std::vector<Lit> lits;
        int lim;
        double time_limit;
        double start_time;
        FilteredDijkstraMandatory* back;
    public:
        ExplainerDijkstraMandatory(BoundedPathPropagator* _btp, 
                                   int _s, int _d,
                                   std::vector< std::vector<int> > _en, 
                                   std::vector< std::vector<int> > _in, 
                                   std::vector< std::vector<int> > _ou,
                                   std::vector<int>& _ws) 
            : FilteredDijkstraMandatory(_btp,_s,_d,_en,_in,_ou,_ws), back(NULL) {}
        ExplainerDijkstraMandatory(BoundedPathPropagator* _btp, 
                                   int _s, int _d,
                                   std::vector< std::vector<int> > _en, 
                                   std::vector< std::vector<int> > _in, 
                                   std::vector< std::vector<int> > _ou,
                                   std::vector<std::vector<int> >& _ws) 
            : FilteredDijkstraMandatory(_btp,_s,_d,_en,_in,_ou,_ws), back(NULL) {}

        void reset(int limit, FilteredDijkstraMandatory* _back, double time_lim = 1.0) {
            explanation.clear();
            lits.clear();
            lim = limit;
            back = _back;
            start_time = wallClockTime();
            time_limit = time_lim;
        }
        std::vector<edge_id>& getExpl() {return explanation;}

        virtual bool ignore_node_scc(int u) {
            //if (p->getNodeVar(u).isFixed() && p->getNodeVar(u).isFalse())
            //        return true;
            return false;
        }
        virtual bool ignore_edge_scc(int e) {
            //if (p->getEdgeVar(e).isFixed() && p->getEdgeVar(e).isFalse())
            //        return true;
            return false;
        }

        virtual bool ignore_node(int n) { return false; }
        virtual bool stop_at_node(int n) { 
            tuple& current = current_iteration();
            int here = current.node;
            int cost_to_here = current.cost;

            if (p->initial_dist_from_dest[here] + cost_to_here >= lim) {
                return true;                
            }

            DijkstraMandatory::table_iterator it;
            it = p->initial_mandatory_sp->table[here].begin();

            for ( ; it != p->initial_mandatory_sp->table[here].end(); ++it) {
                if ((current.mand | (it->second).mand) == target) { //Union
                    int d = (it->second).cost;
                    if (d + cost_to_here > lim) {
                        return true;
                    }
                }
            }
            return false;
        }
        virtual bool ignore_edge(int e) {
            tuple& current = current_iteration();
            if (p->getEdgeVar(e).isFixed() && p->getEdgeVar(e).isFalse()) {
                //Useless edges to be in the explanation:
                if (p->getHead(e) == p->source) 
                    return true;
                if (p->getTail(e) == p->dest)
                    return true;
                int d_tl = current.cost; //includes time spent in tl
                if (weight(e) < 0 || p->isSelfLoop(e)) { 
                    return true; 
                }

                // This is for robustness, if the explanations takes too long
                // kill it by adding all edges in the explanation and build
                // a frontier.
                double time_spent = wallClockTime() - start_time;
                if (time_limit > 0 && time_limit <= time_spent) {
                    if (p->was_shortest[e]) {
                        //explanation.push_back(e);
                        lits.push_back(p->getEdgeVar(e).getValLit());
                        return true;
                    }
                }


                assert(current.node == p->getTail(e));
                int hd = p->getHead(e);

                DijkstraMandatory::table_iterator it = back->table[hd].begin();
                for ( ; it != back->table[hd].end(); ++it) {
                    if ((current.mand | (it->second).mand) == target) { //Union
                        int d_hd = (it->second).cost; //inlcudes time spent in hd
                        int w_e = weight(e);

                        if (d_tl + w_e + d_hd <= lim) {
                            if (table[hd].count(hash_fn(current.mand)) > 0) {
                                if (table[hd][hash_fn(current.mand)].cost <= current.cost + weight(e)) {
                                    return true;
                                } 
                            }
                            //explanation.push_back(e);
                            lits.push_back(p->getEdgeVar(e).getValLit());
                            return true;
                        }   
                    }
                }
                
            }
            return false;
        }
        std::vector<Lit>& getLits() {return lits;}
    };
    ExplainerDijkstraMandatory* mandatory_explainer_sp;



    class ImplementedDynamicKMeans : public DynamicKMeans<Tint> {
        BoundedPathPropagator* _bpp;
    public:
        ImplementedDynamicKMeans(int k, int n, int e,
                                 BoundedPathPropagator* bpp)
            : DynamicKMeans(k,n,e), _bpp(bpp) {
        }

        virtual inline int from(int edge_id) { return _bpp->getTail(edge_id); }
        virtual inline int to(int edge_id) { return _bpp->getHead(edge_id); }
        virtual inline int available_edge(int edge_id) { 
            return !_bpp->getEdgeVar(edge_id).isFixed() || _bpp->getEdgeVar(edge_id).isTrue();
        }
        virtual inline int weight(int edge_id) {
            return (_bpp->getEdgeVar(edge_id).isFixed() && _bpp->getEdgeVar(edge_id).isTrue())? 
                0 : _bpp->getAverageWeight(edge_id);
        }        
    };
    ImplementedDynamicKMeans* dkm;


    int source;
    int dest;

    IntVar* w;

    Tint explanation_tsize;
    int explanation_size;
    vec<Lit> fail_expl;
    vec<Lit> prop_expl;

    Tint in_nodes_tsize;
    int  in_nodes_size;
    std::vector<int> in_nodes_list;
    Tint* last_state_n;


    std::vector<int> new_edges;

    std::vector<std::vector<int> > nodes2edge;
    
    void addToExplanation(int e);
    void update_explanation();
    void update_innodes();

    void computeReason(Clause*& r);
    bool falseOrFail(int e, Clause*& r);
protected:


    enum VType{IN, OUT, UNK};
    Tint* last_state_e;

    std::set<int> rem_edge;

    std::vector< std::vector<edge_id> > in;
    std::vector< std::vector<edge_id> > ou;
    vec<int> ws;
    vec<vec<int> > wst;
    
    Tint* was_shortest;
    
    virtual bool propagate_dijkstra();
    bool propagate_scc_order();
    bool _check_expl(std::vector<int> forbidden, int limit, int at, bool reverse = false) {
        //std::cout << "Forbidden:"<<std::endl;
        std::vector<bool> is_forbidden = std::vector<bool>(nbEdges(), false);
        for (unsigned int i = 0; i < forbidden.size(); i++) {            
            is_forbidden[forbidden[i]] = true;
            //std::cout <<"("<<getTail(forbidden[i])<<","<<getHead(forbidden[i])<<",w"<<ws[forbidden[i]]<<")"<<std::endl;
        }
        

        std::priority_queue<Dijkstra::tuple, std::vector<Dijkstra::tuple>, 
                            Dijkstra::Priority> q;
        std::vector<bool> vis = std::vector<bool>(nbNodes(), false);
        int count = 0;
        std::vector<int> pred = std::vector<int>(nbNodes(), -1);
        std::vector<int> cost = std::vector<int>(nbNodes(), -1);    

        if (!reverse) {
            pred[source] = source;
            cost[source] = 0;
            Dijkstra::tuple initial(source,0);
            q.push(initial);
        } else {
            pred[dest] = dest;
            cost[dest] = 0;
            Dijkstra::tuple initial(dest,0);
            q.push(initial);
        }

        while (!q.empty() && count < nbNodes()) {
            Dijkstra::tuple top = q.top(); q.pop();
            int curr = top.node;
            if (vis[curr])
                continue;
            vis[curr] = true;
            count++;
            
            std::vector<int> in_or_out = ou[curr];
            if (reverse) {
                in_or_out = in[curr];
            }
            
            for (unsigned int i = 0 ; i < in_or_out.size(); i++) {
                int e = in_or_out[i];
                int other;
                if (!reverse) other= getHead(e); 
                else other= getTail(e);
                if (vis[other] || ws[e] < 0 || isSelfLoop(e) || is_forbidden[e]) {
                    continue;
                }
                if (cost[other] == -1 
                    || cost[other] > cost[curr] + ws[e]) {
                    cost[other] = cost[curr] + ws[e];
                    assert(cost[other] != -1);
                    pred[other] = curr;
                    Dijkstra::tuple new_node(other, cost[other]);
                    if (reverse && other == source)
                        continue;
                    if (!reverse && other == dest)
                        continue;
                    q.push(new_node);
                }             
            }
        }
        /*std::cout<< "at: "<< at<<std::endl;
        std::cout<< cost[at]<<" "<<limit<<std::endl;
        int p = at;
        while (p != pred[p] && pred[p] != -1) {
            std::cout << p<< " ";
            p = pred[p];
        }
        std::cout << p<< std::endl;
        std::cout <<"Preds ";
        for (int i = 0; i < pred.size(); i++) {
            std::cout << pred[i]<<" ";
        }
        std::cout<<std::endl;
        //*/
        if(cost[at] == -1)
            return false;//assert(cost[at] != -1);
        return (cost[at] > limit);// || (cost[at] == -1);
    }


    bool check_expl(std::vector<int> forbidden, int limit, int at, bool reverse = false) {
        //std::cout <<"Checking correct ("<<forbidden.size()<<",lim:"<<limit<<"):"<<std::endl;
        //std::cout<< "Forbidden ("<<forbidden.size()<<"):";
        for (unsigned int i = 0; i < forbidden.size(); i++) {
            //std::cout<< forbidden[i]<<"("<<getTail(forbidden[i])<<","<<getHead(forbidden[i])<<") ";
            assert(!isSelfLoop(forbidden[i]) && ws[forbidden[i]] >= 0);
        }
        //std::cout<<std::endl;
        bool ok = _check_expl(forbidden,limit,at,reverse);
        if (!ok) {
            std::cout <<"Not correct"<<std::endl;
            return false;
        }
        //std::cout<< "Checking minimal:"<<std::endl;
        if (forbidden.size() > 0) {
            for (unsigned int i = 0; i < forbidden.size(); i++) {
                std::vector<int> tmp;
                for (unsigned int j = 0; j < forbidden.size(); j++) {
                    if (i == j) continue;
                    tmp.push_back(forbidden[j]);
                }
                //assert(!_check_expl(tmp,limit,at,reverse));
                if(_check_expl(tmp,limit,at,reverse)) {
                    std::cout<<getTail(forbidden[i]) <<" "<< getHead(forbidden[i])<<std::endl;
                    std::cout<<forbidden[i]<< " "<<ws[forbidden[i]]<<std::endl;
                    return false;
                }
            }
        }

        return true;
    }

    bool _check_expl_mand(std::vector<int> forbidden, int limit) {
        std::vector<boost::unordered_map<size_t,DijkstraMandatory::tuple> > table;

        std::vector<bool> is_forbidden = std::vector<bool>(nbEdges(), false);
        for (unsigned int i = 0; i < forbidden.size(); i++) {            
            is_forbidden[forbidden[i]] = true;
        }
        

        std::vector<bool> vis = std::vector<bool>(nbNodes(), false);
        std::vector<int> pred = std::vector<int>(nbNodes(), -1);
        std::vector<int> cost = std::vector<int>(nbNodes(), -1);    

        table.clear();
        for (int i = 0; i < nbNodes(); i++){
            table.push_back(boost::unordered_map<size_t,DijkstraMandatory::tuple>());
        }
        std::bitset<BITSET_SIZE> target;
        for (int i = 0; i < nbNodes(); i++) {
            target[i] = getNodeVar(i).isFixed() && getNodeVar(i).isTrue();
        }
        //Initialize Queue:
        std::bitset<BITSET_SIZE> pathS; pathS[source] = 1;
        std::bitset<BITSET_SIZE> mandS; mandS[source] = 1;
        DijkstraMandatory::tuple initial(source,0, pathS,mandS);
        table[source][DijkstraMandatory::hash_fn(mandS)/*.to_ulong()*/] = initial;

        std::priority_queue<DijkstraMandatory::tuple, 
                            std::vector<DijkstraMandatory::tuple>, 
                            DijkstraMandatory::Priority> q;

        q.push(initial);


        int minToDest = -1;
        //int maxToDest = -1;

        while (!q.empty()) {
            DijkstraMandatory::tuple top = q.top(); q.pop();
            int curr = top.node;
            if (table[curr][DijkstraMandatory::hash_fn(top.mand)/*.to_ulong()*/].cost < top.cost) {
                continue;
            }

            for (unsigned int i = 0 ; i < ou[curr].size(); i++) {
                int e = ou[curr][i];
                assert(getTail(e) == curr);
                int other = getHead(e); //Head of e
                if (is_forbidden[e] || ws[e] < 0) {
                    continue;
                }
                bool enqueue = true;
                bool was_mand_other = top.mand[other];
                if (target[other])
                    top.mand[other] = 1;
                boost::unordered_map<size_t,DijkstraMandatory::tuple>::const_iterator it 
                    = table[other].find(DijkstraMandatory::hash_fn(top.mand)/*.to_ulong()*/);
                if (it != table[other].end()){
                    if ((it->second).cost <= top.cost + ws[e]) {
                        enqueue = false;
                    } 
                }
                top.mand[other] = was_mand_other;
                if (enqueue) {
                    DijkstraMandatory::tuple copy = top;
                    if (target[other]) { //Other is mandatory
                        copy.mand[other] = 1;
                    }
                    copy.cost += ws[e];
                    copy.path[other] = 1;
                    copy.node = other;
                    table[other][DijkstraMandatory::hash_fn(copy.mand)/*.to_ulong()*/] = copy;              
                    //if (other == 10)
                    //    std::cout<<"Adding from "<< curr<<" to table of "<<other<<" "<<copy.path<<" "<<copy.mand<<" "<<copy.cost<<"  we:"<<ws[e]<<std::endl;
                    if (other != dest && other != source) {
                        q.push(copy);
                    } else if (other == dest){
                        if (copy.mand == target && (copy.cost < minToDest || minToDest ==-1)) {
                            minToDest = copy.cost;
                        }
                    }
                }
            }
        }

        if (minToDest >= 0) {
            //*
            if (! (minToDest > limit) ){ 
                for (int i = 0; i < nbNodes(); i++) {
                    if (getNodeVar(i).isFixed() && getNodeVar(i).isTrue())
                        std::cout<< i<<" [color=red];"<<std::endl;
                }
                int ct = 0;
                for (int i = 0; i < nbEdges(); i++) {
                    if (!getEdgeVar(i).isFixed()){
                        std::cout <<" "<<getTail(i)<<"->"<<getHead(i)
                                  <<"[label="<<ws[i]<<"];"<<std::endl;
                        ct++;
                    }
                    if (getEdgeVar(i).isTrue()){
                        std::cout <<" "<<getTail(i)<<"->"<<getHead(i)
                                  <<"[label="<<ws[i]<<",color=red];"<<std::endl;
                        ct++;
                    }
                }
                std::cout<<"Checked explanation::"<<std::endl;
                std::cout<<ct<<std::endl;
                std::cout<<target<<std::endl;
                std::cout<< minToDest<<" "<<limit<<std::endl;
                boost::unordered_map<size_t,DijkstraMandatory::tuple>::const_iterator it = table[dest].begin();
                for ( ; it != table[dest].end(); ++it) {
                    std::cout << (it->second).node <<" "
                              << (it->second).path<< " "
                              << (it->second).mand <<" " 
                              << (it->second).cost<<std::endl;
                }   
                std::cout<<"::"<<std::endl;
            }
            //*/

            return minToDest > limit;
        }
        return true;
    }


protected:
    void constructGraph(vec< vec<edge_id> >& _in, 
                        vec< vec<edge_id> >& _out,
                        vec< vec<int> >& _en);
    void constructWeights(vec<int>& _ws, IntVar* _w);
    void constructWeights(vec< vec<int> >& _ws, IntVar* _w);
    void constructBasicExplanations();
    void rootLevelPropagation();


public:


    BoundedPathPropagator(int _s, int _d, vec<BoolView>& _vs, vec<BoolView>& _es,
                          vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
                          vec< vec<int> >& _en, vec<int>& ws, IntVar* w);
    BoundedPathPropagator(int _s, int _d, vec<BoolView>& _vs, vec<BoolView>& _es,
                          vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
                          vec< vec<int> >& _en, vec< vec<int> >& ws, IntVar* w);
    virtual ~BoundedPathPropagator();
    virtual void wakeup(int i, int c);
    virtual bool propagate();
    virtual void clearPropState();
    
    virtual bool checkFinalSatisfied();

    inline virtual int getAverageWeight(int edge_id) {
        //If variable weight, compute average //No...
        return ws[edge_id];
    }
};



#endif
