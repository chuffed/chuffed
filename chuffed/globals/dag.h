#ifndef DAGPROPAGATOR_H
#define DAGPROPAGATOR_H

#include "dconnected.h"
#include "support/trailed_cst_list.h"

class DAGPropagator : public DReachabilityPropagator {

    class TrailedSuccList : public TrailedConstantAccessList<std::pair<int,int> > {
    public:
        TrailedSuccList(int n) : TrailedConstantAccessList(n){}
        virtual int key(std::pair<int,int> p) {
            return p.first;
        }
        void print() {
            std::cout <<"Size: "<<size<<std::endl;;
            std::cout <<"Sparse: ";
            for (int i = 0; i < sparse.size(); i++) {
                std::cout <<sparse[i]<<" ";
            }
            std::cout<<std::endl;
            
            std::cout <<"Dense: ";
            for (int i = 0; i < dense.size(); i++) {
                std::cout <<"("<<dense[i].first<<","<<dense[i].second<<") ";
            }
            std::cout<<std::endl;
        }
    };
    class TrailedPredList : public TrailedConstantAccessList<int> {
    public:
        TrailedPredList(int n) : TrailedConstantAccessList(n){}
        virtual int key(int p) {
            return p;
        }
        void print() {
            std::cout <<"Size: "<<size<<std::endl;;
            std::cout <<"Sparse: ";
            for (int i = 0; i < sparse.size(); i++) {
                std::cout <<sparse[i]<<" ";
            }
            std::cout<<std::endl;
            
            std::cout <<"Dense: ";
            for (int i = 0; i < dense.size(); i++) {
                std::cout <<dense[i]<<" ";
            }
            std::cout<<std::endl;
        }
    };


    std::vector<TrailedSuccList> succs;
    std::vector<TrailedPredList> preds;


    Tint** reachability;
    void connectTo(int source, int dest);
    inline bool reachable(int source, int dest) {
        return (source == dest || succs[source].get(dest));
        /*if (source == dest)
            return true;
        if (!((reachability[source][dest]>0 && succs[source].get(dest)) ||
              (!reachability[source][dest]>0 && !succs[source].get(dest)))) {
            std::cout <<"Succs of "<<source<<":"<<std::endl;
            succs[source].print();
            std::cout <<source <<" "<<dest<<std::endl;
            assert(false);
        }
        return reachability[source][dest] > 0;*/
        //        return reachability[source][dest/sizeof(int)] 
        //            & (1 << sizeof(int) - (dest % sizeof(int)));
    }

    std::vector<bool> processed_e;
    std::vector<bool> processed_n;



    void findPathFromTo(int u, int v, vec<Lit>& path);


    bool check_correctness(int r,std::vector<int>& v);
public:
    DAGPropagator(int _r, vec<BoolView>& _vs, vec<BoolView>& _es, 
                  vec< vec<edge_id> >& _in, vec< vec<edge_id> >& _out,
                  vec< vec<int> >& _en);

    ~DAGPropagator();

    virtual bool propagateNewEdge(int e);
    virtual bool propagateNewNode(int n);

    virtual bool check_cycle(int e);
    virtual bool prevent_cycle(int e);

    virtual bool propagate();

    virtual bool checkFinalSatisfied();

};

#endif
