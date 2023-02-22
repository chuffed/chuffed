#ifndef DIJKSTRA_H
#define DIJKSTRA_H
#include <iostream>
#include <vector>
#include <queue> 
#include <map> 
#include <bitset>
#include <functional> //For std::hash
#include <chuffed/core/propagator.h> //For Tint
#include <cassert>
#include <chuffed/support/kosaraju_scc.h>
#include <chuffed/support/dynamic_kmeans.h>


class Dijkstra  {
protected:
    typedef std::vector< std::vector <int> > vvi_t; 
    int source;
    int nb_nodes;
    vvi_t en;
    vvi_t in;
    vvi_t out;
private:
    std::vector<int> pred;
    std::vector<bool> has_kids;
    std::vector<int> cost;
    std::vector<int> ws;
    std::vector<std::vector<int> > wst;
    std::vector<int> job;
public:
    bool verbose;
    struct tuple {
        tuple() : node(-1),cost(0) {}
        tuple(int _node,int _cost): node(_node), cost(_cost) {assert(cost>=0);}
        int node;
        int cost;
    };
    typedef struct Dijkstra::tuple tuple;
    class Priority {
    public:
        bool operator() (const tuple& lhs, const tuple&rhs) const {
            return lhs.cost > rhs.cost;
        }
    };
private:

    std::priority_queue<tuple, std::vector<tuple>, 
                        Dijkstra::Priority> q;
public:
    Dijkstra(int _s,vvi_t _en, vvi_t _in, vvi_t _ou,
             std::vector<int>& _ws);
    Dijkstra(int _s,vvi_t _en, vvi_t _in, vvi_t _ou,
             std::vector<std::vector<int> >& _wst, std::vector<int> d = std::vector<int>());
    virtual ~Dijkstra() {};
    void run();

    virtual void set_source(int s) {source = s;}
    inline int parentOf(int n) {return pred[n];}
    inline int distTo(int n) {return cost[n];}
    inline int isInShortestPath(int tl, int hd) {return pred[hd] == tl;}

    virtual void on_visiting_node(int n) { }
    virtual bool ignore_edge(int e) {return false;}
    virtual void on_ignore_edge(int e) { }
    virtual bool ignore_node(int n) {return false;}
    virtual void enqueue(tuple node) { q.push(node); }
    void set_verbose(bool v) {verbose = v;}
    void print_pred() const;
    bool is_leaf(int n) const {return !has_kids[n];}
    inline virtual int weight(int e, unsigned int time = -1) {
        if (ws.size()) {
            return ws[e];
        } else if (wst.size()) {
            return time >= 0 && time < wst[e].size() ? wst[e][time] : -1;
        } else {
            std::cerr<< "Error "<<__FILE__<<__LINE__<<std::endl;
            return -1;
        }
    }
    inline virtual int duration(int n) {
        return job.size()? job[n] : 0;
    }
};


#include <bitset>


// Needs to be the numbr of nodes in the graph. 
#define BITSET_SIZE 21
// Use new SCC knowledge at each iteration to skip edges. This only
// works with basic explanations.
//#define INCREMENTAL_SCC_REASONING
// Use SCC kowledges ad the root to skip edges.
//#define SCC_REASONING
// Use clustering
//#define CLUSTERING
// Allow starting anywhere
//#define DIJKSTRAMANDATORY_ALLOW_CYCLE

class DijkstraMandatory  {
    
public:
    typedef std::vector< std::vector <int> > vvi_t;
protected:
    int source;
    int dest;
    int nb_nodes;

    
    vvi_t en;
    vvi_t in;
    vvi_t out;

    std::vector<int> pred;
    std::vector<int> cost;


    std::vector<int> ws;
    std::vector< std::vector<int> > wst;
    std::vector<int> job;

public:
    struct tuple {
        tuple() : node(-1), cost(-1){
        }
        tuple(int _node,int _cost, std::bitset<BITSET_SIZE> _path, std::bitset<BITSET_SIZE> _mand)
            : node(_node), cost(_cost), path(_path), mand(_mand) {
            assert(cost>=0);
        }
        int node;
        int cost;
        std::bitset<BITSET_SIZE> path;
        std::bitset<BITSET_SIZE> mand;
    };
    typedef DijkstraMandatory::tuple tuple;

    class Priority {
    public:
        bool operator() (const DijkstraMandatory::tuple& lhs, 
                         const DijkstraMandatory::tuple& rhs) const {
            return lhs.cost > rhs.cost;
        }
    };

private:
    tuple top;
    class FilteredKosarajuSCC : public KosarajuSCC {
        DijkstraMandatory* d;
    public:
        FilteredKosarajuSCC(DijkstraMandatory* _d,
                            int v, std::vector< std::vector<int> > outgoing,
                            std::vector< std::vector<int> > ingoing,
                            std::vector< std::vector<int> > ends) 
            : KosarajuSCC(v,outgoing,ingoing,ends), d(_d){}
        virtual bool ignore_edge(int e) {
            return d->ignore_edge_scc(e);
        }
        virtual bool ignore_node(int u) {
            return d->ignore_node_scc(u);
        }
        virtual bool mandatory_node(int u) {
            return d->mandatory_node(u);
        }

    };
    FilteredKosarajuSCC* sccs;


protected:
    std::bitset<BITSET_SIZE> target;
    inline tuple& current_iteration() {return top;}
    std::priority_queue<tuple, std::vector<tuple>, 
                       DijkstraMandatory::Priority> q;
public:
#if BITSET_SIZE > 50
    std::vector< std::unordered_map<size_t,tuple> > table;
    typedef std::unordered_map<size_t,tuple> map_type;
    static std::hash<std::bitset<BITSET_SIZE> > hash_fn;
    typedef std::unordered_map<size_t,tuple>::const_iterator table_iterator;
#else
    typedef unsigned long ulong;
    std::vector< std::unordered_map<ulong,tuple> > table;
    typedef std::unordered_map<ulong,tuple> map_type;
    static inline ulong hash_fn(std::bitset<BITSET_SIZE>& b) {return b.to_ulong();}
    typedef std::unordered_map<ulong,tuple>::const_iterator table_iterator;
#endif
    typedef std::vector< map_type > table_type;



    DijkstraMandatory(int _s, int _d, vvi_t _en, vvi_t _in, vvi_t _ou,
                      std::vector<int> _ws);
    DijkstraMandatory(int _s, int _d, vvi_t _en, vvi_t _in, vvi_t _ou,
                      std::vector<std::vector<int> > _wst, 
                      std::vector<int> _ds = std::vector<int>());
    virtual void init();
    virtual ~DijkstraMandatory() {};

#ifdef DIJKSTRAMANDATORY_ALLOW_CYCLE
    virtual int run(bool* ok = NULL, bool use_set_target = false, int start = -1);
    int fake_start_point;
    virtual int get_start_point() {return fake_start_point;}
#else
    virtual int run(bool* ok = NULL, bool use_set_target = false);
#endif


    virtual bool ignore_edge(int e) {return false;}
    virtual bool ignore_node(int n) {return false;}
    virtual bool ignore_edge_scc(int e) {return false;}
    virtual bool ignore_node_scc(int n) {return false;}
    virtual void enqueue(tuple node) { q.push(node); }
    virtual bool stop_at_node(int n) {return false;}
    virtual bool mandatory_node(int n) {return false;}
    virtual bool mandatory_edge(int e) {return false;} 
    static std::vector<int> DEFAULT_VECTOR;
    virtual std::vector<int>& mandatory_nodes() {return DijkstraMandatory::DEFAULT_VECTOR;}
    inline virtual int weight(int e, int time = -1) {
        if (ws.size()) {
            return ws[e];
        } else if (wst.size()) {
            return time >= 0 && time < (int)wst[e].size() ? wst[e][time] : -1;
        } else {
            std::cerr<< "Error "<<__FILE__<<__LINE__<<std::endl;
            return -1;
        }
        
    }
    inline virtual int duration(int n) {
        return job.size()? job[n] : 0;
    }

    inline void set_target(std::vector<int> tar) { 
        target.reset();
        for (unsigned int i = 0; i < tar.size(); i++)
            target[tar[i]] = 1;
    }
    inline void set_target(std::vector<bool> tar) { 
        target.reset();
        for (unsigned int i = 0; i < tar.size(); i++)
            target[i] = tar[i];
    }
    inline void set_target(std::bitset<BITSET_SIZE> tar) { target = tar; }
    inline std::bitset<BITSET_SIZE> get_target() { return target; }


    //Clustering features
protected:
    ClusteringAlgorithm<Tint>* clustering;
public:
    void set_clustering(ClusteringAlgorithm<Tint>* c) {clustering = c;};
    //virtual std::vector<int> cluster(std::vector<int> v) {return v;};
    //virtual unsigned int nb_clusters() const {return clusters_count;}
    //virtual void set_nb_clusters(int v) {clusters_count = v;}

};


#endif
