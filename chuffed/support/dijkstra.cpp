#include "dijkstra.h"

#include <map>
#include <iostream>
#include "../support/set_finder.h"



using namespace std;


//The label on each node counts the cost of its duration! (i.e. Duration included)
// i.e. the label on each node says when will you be done with it.


Dijkstra::Dijkstra(int _s, vvi_t _en, vvi_t _in, vvi_t _ou, vector<int>& _ws)
    :source(_s), nb_nodes(_in.size()), en(_en), in(_in), out(_ou), ws(_ws), 
     verbose(false) {
}
Dijkstra::Dijkstra(int _s, vvi_t _en, vvi_t _in, vvi_t _ou, vector<vector<int> >& _wst,
                   std::vector<int> d)
    :source(_s), nb_nodes(_in.size()), en(_en), in(_in), out(_ou), wst(_wst), job(d),
     verbose(false) {
}


void Dijkstra::run() {

    q = std::priority_queue<tuple, std::vector<tuple>, 
                            Dijkstra::Priority>();
    vector<bool> vis = vector<bool>(nb_nodes, false);

    int count = 0;

    pred = vector<int>(nb_nodes, -1);
    has_kids = vector<bool>(nb_nodes, false);
    cost = vector<int>(nb_nodes, -1);    

    pred[source] = source;
    cost[source] = duration(source);
    tuple initial(source,cost[source]);
    q.push(initial);

    if (verbose) cout<<"START"<<endl;

    while (!q.empty() && count < nb_nodes) {

        tuple top = q.top(); q.pop();
        int curr = top.node;

        if (vis[curr]) continue;

        on_visiting_node(curr);
        vis[curr] = true;
        count++;

        if(verbose) cout<<"Visiting "<<curr<<" from "<<pred[curr]<<"(cost: "<<cost[curr]<<")"<<endl;

        for (unsigned int i = 0 ; i < out[curr].size(); i++) {
            int e = out[curr][i];
            assert(en[e][0] == curr);
            if (ignore_edge(e) || weight(e) < 0) {
                if(verbose) cout<<"Ignoring edge "<<e<<" from "<<en[e][0]<<" to "<<en[e][1]<<endl;
                on_ignore_edge(e);
                continue;
            }
            int other = en[e][1]; //Head of e

            if (ignore_node(other)) {
                continue;            
            }    
            if (vis[other]) {
                continue;
            }

            if (cost[other] == -1 
                || cost[other] > cost[curr] + weight(e,cost[curr]) + duration(other)) {
                cost[other] = cost[curr] + weight(e,cost[curr]) + duration(other);
                assert(cost[other] != -1);
                pred[other] = curr;
                has_kids[curr] = true;
                if (verbose) cout <<"Marked "<<other<<" from "<<curr<<" of cost "<<cost[other]<<endl;
                tuple new_node(other, cost[other]);
                enqueue(new_node);
            }             
        }
    }
}


/*
int main(int argc, char* argv[]) {
    int n = 13;
    int e = 21;

    vector< vector<int> > in(n,vector<int>());
    in[0].push_back(11);
    in[1].push_back(2);
    in[1].push_back(14);
    in[2].push_back(1);
    in[3].push_back(0);
    in[4].push_back(13);
    in[4].push_back(15);
    in[5].push_back(12);
    in[5].push_back(17);
    in[6].push_back(3);
    in[7].push_back(4);
    in[8].push_back(16);
    in[8].push_back(19);
    in[9].push_back(5);
    in[9].push_back(6);
    in[9].push_back(8);
    in[9].push_back(10);
    in[10].push_back(7);
    in[11].push_back(9);
    in[11].push_back(20);
    in[12].push_back(18);

    vector< vector<int> > out(n,vector<int>());
    out[0].push_back(0);
    out[0].push_back(1);
    out[0].push_back(2);
    out[1].push_back(15);
    out[2].push_back(12);
    out[2].push_back(14);
    out[2].push_back(13);
    out[3].push_back(3);
    out[3].push_back(4);
    out[4].push_back(18);
    out[5].push_back(16);
    out[6].push_back(5);
    out[7].push_back(6);
    out[7].push_back(7);
    out[8].push_back(17);
    out[8].push_back(20);
    out[9].push_back(9);
    out[10].push_back(8);
    out[11].push_back(10);
    out[11].push_back(11);
    out[12].push_back(19);


    vector< vector<int> > endnodes(e,vector<int>());

    endnodes[0].push_back(0);
    endnodes[0].push_back(3);
    endnodes[1].push_back(0);
    endnodes[1].push_back(2);
    endnodes[2].push_back(0);
    endnodes[2].push_back(1);
    endnodes[3].push_back(3);
    endnodes[3].push_back(6);
    endnodes[4].push_back(3);
    endnodes[4].push_back(7);
    endnodes[5].push_back(6);
    endnodes[5].push_back(9);
    endnodes[6].push_back(7);
    endnodes[6].push_back(9);
    endnodes[7].push_back(7);
    endnodes[7].push_back(10);
    endnodes[8].push_back(10);
    endnodes[8].push_back(9);
    endnodes[9].push_back(9);
    endnodes[9].push_back(11);
    endnodes[10].push_back(11);
    endnodes[10].push_back(9);
    endnodes[11].push_back(11);
    endnodes[11].push_back(0);
    endnodes[12].push_back(2);
    endnodes[12].push_back(5);
    endnodes[13].push_back(2);
    endnodes[13].push_back(4);
    endnodes[14].push_back(2);
    endnodes[14].push_back(1);
    endnodes[15].push_back(1);
    endnodes[15].push_back(4);
    endnodes[16].push_back(5);
    endnodes[16].push_back(8);
    endnodes[17].push_back(8);
    endnodes[17].push_back(5);
    endnodes[18].push_back(4);
    endnodes[18].push_back(12);
    endnodes[19].push_back(12);
    endnodes[19].push_back(8);
    endnodes[20].push_back(8);
    endnodes[20].push_back(11);


    vector<int> ws = vector<int>(e,-1);
    for (int i = 0; i < e; i++)
        ws[i] = (i*7+4)%9+1;

    cout <<"Weights: ";
    for (int i = 0; i < e; i++)
        cout << ws[i] <<" ";
    cout <<endl;

    Dijkstra d(0,endnodes,in,out,ws);
    d.run();


    for (int i = 0; i < n; i++)
        cout << i <<"("<<d.distTo(i)<<","<<d.parentOf(i)<<") ";
    cout <<endl;

}
//*/




vector<int> DijkstraMandatory::DEFAULT_VECTOR;
DijkstraMandatory::DijkstraMandatory(int _s, int _d, 
                                     vvi_t _en, vvi_t _in, vvi_t _ou, 
                                     vector<int> _ws)
    :source(_s), dest(_d), nb_nodes(_in.size()), en(_en), in(_in), out(_ou), 
     ws(_ws), sccs(new FilteredKosarajuSCC(this,nb_nodes,out,in,en)),
     clustering(NULL) {

#ifdef DIJKSTRAMANDATORY_ALLOW_CYCLE
    //Extra edge from dest to source of cost 0
    out[dest].push_back(en.size());
    in[source].push_back(en.size());
    en.push_back(vector<int>());
    en[en.size()-1].push_back(dest);
    en[en.size()-1].push_back(source);
    ws.push_back(0);

#endif

}
DijkstraMandatory::DijkstraMandatory(int _s, int _d, 
                                     vvi_t _en, vvi_t _in, vvi_t _ou, 
                                     vector<vector<int> > _wst, vector<int> _ds)
    :source(_s), dest(_d), nb_nodes(_in.size()), en(_en), in(_in), out(_ou), 
     wst(_wst), job(_ds), sccs(new FilteredKosarajuSCC(this,nb_nodes,out,in,en)),
     clustering(NULL) {
}


void DijkstraMandatory::init() {
#ifdef SCC_REASONING
    sccs->run();
    sccs->set_levels(source,dest);
#endif
}

#ifdef DIJKSTRAMANDATORY_ALLOW_CYCLE
int DijkstraMandatory::run(bool* ok, bool use_set_target, int start) {
#else
int DijkstraMandatory::run(bool* ok, bool use_set_target) {
#endif

#ifdef DIJKSTRAMANDATORY_ALLOW_CYCLE
    vector<int>& mands = mandatory_nodes();
    int val = -1;
    if (mands.size() == 0) {
        val = source;
    } else {
        val = mands[rand()%mands.size()];
    }
    if (start != -1)
        val = start;
    int source = val;
    fake_start_point = source;

    int dest = source;
#endif

    int nb_sccs = 1;
    (void)nb_sccs; //Avoid -Wunused

#if defined (INCREMENTAL_SCC_REASONING) && defined(BASIC_EXPL)
    sccs->run();
    sccs->set_levels(source,dest);
    nb_sccs = sccs->nb_sccs();
#endif


    //vector<SetFinder<BITSET_SIZE> > tries = 
    //    vector<SetFinder<BITSET_SIZE> >(nb_nodes, SetFinder<BITSET_SIZE>());
    
#if BITSET_SIZE > 50
    table = vector<boost::unordered_map<size_t,tuple> >(nb_nodes, boost::unordered_map<size_t,tuple>());
#else
    table = vector<boost::unordered_map<ulong,tuple> >(nb_nodes, boost::unordered_map<ulong,tuple>());
#endif

    if (!use_set_target) { //Create the target bitset here


        target.reset();
        vector<int>& mands = mandatory_nodes();

#ifdef CLUSTERING
        // Cluster mands if only one SCC
        // or cluster the mandatory nodes in each SCC 
        if (mands.size() > clustering->nb_clusters()) {
            if (nb_sccs == 1) {
                clustering->update_dists();
                vector<int> centroids = clustering->cluster(mands);
                for (unsigned int i = 0; i < centroids.size(); i++) {
                    target[centroids[i]] = 1;
                }                

            } else {
                bool updated = false;
                for (int s = 0; s < nb_sccs; s++) {
                    vector<int> scc = sccs->get_scc(s);
                    vector<int> local_mands;
                    for (unsigned int i = 0; i < scc.size(); i++) {
                        int n = scc[i];
                        if (mandatory_node(n)) {
                            local_mands.push_back(n);
                        }
                    }
                    if (local_mands.size() > clustering->nb_clusters()) {
                        //Cluster with local_mands
                        //Get centroid of each cluster and set 1 in target
                        if (!updated) {
                            clustering->update_dists();
                            updated = true;
                        }
                        vector<int> centroids = clustering->cluster(local_mands);
                        for (unsigned int i = 0; i < centroids.size(); i++) {
                            target[centroids[i]] = 1;
                        }
                    } else {
                        for (unsigned int i = 0; i < local_mands.size(); i++) {
                            target[local_mands[i]] = 1;
                        }
                    }
                }
            }

            } else 
#endif
        {
            //Normal case, less mandatories than clusters
            for (unsigned int i = 0; i < mands.size(); i++) {
                target[mands[i]] = 1;
            }
        }
    }

    target[source] = 1;
    target[dest] = 1;
#ifdef SCC_REASONING
    vector<std::bitset<BITSET_SIZE> > target_sccs 
        = vector<std::bitset<BITSET_SIZE> >(nb_nodes+1,std::bitset<BITSET_SIZE>());
    for (int i = 0; i < nb_nodes; i++) {
        target_sccs[sccs->level_of_scc(sccs->scc_of(i))][i] = target[i]; 
    }

#endif

    //Initialize Queue:
    std::bitset<BITSET_SIZE> pathS; pathS[source] = 1;
    std::bitset<BITSET_SIZE> mandS; mandS[source] = 1;
    tuple initial(source,duration(source), pathS,mandS);
    table[source][hash_fn(mandS)] = initial;
    //tries[source].add(mandS,duration(source));

    q = boost::heap::priority_queue<tuple, boost::heap::compare<DijkstraMandatory::Priority> >();
    //q = std::priority_queue<tuple, std::vector<tuple>, 
    //                        DijkstraMandatory::Priority>();
    q.push(initial);

    int minToDest = -1;
    while (!q.empty()) {
        top = q.top(); q.pop();
        int curr = top.node;
        table_iterator it;
        if (table[curr][hash_fn(top.mand)].cost < top.cost) {
            continue;
        }
        //table_iterator it = table[curr].find(hash_fn(top.mand));
        //if (it == table[curr].end() ||
        //    (it->second).cost < top.cost) {
        //    continue;
        //}

        //if(stop_at_node(curr))
        //    continue;
        for (unsigned int i = 0 ; i < out[curr].size(); i++) {
            int e = out[curr][i];
            assert(en[e][0] == curr);
            int other = en[e][1]; //Head of e

#ifdef DIJKSTRAMANDATORY_ALLOW_CYCLE
            if (e != en.size()-1) {
#endif
                if (ignore_edge(e) || weight(e) < 0) {
                    continue;
                }
#ifdef DIJKSTRAMANDATORY_ALLOW_CYCLE
            }
#endif
            if (ignore_node(other) || other == curr) {
                continue;            
            }    
#ifdef SCC_REASONING      
            //Check if different SCCs. If so, don't cross unless
            //you already saw the entire SCC of the head.
            if (sccs->scc_of(curr) != sccs->scc_of(other)) {
                int fr = sccs->level_of_scc(sccs->scc_of(curr));
                int to = sccs->level_of_scc(sccs->scc_of(other));
                if (abs(to - fr) > 1) {
                    // You are skipping some mandatory node that you won't 
                    // be able to get back at
                    continue; 
                }
                if (to == fr + 1) { 
                    // Make sure you are done with all the mandatory nodes
                    // at your level before going to the next level.
                    if ((top.mand & target_sccs[fr]) != target_sccs[fr]) {
                        continue;
                    }   
                }
            }
#endif

            

            bool _enqueue = true;
            bool was_mand_other = top.mand[other];
            if (target[other])
                top.mand[other] = 1;
            it = table[other].find(hash_fn(top.mand));
            if (it != table[other].end() && (it->second).cost >= 0){ 
                if ((it->second).cost <= top.cost + weight(e,top.cost) + duration(other)) {
                    _enqueue = false;
                } 
            }

            
            /*//TODO! Find cheapest superset in sfs[other], if cheaper than me, dont enqueu
            vector<std::bitset<BITSET_SIZE> > supersets;
            vector<int > costs;
            if (_enqueue) {
                tries[other].supersets(top.mand,supersets,costs);
                if (supersets.size() > 0) {
                    int min_cost = costs[0];
                    for (unsigned int i = 0; i < supersets.size(); i++) {
                        if (min_cost > costs[i]) {
                            min_cost = costs[i];
                        }
                    }
                    if (min_cost <= top.cost + weight(e,top.cost) + duration(other)) {
                        _enqueue = false;
                    }
                }
            }//*/

            top.mand[other] = was_mand_other;
            if (_enqueue) {
                tuple copy = top;
                if (target[other]) { //Other is mandatory
                    copy.mand[other] = 1;
                }
                copy.cost += weight(e,top.cost) + duration(other);
                copy.path[other] = 1;
                copy.node = other;
                /*//TODO !Find all subsets in sfs[other]. If more expensive, mark them -1 on the table
                // to not explore them. Remove them from sfs[other].
                vector<std::bitset<BITSET_SIZE> > subsets;
                costs.clear();
                tries[other].subsets(top.mand,subsets,costs,true, copy.cost);
                if (subsets.size() > 0) {
                    for (unsigned int i = 0; i < subsets.size(); i++) {
                        if (costs[i] > top.cost + weight(e,top.cost) + duration(other)) {
                            table[other].erase(hash_fn(subsets[i]));
                        }
                    }
                }
                tries[other].add(copy.mand,copy.cost);//*/
                table[other][hash_fn(copy.mand)] = copy;
                if (other != dest && other != source) {
                    enqueue(copy);//q.push(copy);
                } else if (other == dest){
                    if (copy.mand == target && (copy.cost < minToDest || minToDest ==-1)) {
                        minToDest = copy.cost;
                    }
                }
            }
        }
    }

    //cout<<endl;

    if (minToDest >= 0) {
        if(ok != NULL) 
            *ok = true;
        //cout<<target<<" Min: "<<minToDest<<" ("<<engine.decisionLevel()<<")"<<endl;
        return minToDest;
    } else {  
        if(ok != NULL) 
            *ok = false;
        int max = -1;
        
        for (table_iterator it = table[dest].begin(); it != table[dest].end(); ++it) {
            if ((it->second).cost > max)
                max = (it->second).cost;
        }
        //cout<<target<<" Max: "<<max<<endl;
        return max;
    }

    
}



void Dijkstra::print_pred() const {
    for (unsigned int i = 0; i < pred.size(); i++)
        std::cout<< pred[i]<<" ";
    std::cout<<std::endl;
}
