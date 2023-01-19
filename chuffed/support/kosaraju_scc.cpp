#include <cstring>
#include <iostream>

#include <chuffed/support/kosaraju_scc.h>
using namespace std;
 
KosarajuSCC::KosarajuSCC(int v, vector< vector<int> > out,
                         vector< vector<int> > in,
                         vector< vector<int> > en) 
    : nb_nodes(v), outgoing(out), ingoing(in), ends(en),scc(nb_nodes,-1) {
}

// A recursive function to print DFS starting from v
void KosarajuSCC::DFS(int v, bool visited[], int curr) {
    // Mark the current node as visited and print it
    visited[v] = true;
    scc[v] = curr;
    sccs[curr].push_back(v);
    // Recur for all the vertices adjacent to this vertex
    for(unsigned int i = 0; i < ingoing[v].size(); ++i) {
        int e = ingoing[v][i];
        if (ignore_edge(e))
            continue;
        int u = ends[e][0];
        if (ignore_node(u))
            continue;
        if(!visited[u])
            DFS(u, visited, curr);
    }
}
 
void KosarajuSCC::fillOrder(int v, bool visited[], stack<int> &s) {
    // Mark the current node as visited and print it
    visited[v] = true;
    // Recur for all the vertices adjacent to this vertex
    for(unsigned int i = 0; i < outgoing[v].size(); ++i) {
        int e = outgoing[v][i];
        if (ignore_edge(e))
            continue;
        int u = ends[e][1];
        if (ignore_node(u))
            continue;
        if(!visited[u]) {
            fillOrder(u, visited, s);
        }
    }
 
    // All vertices reachable from v are processed by now, push v 
    s.push(v);
}
 
// The main function that finds and prints all strongly connected 
// components
void KosarajuSCC::run() {
    scc = vector<int>(nb_nodes,-1);
    sccs.clear();
    stack<int> s;
 
    // Mark all the vertices as not visited (For first DFS)
    bool *visited = new bool[nb_nodes];
    memset(visited,false , nb_nodes*sizeof(bool));
    // Fill vertices in stack according to their finishing times
    for(int i = 0; i < nb_nodes; i++) {
        if(visited[i] == false && !ignore_node(i)) {
            fillOrder(i, visited, s);
        }
    }

    // Mark all the vertices as not visited (For second DFS)
    memset(visited,false , nb_nodes*sizeof(bool));
 
    // Now process all vertices in order defined by Stack
    int curr = 0;
    while (!s.empty())
    {
        // Pop a vertex from stack
        int v = s.top();
        s.pop();
 
        // Print Strongly connected component of the popped vertex
        if (visited[v] == false)
        {
            sccs.push_back(vector<int>());
            DFS(v, visited,curr);
            curr++;
        }
    }
    delete[] visited;
}


void KosarajuSCC::__set_levels(int start, int sink) {
    int start_scc = scc_of(start);
    std::stack<int> s;
    s.push(start);
            
    std::vector< std::vector<int> > scc_graph_out
        = std::vector< std::vector<int> >(nb_sccs(), std::vector<int>());
    std::vector< std::vector<int> > scc_graph_ends;
    is_mand = std::vector<bool>(nb_sccs(), false);
    std::vector<bool> seen = std::vector<bool>(nb_nodes, false);
    std::vector< std::vector<int> > matrix = 
        std::vector< std::vector<int> >(nb_sccs(), std::vector<int>(nb_sccs(),0) );

    level2mandscc = boost::unordered_map<int,int>();
    mandscc2somenode = boost::unordered_map<int,int>();
    int edges = 0;
    int mand_sccs = 0;
    while (!s.empty()) {
        int u = s.top();
        seen[u] = true;
        s.pop();
        if (mandatory_node(u) && !is_mand[scc_of(u)]) {
            is_mand[scc_of(u)] = true;
            mandscc2somenode[scc_of(u)] = u;
            mand_sccs++;            
        }
        for(unsigned int i = 0; i < outgoing[u].size(); ++i) {
            int e = outgoing[u][i];
            int v = ends[e][1];
            if (ignore_edge(e) || ignore_node(v)){
                continue;
            }
            if (scc_of(u) != scc_of(v) && matrix[scc_of(u)][scc_of(v)] == 0) {
                scc_graph_out[scc_of(u)].push_back(edges);
                scc_graph_ends.push_back(std::vector<int>());
                scc_graph_ends.back().push_back(scc_of(u));
                scc_graph_ends.back().push_back(scc_of(v));
                edges++;
                matrix[scc_of(u)][scc_of(v)] = 1;
            }
            if (!seen[v])
                s.push(v);
        }
    }
    /*std::cout<<"\n";
      std::cout<<"SCC GRAPH"<<std::endl;
      for (int i = 0; i < scc_graph_out.size(); i++) {
      for (int j = 0; j < scc_graph_out[i].size(); j++) {
      std::cout<<scc_graph_out[i][j]<<"(to "
      <<scc_graph_ends[scc_graph_out[i][j]][1]<<") ";
      }
      std::cout<<std::endl;
      }
      std::cout<<std::endl;
      std::cout<<"MANDS ";
      for (int i = 0; i < nb_sccs(); i++) {
      std::cout<<is_mand[i]<<" ";
      }
      std::cout<<std::endl;
      //*/
    std::queue<int> topo;
    seen = std::vector<bool>(nb_sccs(), false);
    topological_sort(start_scc, scc_graph_out, scc_graph_ends, topo,seen);
            
    levels = std::vector<int>(nb_sccs(),nb_sccs()+10);
    levels[scc_of(sink)] = mand_sccs;

    while (!topo.empty()) {
        int u = topo.front();
        topo.pop();
        int min = nb_sccs()+10;
        //std::cout<<"Looking at "<<u<<std::endl;
        for(unsigned int i = 0; i < scc_graph_out[u].size(); ++i) {
            int e = scc_graph_out[u][i];
            int v = scc_graph_ends[e][1];
            min = (min < levels[v]) ? min : levels[v];
        }
        levels[u] = (min < levels[u]) ? min : levels[u];
        if (is_mand[u]) {
            levels[u] -= 1;
            level2mandscc[levels[u]] = u;
        }
    }
    /*std::cout<<"LEVELS: "<<mand_sccs<<"     ";
      for (int i = 0; i < nb_sccs(); i++)
      std::cout<<levels[i]<<" ";
      std::cout<<std::endl;
    */


}

void KosarajuSCC::topological_sort(int u, std::vector< std::vector<int> >& out,
                      std::vector< std::vector<int> >& ends,
                      std::queue<int>& sort,
                      std::vector<bool>& seen) {
    seen[u] = true;
    for(unsigned int i = 0; i < out[u].size(); ++i) {
        int e = out[u][i];
        int v = ends[e][1];
        if (!seen[v])
            topological_sort(v,out,ends,sort,seen);
    }                
    sort.push(u);
}

void KosarajuSCC::_set_levels(int u, bool vis[], 
                 boost::unordered_map<int,bool>& mscc,
                 int parent,
                 std::string des){
    // std::cout<<des;
    // for (int i = 0; i < nb_sccs(); i++)
    //      std::cout<<levels[i]<<" ";
    //  std::cout<<std::endl;
    if (vis[u])
        return;
    vis[u] = true;
    int my_scc = scc_of(u);
    //std::cout<<des<<"Looking at " <<u<<std::endl;
    for(unsigned int i = 0; i < outgoing[u].size(); ++i) {
        int e = outgoing[u][i];
        if (ignore_edge(e))
            continue;
        int v = ends[e][1];
        if (ignore_node(v))
            continue;
        if (v == parent)
            continue;

        if (!vis[v])
            _set_levels(v,vis,mscc,u,des+"  ");

        if (my_scc != scc_of(v)) {
            //std::cout<<des<<"!=SCCS "<<u<<" "<<v<<std::endl;
            if (levels[scc_of(v)] <= levels[my_scc]) {
                //std::cout<<des<<"levels < "<<u<<" "<<v<<std::endl;
                bool is_mand = false;
                boost::unordered_map<int,bool>::const_iterator it 
                    = mscc.find(my_scc);
                if (it == mscc.end()) { 
                    std::vector<int> scc = get_scc(my_scc);
                    for (unsigned int i = 0; i < scc.size(); i++) {
                        if(mandatory_node(scc[i])) {
                            is_mand = true;
                            break;
                        }
                    }
                    mscc[my_scc] = is_mand;
                } else {
                    is_mand = it->second;
                }
                levels[my_scc] = levels[scc_of(v)] - 1*is_mand;
                // std::cout<<des;
                // for (int i = 0; i < nb_sccs(); i++)
                //      std::cout<<levels[i]<<" ";
                //  std::cout<<std::endl;
            }
        }
    }            
}

void KosarajuSCC::set_levels(int start, int sink) {
    levels.clear();
    levels = std::vector<int>(nb_sccs(),nb_nodes+1);
    //bool *visited = new bool[nb_nodes];
    //memset(visited,false , nb_nodes*sizeof(bool));


    boost::unordered_map<int,bool> mand_sccs;
    //levels[scc_of(sink)] = nb_nodes;
    //_set_levels(start,visited,mand_sccs);
    __set_levels(start,sink);
    //delete[] visited;
}



/* 
// Driver program to test above functions
#include <iostream>
int main()
{


    vector< vector<int> > in (5, vector<int>());
    in[0].push_back(0);
    in[1].push_back(2);
    in[2].push_back(1);
    in[3].push_back(3);
    in[4].push_back(4);
    vector< vector<int> > out (5, vector<int>());
    out[0].push_back(1);
    out[0].push_back(3);
    out[1].push_back(0);
    out[2].push_back(2);
    out[3].push_back(4);

    vector< vector<int> > ends (5, vector<int>());
    ends[0].push_back(1);
    ends[0].push_back(0);
    ends[1].push_back(0);
    ends[1].push_back(2);
    ends[2].push_back(2);
    ends[2].push_back(1);
    ends[3].push_back(0);
    ends[3].push_back(3);
    ends[4].push_back(3);
    ends[4].push_back(4);

    KosarajuSCC g(5,out,in,ends);
    g.run();

    for (int i = 0; i < 5; i++)
        cout<< g.scc_of(i)<<endl;
    
    cout<<"    "<<g.nb_sccs()<<endl;

    for (int i = 0; i < g.nb_sccs(); i++) {
        for (int j = 0; j < g.get_scc(i).size(); j++) {
            cout << g.get_scc(i)[j]<<" ";
        }
        cout<<endl;
    }


    return 0;
}
//*/
