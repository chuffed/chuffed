#ifndef FLOYDWARSHALL_H
#define FLOYDWARSHALL_H

template <typename T>
class FloydWarshall{

private:
    int n;
    int e;
    T** dist;
    T** inf;
public:
    FloydWarshall(int _n, int _e) : n(_n),e(_e),dist(NULL), inf(NULL) {
        dist = new T*[n];
        inf  = new T*[n];
        for (int i = 0; i < n; i++) {
            dist[i] = new T[n];
            inf[i]  = new T[n];
            for (int j = 0; j < n; j++) {
                dist[i][j] = 0;
                inf[i][j] = (i != j); //is infinite
            }
        }
    }
    
    virtual ~FloydWarshall() {
        if(dist != NULL) {
            for (int i = 0; i < n; i++) 
                delete[] dist[i];
            delete[] dist;
        }
        if(inf != NULL) {
            for (int i = 0; i < n; i++) 
                delete[] inf[i];
            delete[] inf;
        }
    }

    virtual int from(int edge_id) = 0;
    virtual int to(int edge_id) = 0;
    virtual int exists(int edge_id) = 0;
    virtual int weight(int edge_id) = 0;

    void compute() {
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                dist[i][j] = 0;
                inf[i][j] = (i != j); //is infinite
            }
        }


        for (int i = 0; i < n; i++)
            dist[i][i] = 0;

        for (int edge = 0; edge < e; edge++) {

            if (exists(edge)) {
                dist[from(edge)][to(edge)] = weight(edge);
                inf[from(edge)][to(edge)] = 0;
                dist[to(edge)][from(edge)] = weight(edge);
                inf[to(edge)][from(edge)] = 0;
            }
        } 



        /*std::cout<<"INIT"<<std::endl;
        for (int i = 0; i < n; i++) {
            for(int j = 0; j < n; j++) {
                assert(dist[i][j] == dist[j][i]);
                if (dist[i][j]>= 10000)//inf[i][j]) 
                    std::cout<<". ";
                else
                    std::cout<<dist[i][j]<<" ";
            }
            std::cout<<std::endl;
        }
        */
        for (int k = 0; k < n; k++) {
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    if ((inf[i][j] || dist[i][j] > dist[i][k] + dist[k][j]) 
                        && !inf[i][k] && !inf[k][j]) {
                        dist[i][j] = dist[i][k] + dist[k][j];
                        inf[i][j] = 0;
                    }
                }
            }
        }
        /*
        for (int i = 0; i < n; i++) {
            for(int j = 0; j < n; j++) {
                assert(dist[i][j] == dist[j][i]);
                if (dist[i][j]>= 10000)//inf[i][j]) 
                    std::cout<<". ";
                else
                    std::cout<<dist[i][j]<<" ";
            }
            std::cout<<std::endl;
        }
        */
    }

    T getDist(int i, int j, int* infinite) {
        //*infinite = dist[i][j] >= 10000;
        *infinite = inf[i][j];
        return dist[i][j];
    }

};


#endif
