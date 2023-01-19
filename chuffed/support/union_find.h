#ifndef UNION_FIND_H
#define UNION_FIND_H


#include <vector>
#include <cstring>
#include <iostream>
#include <chuffed/branching/branching.h>

class UnionFind {
public:
    virtual void reset() = 0;
    virtual int find(int p)  = 0;
    virtual bool unite(int x, int y) = 0;
    virtual bool connected(int x, int y) {
        return find(x) == find(y);
    }
    virtual int getSize() const = 0;
};

template<typename T>
class UF : public UnionFind{
    int const size;
public:

    T* id;
    int getSize() const { return size; }
    UF(int n);
    virtual ~UF();
    void reset();
    int find(int p);
    bool unite(int x, int y);

    void print() const {
        std::cout<<"Unionfind: ";
        for (int i = 0 ; i < size; i++) {
            std::cout<<id[i]<<" ";
        }
        std::cout<<std::endl;
        std::cout<<"           ";
        for (int i = 0 ; i < size; i++) {
            if (id[i] == i)
                std::cout<<"S ";
            else
                std::cout<<"  ";
            int x = id[i];
            while ( x /= 10 )
                std::cout<<" ";
        }
        std::cout<<std::endl;
    }
};

class ExtensibleUF : public UnionFind {
private: 
    std::vector<int> id;
public:

    int getSize() const { return id.size(); }

    void reset() {
        id = std::vector<int>();
    }

    //Created a new node associated to parent
    void push_back(int parent) {
        id.push_back(parent);
        assert(parent < id.size());
    }

    int find(int p)  {
        if (p != id[p])
            id[p] = find(id[p]);
        return id[p];
    }
    bool unite(int x, int y) {
        int i = find(x);
        int j = find(y);
        if (i == j) return false;
        id[j] = i;
        return true;
    }
    
};

template <typename T>
class UFRootInfo : public UF<T> {
    T* is_root;
 public:
    UFRootInfo(int n);
    virtual ~UFRootInfo();
    bool unite(int x, int y);
    bool isRoot(int n);
};

template<typename T>
class RerootedUnionFind : public UnionFind{

 private:
    int const size;
    T* parents;
    T nbCC;

    struct fancyFindInfo{
        int lengthUntilRoot;
        int repr;
    };
    

    struct fancyFindInfo fancyFind(int val) const;
    void makeRoot(int u);
public:

    RerootedUnionFind(int _size);
    ~RerootedUnionFind();
    int getSize() const { return size; }
    //No path compression, otherwise we loose the magic of knowing where
    //explanations come from
    int find(int val) ;
    bool unite(int u, int v);
    void reset();
    int ccCount() const;
    bool isRoot(int i);
    /*
     * This returns a list of NODES (not edges) between two nodes u and v in 
     * the RUF
     */
    std::vector<int> connectionsFromTo(int u, int v) const;
};

template <typename T>
UF<T>::UF(int n) : size(n) {
    id = new T[n];
    for (int i = 0; i < n; i++) {
        id[i] = i;
    }
}

template <typename T>
UF<T>::~UF() {
    delete[] id;
}

template <typename T>
void UF<T>::reset() {
    for (int i = 0; i < size; i++) {
        id[i] = i;
    }
}
template <typename T>
int UF<T>::find(int p)  {
    if (p != id[p])
        id[p] = find(id[p]);
    return id[p];
}
template <typename T>
bool UF<T>::unite(int x, int y)	{
    int i = find(x);
    int j = find(y);
    if (i == j) return false;
    id[j] = i;

    return true;
}

template <typename T>
UFRootInfo<T>::UFRootInfo(int n) :UF<T>(n) {
    this->id = new T[n];
    is_root = new T[n];
    for (int i = 0; i < n; i++) {
        this->id[i] = i;
        is_root[i] = 1;
    }
}

template <typename T>
UFRootInfo<T>::~UFRootInfo() {
    delete[] is_root;
}

template <typename T>
bool UFRootInfo<T>::unite(int x, int y)	{
    int i = this->find(x);
    int j = this->find(y);
    if (i == j) return false;
    this->id[j] = i;
    is_root[j] = 0;

    return true;
}
template <typename T>
bool UFRootInfo<T>::isRoot(int n) {
    return is_root[n];
}



template <typename T>
struct RerootedUnionFind<T>::fancyFindInfo RerootedUnionFind<T>::fancyFind(int val) const {
    assert(val >= 0);
    assert(val < size);
    int i = val;
    int count = 0;
    while (parents[i] != i) {
        i = parents[i];
        count++;
    }
    struct fancyFindInfo v;
    v.lengthUntilRoot = count;
    v.repr = i;
    return v;
}

template <typename T>
void RerootedUnionFind<T>::makeRoot(int u) {
    int i = u;
    int parent = parents[i];
    int last = i;
    while (parent != i) {
        int tmp = parent;
        parent = parents[parent];
        parents[i] = last;
        last = i;
        i = tmp;
    }
    parents[i] = last;
}

template <typename T>
RerootedUnionFind<T>::RerootedUnionFind(int _size) : size(_size), nbCC(_size) {
    parents = new T[size];
    for (int i = 0; i < size; i++) {
        parents[i] = i;
    }
}
template <typename T>
RerootedUnionFind<T>::~RerootedUnionFind() {
    //Cannot delete Tints (should use smart pointers?)
    delete[] parents;
}

//No path compression, otherwise we loose the magic of knowing where
//explanations come from
template <typename T>
int RerootedUnionFind<T>::find(int val) {
    assert(val >= 0);
    assert(val < size);
    int i = val;
    while (parents[i] != i) {
        i = parents[i];
    }
    return i;
}

template <typename T>
bool RerootedUnionFind<T>::unite(int u, int v) {
    if (connected(u,v))
        return false;
    //Walking the first tree to revert it
    makeRoot(u);

    //Walking the second tree to revert it
    // TODO /!\: This can be removed (run all unit-tests again before using
    // it for the paper's results), should still be correct and slightly cheaper
    makeRoot(v); 
    //Merging
    parents[u] = v;
    //One cc less
    nbCC--;
    return true;
}
template <typename T>
void RerootedUnionFind<T>::reset() {
    for (int i = 0; i < size; i++) {
        parents[i] = i;
    }
}

template <typename T>
int RerootedUnionFind<T>::ccCount() const {
    return nbCC;
}
template <typename T>
bool RerootedUnionFind<T>::isRoot(int i) {
    return (parents[i] == i);
}

/*
 * This returns a list of NODES (not edges) between two nodes u and v in the RUF
 */
template <typename T>
std::vector<int> RerootedUnionFind<T>::connectionsFromTo(int u, int v) const {
    std::vector<int> path;
    //struct fancyFindInfo uinfo = fancyFind(u);
    //struct fancyFindInfo vinfo = fancyFind(v);
    //if(uinfo.repr != vinfo.repr)
    //    return path;
    if(u==v)
        return path;
    int i = v;//(uinfo.lengthUntilRoot > vinfo.lengthUntilRoot) ? u : v;
    int limit = (i==u) ? v : u;
      
    int seen[size];
    std::memset(seen, -1, size*sizeof(int));
    while (i != limit && i != parents[i]) { //We stop at the root
        path.push_back(i);
        seen[i] = path.size() -1;
        i = parents[i];
    }
    path.push_back(i);
    seen[i] = path.size() -1;
    //If we got to the root, without seing the other guy, then he is 
    //a sibling, and we have to add his path to the previous explored path
    if(parents[i] == i && i != limit) {
        std::vector<int> path2;
        i = limit;
        while (seen[i] == -1) { //We stop at the root
            path2.push_back(i);
            i = parents[i];
        } 
        //path2.push_back(i);
            
        //Merge paths
        std::vector<int> result;
        /*int i,j;
        for (i = path.size()-1, j = path2.size() -1; i > 0 && j > 0; i--,j--){
            if (path[i] == path2[j] && path[i-1] == path2[j-1]){
                //They havent reached the separation yet
                //i.e. this part of the path is common to both, so we 
                //are not interested in it.
            } else {
                //Separation point
                break;
            }
            }*/
        result.insert(result.begin(), path.begin(), path.begin()+seen[i]+1);
        result.insert(result.end(),path2.rbegin(), path2.rend());
        //for (int k = path2.size()-1; k >=0; k--)
        //    result.push_back(path2[k]);

        assert(result.size() == 0
               || (result[0] == u && result[result.size()-1] == v)
               || (result[0] == v && result[result.size()-1] == u));
               return result;
    } 
    assert(path.size() == 0
           || (path[0] == u && path[path.size()-1] == v)
           || (path[0] == v && path[path.size()-1] == u));
    return path;
}


#endif
