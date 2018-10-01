#ifndef SET_FINDER_H
#define SET_FINDER_H

#include <stddef.h>
#include <bitset>
#include <vector>
#include <iostream>

template<unsigned int N>
class SetFinder {
    
    enum Type {ZERO, ONE, ROOT};
    int _nb_terminals;
    class TrieNode {
    public: 
        SetFinder* sf;
        bool terminal;
        int val;
        Type type;
        TrieNode* zero;
        TrieNode* one;
        TrieNode(SetFinder* sf,Type t, bool term = false)
            : sf(sf), terminal(term), val(-1),type(t), zero(NULL), one(NULL){
            if (terminal)
                sf->_nb_terminals++;
        }
        ~TrieNode() {
            if (terminal)
                sf->_nb_terminals--;
            if (zero != NULL)
                delete zero;
            zero = NULL;
            if (one != NULL)
                delete one;
            one = NULL;
        }
    };
    
    TrieNode root;


    void _add(std::bitset<N> key, int val, TrieNode* n, int level) {
        if (n->terminal) {
            n->val = val;
            return;
        }
        if (level >= N)
            return;
        int bit = key[level];
        if (bit == 0) {
            if (n->zero == NULL) {
                n->zero = new TrieNode(this,ZERO, level == N - 1);
            }
            _add(key,val,n->zero,level+1);
        } else {
            if (n->one == NULL) {
                n->one = new TrieNode(this,ONE, level == N - 1);
            }
            _add(key,val,n->one,level+1);
        }
    }

    int _find(std::bitset<N> key, bool* ok, TrieNode* n, int level) {
        if (n->terminal) {
            *ok = true;
            return n->val;
        }
        if (level >= N) {
            *ok =false;
            return -1;
        }
        int bit = key[level];
        if (bit == 0) {
            if (n->zero != NULL) {
                _find(key, ok, n->zero, level+1);
            } else {
                *ok = false;
                return -1;
            }
        } else if (bit == 1) {
            if (n->one != NULL) {
                _find(key, ok, n->one, level+1);
            } else {
                *ok = false;
                return -1;
            }
        }
    }

    bool _subsets(std::bitset<N> key, std::vector<std::bitset<N> >& ss, 
                  std::vector<int>& vals, 
                  TrieNode* n, int level,
                  std::bitset<N> chain,
                  bool remove = false, int threshold = -1) {
        if (level > N)
            return false;
        if (n->type == ONE && level > 0) chain[level - 1] = 1;
        else if (n->type == ZERO && level > 0)  chain[level - 1] = 0;

        if (n->terminal) {
            int last_bit = key[N-1];
            if (last_bit == 1 || (last_bit == 0 && n->type == ZERO)) {
                ss.push_back(chain);
                vals.push_back(n->val);
                if (remove) {
                    if (threshold < n->val) {
                        return true;
                    } else {
                        return false;
                    }
                }
            }
            return false;
        }
        int bit = key[level];
        bool rem = false;
        //If bit == 1, explore both sides, so always explore 0
        if (n->zero != NULL) {
            rem = _subsets(key, ss, vals, n->zero, level+1, chain,remove, threshold);
            if (remove && rem) {
                delete n->zero;
                n->zero = NULL;
                if (n->one != NULL)
                    rem = false;
            }
        }
        if (bit == 1 && n->one != NULL) {
            rem = _subsets(key, ss, vals, n->one, level+1, chain,remove, threshold);
            if (remove && rem) {
                delete n->one;
                n->one = NULL;
                if (n->zero != NULL)
                    rem = false;
            }
        }

        return rem;
    }


    bool _supersets(std::bitset<N> key, std::vector<std::bitset<N> >& ss, 
                    std::vector<int>& vals, 
                    TrieNode* n, int level,
                    std::bitset<N> chain,
                    bool remove = false, int threshold = -1) {
        if (level > N)
            return false;
        if (n->type == ONE && level > 0) chain[level - 1] = 1;
        else if (n->type == ZERO && level > 0)  chain[level - 1] = 0;

        if (n->terminal) {
            int last_bit = key[N-1];
            if (last_bit == 0 || (last_bit == 1 && n->type == ONE)) {
                ss.push_back(chain);
                vals.push_back(n->val);
                if (remove) {
                    if (threshold < n->val) {
                        return true;
                    } else {
                        return false;
                    }
                }
            }
            return false;
        }
        int bit = key[level];
        bool rem = false;
        //If bit == 1, explore both sides, so always explore 0
        if (n->one != NULL) {
            rem = _supersets(key, ss, vals, n->one, level+1, chain,remove, threshold);
            if (remove && rem) {
                delete n->one;
                n->one = NULL;
                if (n->zero != NULL)
                    rem = false;
            }
        }
        if (bit == 0 && n->zero != NULL) {
            rem = _supersets(key, ss, vals, n->zero, level+1, chain,remove, threshold);
            if (remove && rem) {
                delete n->zero;
                n->zero = NULL;
                if (n->one != NULL)
                    rem = false;
            }
        }

        return rem;

    }


public:
    SetFinder() : _nb_terminals(0), root (this,ROOT) { }
    
    void add(std::bitset<N> key, int val) {
        _add(key,val, &root, 0);
    }


    int find(std::bitset<N> key, bool* ok) {
        return _find(key, ok, &root, 0);
    }

    void subsets(std::bitset<N> key, std::vector<std::bitset<N> >& ss, 
                 std::vector<int>& vals, bool remove = false, int threshold = -1) {
        _subsets(key, ss, vals, &root, 0, std::bitset<N>(), remove, threshold);
    }

    void supersets(std::bitset<N> key, std::vector<std::bitset<N> >& ss, 
                   std::vector<int>& vals, bool remove = false, int threshold = -1) {
        _supersets(key, ss, vals, &root, 0, std::bitset<N>(), remove, threshold);
    }

    inline int nb_terminals() {return _nb_terminals;}

    void print(TrieNode* n = NULL, std::string s = "-") {
        if (n == NULL) {
            std::cout<< "R"<<std::endl;
            n = &root;
        } else if (n->type == ONE)
            std::cout<<s<< "1"<<"("<<n->val<<")"<<std::endl;
        else if (n->type == ZERO)
            std::cout<<s<< "0"<<"("<<n->val<<")"<<std::endl;
        if (n->one != NULL)
            print(n->one, s+"-");
        if (n->zero != NULL)
            print(n->zero, s+"-");

    }

};




#endif
