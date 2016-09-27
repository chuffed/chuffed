#ifndef __CFG_H__
#define __CFG_H__
#include <cassert>
#include <iostream>

namespace CFG {

class ProdR {
public:
  virtual ~ProdR() {};
  virtual bool check(int start, int end) = 0; 
};

class Span : public ProdR {
public:
  Span(int _low, int _high)
    : low(_low), high(_high)
  { }
  
  bool check(int start, int end)
  {
    int span(end - start);
    return low <= span && span <= high;
  }
protected:
  int low;
  int high;
};

class Start : public ProdR {
public:
  Start(int _low, int _high)
    : low(_low), high(_high)
  { }
  
  bool check(int start, int end)
  {
    return low <= start && start <= high;
  }
protected:
  int low;
  int high;
};

class SpanLB : public ProdR {
public:
  SpanLB(int _low)
    : low(_low)
  { }
  
  bool check(int start, int end)
  {
    int span(end - start);
    return low <= span;
  }
protected:
  int low;
};

class LB : public ProdR {
public:
  LB(int _lb)
    : lb(_lb)
  { }
  bool check(int start, int end) { return lb <= start; }
protected:
  int lb;
};

class ProdInfo {
public:
  ProdInfo(ProdR* _cond, int _rule)
    : cond(_cond), rule(_rule)
  { } 

  ProdR* cond;
  int rule;
};

struct Sym {
  int x;

  friend Sym mkTerm(int id);
  friend Sym mkVar(int id);
  
  bool operator == (Sym p) const { return x == p.x; }
  bool operator != (Sym p) const { return x != p.x; }
  bool operator < (Sym p) const  { return x < p.x; }
};

inline Sym mkTerm(int id) { Sym p; p.x = (id<<1); return p; }
inline Sym mkVar(int id)  { Sym p; p.x = (id<<1) + 1; return p; }
inline int symID(Sym p)   { return p.x>>1; }
inline bool isVar(Sym p)  { return p.x&1; }

class RSym {
public:
  RSym()
    : sym(mkTerm(0)), cond(NULL)
  { }
  RSym(int i)
    : sym(mkTerm(i)), cond(NULL)
  { }
  RSym(const Sym& _s)
    : sym(_s), cond(NULL)
  { }
  RSym(int i, ProdR* _p)
    : sym(mkTerm(i)), cond(_p)
  { }
  RSym(const Sym& _s, ProdR* _p)
    : sym(_s), cond(_p)
  { }

  Sym sym;
  ProdR* cond;
};

class Cond
{
public:
  Cond(ProdR* _p)
    : p(_p)
  { }
  
  RSym operator() (const Sym& s) {
    return RSym(s,p);
  }
  RSym operator() (int i) {
    return RSym(i,p);
  }
protected:
  ProdR* p;
};

std::ostream& operator<<(std::ostream& o, Sym s) {
  if( isVar(s) )
  {
    o << (char) ('A' + symID(s));
  } else {
    o << symID(s);
  }
  return o;
}


class CFG;

class Rule {
public:
  Rule(void)
  { }
  
  Rule& operator << (RSym s)
  {
    syms.push_back(s);
    return *this;
  }

  Rule& operator << (int n)
  {
    syms.push_back(mkTerm(n));
    return *this;
  }
  
  std::vector<RSym> syms;
};

Rule E(void) {
  return Rule();
}

class CFG {
public:
  CFG(int _alphsz)
    : alphsz(_alphsz), start( 0 )
  { }
    
  CFG(int _alphsz, int _nv)
    : alphsz(_alphsz)
  {
    for( int ii = 0; ii < _nv; ii++ )
    {
      
    }
  }

  ~CFG()
  {
    for(unsigned int ii = 0; ii < conds.size(); ii++)
      delete conds[ii];
  }

  Sym term(int i) { return mkTerm(i); }
  Sym var(int i)
  {
    while( ((int) prods.size()) <= i )
      prods.push_back( std::vector<ProdInfo>() );
    return mkVar(i);
  }
  Sym newVar(void)
  {
    int id = prods.size();
    prods.push_back( std::vector<ProdInfo>() );
    return mkVar(id);
  }

  void setStart(Sym s)
  {
    assert( isVar(s) );
    start = symID(s); 
  }
  
  Sym startSym(void) const {
    return mkVar(start);
  }

  void prod(RSym p, const Rule& r)
  {
    int r_id = rules.size();
    rules.push_back(r.syms);
    prods[symID(p.sym)].push_back(ProdInfo(p.cond, r_id));
  }
  
  void rulePush(int id, Sym r) {
    rules[id].push_back(r);
  }
  
  void normalize(void)
  {
    for( unsigned int ii = 0; ii < rules.size(); ii++ )
    {
      std::vector<RSym> nr(2);
      while( rules[ii].size() > 2 )
      {
        Sym next( newVar() );
        nr[1] = rules[ii].back();
        rules[ii].pop_back();
        nr[0] = rules[ii].back();
        rules[ii].pop_back();

        rules[ii].push_back(next);
        rules.push_back(nr);
        prods[symID(next)].push_back(ProdInfo(NULL,rules.size()-1));
      } 
    }
  }

  void print(void)
  {
    for( unsigned int vv = 0; vv < prods.size(); vv++ )
    {
      std::cout << (char) ('A' + vv) << " -> ";

      for( unsigned int ri = 0; ri < prods[vv].size(); ri++ )
      {
        if( ri != 0 )
          std::cout << "|";
        printRule(prods[vv][ri].rule);
      }
      std::cout << std::endl;
    }
  }

  void printRule(int r)
  {
    if( rules[r].size() == 0 )
    {
      std::cout << "e";
      return;
    }

    for( unsigned int ii = 0; ii < rules[r].size(); ii++ )
    {
      std::cout << rules[r][ii].sym;
    }
  }

  Cond attach(ProdR* p)
  {
    conds.push_back(p);
    return Cond(p);
  }

  int alphsz;
  int start;

  std::vector< std::vector<ProdInfo> > prods; // Mapping var -> rule.
  std::vector< std::vector<RSym> > rules;     // The actual production rules.
  std::vector<ProdR*> conds;
};

}
#endif
