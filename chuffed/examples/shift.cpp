#include <iostream>
#include <cstdlib>
#include <cmath>
#include <algorithm>
#include <vector>
//#include <chuffed/circuit/FDNNF.h>
#include <chuffed/mdd/MDD.h>
#include <chuffed/mdd/CFG.h>
#include <chuffed/mdd/CYK.h>
#include <chuffed/globals/mddglobals.h>
// #include <chuffed/globals/circglobals.h>
// #include <chuffed/circuit/nnfprop.h>
#include <chuffed/mdd/circ_fns.h>

// Using the simplified model, with infinite under-costs, and unit over-costs.
// This maps to hard coverage constraints, and minimizing the # of worked hours.

#define DECOMP 1
#define USEMDD 2
#define USEGCC 4

#define DISTINCT_REST

#if 0
template <class T>
T circ_gcc(T fff, vec< vec<T> >& xs, IntRelType rel, const vec<int>& cards)
{
  assert(cards.size() > 0);

  vec< vec<T> > vals(cards.size());
  for(int ii = 0; ii < xs.size(); ii++)
  {
    assert(xs[ii].size() == cards.size());
    for(int jj = 0; jj < cards.size(); jj++)
    {
      vals[jj].push(xs[ii][jj]);
    }
  }

  T ret = card(fff, vals[0], rel, cards[0]);
  for(int jj = 1; jj < cards.size(); jj++)
  {
    assert(vals[jj].size() == xs.size());
    ret = ret&(card(fff,vals[jj],rel,cards[jj]));
  }
  return ret;
}

void mdd_gcc(vec<IntVar*>& vs, IntRelType rel, const vec<int>& cards)
{
  MDDTable tab(vs.size());
  
  vec< vec<MDD> > vars;
  for(int ii = 0; ii < vs.size(); ii++)
  {
    vars.push();
    for(int jj = 0; jj < cards.size(); jj++)
      vars.last().push(tab.vareq(ii,jj));
  }
  MDD ret(circ_gcc(tab.fff(), vars, rel, cards));
  
  addMDD(vs, ret);
}
#endif

// Code for additional option handling.
static char* hasPrefix(char* str, const char* prefix) {
	int len = strlen(prefix);
	if (strncmp(str, prefix, len) == 0) return str + len;
	else return NULL;
}

#ifdef DISTINCT_REST
enum GapT { G_R = 2, G_B = 1, G_L = 0, maxG = 3 };
#else
enum GapT { G_R = 0, G_B = 0, G_L = 0, maxG = 1 };
#endif

class ShiftSched : public Problem {
public:
  int const staff;
  int const shifts;
  int const acts;
  int const dom;
  const vec< vec<int> > demand;
  vec< vec<IntVar*> > xv;
  IntVar* cost;

  ShiftSched(int _staff, int _shifts, int _acts, vec< vec<int> >& _demand, int mode)
      : staff(_staff), shifts(_shifts), acts(_acts), dom(acts+maxG), demand(_demand)
  {
    for(int ww = 0; ww < staff; ww++)
    {
      xv.push();
      for( int ss = 0; ss < shifts; ss++ )
      {
          xv[ww].push(newIntVar(0,dom-1));
          xv[ww][ss]->specialiseToEL();
      }
    }
    
    // Build the grammar 
    int first = 0;
    while(first < shifts)
    {
      for(int ii = 0; ii < acts; ii++)
      {
        if(demand[first][ii])
          goto found_first;
      }
      first++;
    }
found_first:

    int last = first;
    for(int ss = first; ss < shifts; ss++)
    {
      for(int ii = 0; ii < acts; ii++)
      {
        if(demand[ss][ii])
        {
          last = ss;
          break;
        }
      }
    }
    CFG::CFG g( buildSchedG(acts, first, last) ); 
    
#if 0
    if(!(mode&USEMDD))
    {
      // Construct variables for the circuit
      FDNNFTable tab;
      std::vector< std::vector<FDNNF> > seq;
      for(int ii = 0; ii < shifts; ii++)
      {
        seq.push_back( std::vector<FDNNF>() );
        for(int kk = 0; kk < dom; kk++)
        {
          seq[ii].push_back(tab.vareq(ii, kk));
        }
      }
      // Construct a circuit from the grammar.
      FDNNF gcirc(parseCYK(tab.fff(), seq, g));

      if(mode&DECOMP)
      {
        for(int ww = 0; ww < staff; ww++)
        {
//          nnf_decomp(xv[ww], gcirc);
          nnf_decompGAC(xv[ww], gcirc);
        }
      } else {
        // Enforce the schedule for each worker.
        for(int ww = 0; ww < staff; ww++)
          addNNF(xv[ww], gcirc);
      }
    } else {
#endif
      // Construct variables for the circuit
      MDDTable mdd_tab(shifts);
      std::vector< std::vector<MDD> > seq;
      for(int ii = 0; ii < shifts; ii++)
      {
        seq.push_back( std::vector<MDD>() );
        for(int kk = 0; kk < dom; kk++)
        {
          seq[ii].push_back(mdd_tab.vareq(ii, kk));
        }
      }
      MDD gcirc(parseCYK(mdd_tab.fff(), seq, g));
      
      // Enforce the schedule for each worker.
      MDDOpts opts;
      for(int ww = 0; ww < staff; ww++)
        addMDD(xv[ww], gcirc, opts);
#if 0
    }
#endif

    for(int ww = 1; ww < staff; ww++)
      lex(xv[ww-1],xv[ww],false);

    // Enforce coverage constraints.
    for(int ss = 0; ss < shifts; ss++)
    {
      /*
      if(mode&USEGCC)
      {
        // Allocation for the current shift.
        vec<IntVar*> sv;
        for(int ww = 0; ww < staff; ww++)
          sv.push(xv[ww][ss]);

        mdd_gcc(sv, IRT_GE, demand[ss]);
      } else {
        */
        for(int act = 0; act < acts; act++)
        {
          vec<BoolView> bv;
          for(int ww = 0; ww < staff; ww++)
          {
            bv.push(xv[ww][ss]->getLit(act,1));
          }
          
          bool_linear_decomp(bv, IRT_GE, demand[ss][act]);
        }
//      } 
    }
  
    // Define the objective function.
    vec<BoolView> rostered;
    for(int ss = 0; ss < shifts; ss++)
    {
      if(ss < first || ss > last)
        continue;

      for(int ww = 0; ww < staff; ww++)
      {
        rostered.push(xv[ww][ss]->getLit(acts-1,3));
      }
    }
    
    unsigned int cMin(0); 
    for(int ss = 0; ss < shifts; ss++)
    {
      for(int aa = 0; aa < acts; aa++)
      {
        cMin += demand[ss][aa];
      }
    }

    cost = newIntVar(cMin, (last - first + 1)*staff);
    bool_linear_decomp(rostered, IRT_LE, cost);

#if 0
    vec<IntVar*> rostered_int;
    for(int ss = 0; ss < shifts; ss++)
    {
      if(ss < first || ss > last)
        continue;

      for(int ww = 0; ww < staff; ww++)
      {
        IntVar* sv = newIntVar(0,1);
        bool2int(xv[ww][ss]->getLit(acts-1,3),sv);
        rostered_int.push(sv);
      }
    }
    int_linear(rostered_int, IRT_GE, cost);
#endif

    vec<IntVar*> vs;
    for(int ss = 0; ss < shifts; ss++)
    {
      for(int ww = 0; ww < staff; ww++)
      {
        vs.push(xv[ww][ss]);
      }
    }

    branch(vs, VAR_INORDER, VAL_MAX);
		optimize(cost, OPT_MIN);
    
//    vs.push(cost);
    output_vars(vs);
  }
  
  CFG::CFG buildSchedG(int n_acts, int first, int last)
  {
    unsigned int rest(n_acts+G_R);
    unsigned int brk(n_acts+G_B);
    unsigned int lunch(n_acts+G_L);
    CFG::CFG g(n_acts+maxG);

    CFG::Sym S(g.newVar());
    g.setStart(S);

    CFG::Sym R(g.newVar());
    CFG::Sym P(g.newVar());
    CFG::Sym W(g.newVar());
    CFG::Sym L(g.newVar());
    CFG::Sym F(g.newVar());
    
    CFG::Cond actLB(g.attach(new CFG::SpanLB(4)));
    CFG::Cond lunEQ(g.attach(new CFG::Span(4,4)));
    CFG::Cond part(g.attach(new CFG::Span(13,24)));
    CFG::Cond full(g.attach(new CFG::Span(30,38)));
    CFG::Cond open(g.attach(new CFG::Start(first,last)));

    std::vector<CFG::Sym> activities;
    for(int ii = 0; ii < n_acts; ii++)
    {
      CFG::Sym act(g.newVar());
      activities.push_back(act);
      g.prod(open(act), CFG::E() << ii << act);
      g.prod(open(act), CFG::E() << ii);
      
      g.prod(W, CFG::E() << actLB(act));
    }

    g.prod(S, CFG::E() << R << part(P) << R);
    g.prod(S, CFG::E() << R << full(F) << R);
    
    g.prod(R, CFG::E() << rest << R);
    g.prod(R, CFG::E() << rest);
    
    g.prod(L, CFG::E() << lunch << L);
    g.prod(L, CFG::E() << lunch);

    g.prod(P, CFG::E() << W << brk << W);
    g.prod(F, CFG::E() << P << lunEQ(L) << P);

    return g;
  }

  void print(std::ostream& os) {
#if 1
    for(int act = 0; act < acts; act++)
    {
      os << "[";
      for(int ss = 0; ss < shifts; ss++)
      {
        os << demand[ss][act];
      }
      os << "]\n";
    }
#endif
    os << "Hours worked: " << (1.0*cost->getVal()/4) << "\n";
    for(int ww = 0; ww < xv.size(); ww++)
    {
      os << "[";
      for (int ii = 0; ii < shifts; ii++ )
      {
//        if(ii)
//            printf(", ");
        int val(xv[ww][ii]->getVal());
        if(val < acts)
        {
          os << val;
        } else {
          switch(val - acts)
          {
#ifdef DISTINCT_REST
            case G_R:
              os << "R";
              break;
            case G_B:
              os << "B";
              break;
            case G_L:
              os << "L";
              break;
#else
            case G_R:
              os << "R";
              break;
            default:
              assert(0);
              break;
#endif
          }
        }
      }
      os << "]\n";
    }
  }
};

void parseInst(std::istream& in, int& acts, int& shifts, vec< vec<int> >& demand)
{
  in >> acts;
  in >> shifts;

  for(int ss = 0; ss < shifts; ss++)
  {
    demand.push();
    for(int aa = 0; aa < acts; aa++)
    {
      double d;
      in >> d;
      demand.last().push((int) ceil(d));
    }
  }
}

int main(int argc, char** argv)
{
  int mode = 0;
  
  int jj = 1;
  char* value;
  for(int ii = 1; ii < argc; ii++)
  {
    if ((value = hasPrefix(argv[ii], "-decomp=")))
    {
      if(strcmp(value, "true") == 0)
      {
        mode |= DECOMP; 
      }
    } else if ((value = hasPrefix(argv[ii], "-mdd="))) {
      if(strcmp(value, "true") == 0)
      {
        mode |= USEMDD; 
      }
    } else if ((value = hasPrefix(argv[ii], "-gcc="))) {
      if(strcmp(value, "true") == 0)
      {
        mode |= USEGCC; 
      }
    } else {
      argv[jj++] = argv[ii];
    }
  }
  argc = jj;

  parseOptions(argc, argv);

  // Arguments:
  // #staff
  
//	assert(argc == 2 || argc == 3);
	assert(argc == 2);
  int staff = 1;
  int acts = 1;
  int shifts = 96;

  staff = atoi(argv[1]);

  vec< vec<int> > demand;
  
  parseInst(std::cin, acts, shifts, demand);   

  engine.solve(new ShiftSched(staff,shifts,acts,demand,mode));
  return 0;
}
