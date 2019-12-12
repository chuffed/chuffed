#ifndef sat_h
#define sat_h

#include <climits>
#include <cmath>
#include <map>
#include <set>
#include <string>
#include <chuffed/support/misc.h>
#include <chuffed/support/heap.h>
#include <chuffed/core/sat-types.h>
#include <chuffed/branching/branching.h>

#include <sstream>

#define TEMP_SC_LEN 1024
#define MAX_SHARE_LEN 512

class IntVar;
class SClause;

extern std::map<int,std::string> litString;

inline
std::string getLitString(int n) {
  if (n == toInt(lit_True)) return "true";
  if (n == toInt(lit_False)) return "false";
  if (n == toInt(~lit_True)) return "false";
  if (n == toInt(~lit_False)) return "true";
    std::map<int,std::string>::const_iterator it = litString.find(n);
    if (it != litString.end())
        return it->second;
    else {
      std::stringstream ss;
      ss << "UNKNOWN_LITERAL (" << n << ")";
      return ss.str();
    }
}

class SAT : public Branching {
	// For sorting Lits in learnt clause
	struct LitSort {
		vec<int>& level;
		bool operator() (Lit i, Lit j) { return (level[var(i)] > level[var(j)]); }
		LitSort(vec<int>& l) : level(l) {}
	} lit_sort;

	// For VSIDS
	struct VarOrderLt {
		const vec<double>&  activity;
		bool operator () (int x, int y) const { return activity[x] > activity[y]; }
		VarOrderLt(const vec<double>&  act) : activity(act) {}
	};

public:

	// Persistent state

  vec<Clause*> clauses;             // List of problem clauses
  vec<Clause*> learnts;             // List of learnt clauses

	vec<ChannelInfo> c_info;          // Channel info
  vec<vec<WatchElem> > watches;     // Watched lists
  vec<char> assigns;                // The current assignments
  vec<Reason> reason;               // explanation for the variable's current value, or 'NULL' if none
  vec<int> trailpos;                // the trailPos at which the assignment was made
	vec<LitFlags> flags;              // Info about literal

	duration pushback_time;

	// Lazy Lit Generation
	int orig_cutoff;
	vec<int> var_free_list;
	vec<int> num_used;

	vec<vec<Lit> > trail;             // Boolean vars fix order
	vec<int> qhead;

	vec<vec<Clause*> > rtrail;        // List of temporary reason clauses

	// Intermediate state
	Clause *confl;
	int index;
	vec<Lit> out_learnt;
        vec<int> out_learnt_level;
  vec<char> seen;
	vec<bool> ivseen;
	vec<int> ivseen_toclear;
  vec<Lit> analyze_stack;
  vec<Lit> analyze_toclear;
	vec<IntVar*> min_vars;
	SClause *temp_sc;

	Clause *short_expl;
	Clause *short_confl;

	// VSIDS
	double var_inc;                        // Amount to bump variable with.
	double cla_inc;                        // Amount to bump clause with.
	vec<double> activity;                  // A heuristic measurement of the activity of a variable.
	Heap<VarOrderLt> order_heap;           // A priority queue of variables ordered with respect to the variable activity.
	vec<bool> polarity;

	void insertVarOrder(int x);            // Insert a variable in the decision order priority queue.
	void varDecayActivity();               // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
	void varBumpActivity(Lit p);           // Increase a variable with the current 'bump' value.
	void claDecayActivity();               // Decay all clause activities with the specified factor
	void learntLenDecayActivity();
	void learntLenBumpActivity(int l);

	// Statistics
	int bin_clauses, tern_clauses, long_clauses, learnt_clauses;
	long long int propagations, back_jumps, nrestarts, next_simp_db;
  long long int clauses_literals, learnts_literals, max_literals, tot_literals;
	double avg_depth;
	double confl_rate;

	// Parallel

	time_point ll_time;
	double ll_inc;
	double learnt_len_el;
	vec<double> learnt_len_occ;

	// Propagator methods

	SAT();
	~SAT();
	void init();
	int  newVar(int n = 1, ChannelInfo ci = ci_null);
	int  getLazyVar(ChannelInfo ci);
	void removeLazyVar(int v);
	void addClause(Lit p, Lit q);
	void addClause(vec<Lit>& ps, bool one_watch = false);
	void addClause(Clause& c, bool one_watch = false);
	void removeClause(Clause& c);
	void topLevelCleanUp();
	void simplifyDB();
	bool simplify(Clause& c);
	void enqueue(Lit p, Reason r = NULL);
	void cEnqueue(Lit p, Reason r);
	void aEnqueue(Lit p, Reason r, int l);
	void untrailToPos(vec<Lit>& t, int p);
	void btToLevel(int level);
	void btToPos(int sat_pos, int core_pos);
	bool propagate();
	Clause* getExpl(Lit p);
	Clause* _getExpl(Lit p);
	Clause* getConfl(Reason& r, Lit p);


	void reduceDB();
	void printStats();
	void printLearntStats();

	// Branching methods

	bool finished();
	double getScore(VarBranch vb) { NEVER; }
	DecInfo* branch();

	// Parallel methods

	void convertToSClause(Clause& c);
	void convertToClause(SClause& sc);
	void addLearnt();
	void updateShareParam();

	// Conflict methods

	void analyze(int nodeid, std::set<int>& contributingNogoods);
	void getLearntClause(int nodeid, std::set<int>& contributingNogoods);
	int findConflictLevel();
	void explainUnlearnable(std::set<int>& contributingNogoods);
	void explainToExhaustion(std::set<int>& contributingNogoods);
	void clearSeen();
	int  findBackTrackLevel();


	bool     consistent    ()      const   { return qhead.last() == trail.last().size(); }
	int      nVars         ()      const   { return assigns.size(); }
	int      decisionLevel ()      const   { return trail.size()-1; }
	Lit      decLit        (int i) const   { return trail[i][0]; }
	lbool    value         (Lit p) const   { return toLbool(assigns[var(p)]) ^ sign(p); }
	bool     locked        (Clause& c) const { return reason[var(c[0])].pt == &c && value(c[0]) == l_True; }

	void    newDecisionLevel();
	void    incVarUse(int v);
	void    decVarUse(int v);
	void    setConfl(Lit p = lit_False, Lit q = lit_False);

	bool isRootLevel(int v) const { return engine.trail_lim.size()==0 || trailpos[v] < engine.trail_lim[0]; }
	bool isCurLevel(int v) const { return trailpos[v] >= engine.trail_lim.last(); }
	int getLevel(int v) const { 
          for (int i = engine.trail_lim.size(); i--; ) {
            if (trailpos[v] >= engine.trail_lim[i])
              return i;
          }
          return 0;
	}

	// Debug Methods

	void printLit(Lit p);
	template <class T> void printClause(T& c);
	void checkConflict();
	void checkExplanation(Clause& c, int clevel, int index);

};

inline void SAT::newDecisionLevel() {
	trail.push();
	qhead.push(0);
	rtrail.push();
}

inline void SAT::incVarUse(int v) {
	v -= orig_cutoff;
	if (v >= 0) num_used[v]++;
}

inline void SAT::decVarUse(int v) {
	v -= orig_cutoff;
	if (v >= 0) num_used[v]--;
}

inline Clause* SAT::getExpl(Lit p) {
	Reason& r = reason[var(p)];
	switch(r.d.type) {
		case 0:
			return r.pt;
		case 1: 
			btToPos(index, trailpos[var(p)]);
			return _getExpl(p);
		default:
			Clause& c = *short_expl;
			c.sz = r.d.type; c[1] = toLit(r.d.d1);
      if (c.sz == 3)
        c[2] = toLit(r.d.d2);
			return short_expl;
	}
}

extern SAT sat;

#endif
