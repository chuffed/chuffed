#ifndef sat_h
#define sat_h

#include "chuffed/branching/branching.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/support/heap.h"
#include "chuffed/support/misc.h"

#include <climits>
#include <cmath>
#include <cstdint>
#include <map>
#include <set>
#include <sstream>
#include <string>

#define TEMP_SC_LEN 1024
#define MAX_SHARE_LEN 512

class IntVar;
class SClause;

extern std::map<int, std::string> litString;

inline std::string getLitString(int n) {
	if (n == toInt(lit_True)) {
		return "true";
	}
	if (n == toInt(lit_False)) {
		return "false";
	}
	if (n == toInt(~lit_True)) {
		return "false";
	}
	if (n == toInt(~lit_False)) {
		return "true";
	}
	const std::map<int, std::string>::const_iterator it = litString.find(n);
	if (it != litString.end()) {
		return it->second;
	}
	std::stringstream ss;
	ss << "UNKNOWN_LITERAL (" << n << ")";
	return ss.str();
}

class SAT : public Branching {
	// For sorting Lits in learnt clause
	struct LitSort {
		vec<int>& level;
		bool operator()(Lit i, Lit j) { return (level[var(i)] > level[var(j)]); }
		LitSort(vec<int>& l) : level(l) {}
	} lit_sort;

	// For VSIDS
	struct VarOrderLt {
		const vec<double>& activity;
		bool operator()(int x, int y) const { return activity[x] > activity[y]; }
		VarOrderLt(const vec<double>& act) : activity(act) {}
	};

public:
	// Persistent state

	vec<Clause*> clauses;  // List of problem clauses
	vec<Clause*> learnts;  // List of learnt clauses

	vec<ChannelInfo> c_info;       // Channel info
	vec<vec<WatchElem> > watches;  // Watched lists
	vec<int8_t> assigns;           // The current assignments
	vec<Reason> reason;            // explanation for the variable's current value, or 'NULL' if none
	vec<int> trailpos;             // the trailPos at which the assignment was made
	vec<LitFlags> flags;           // Info about literal

	duration pushback_time;

	// Lazy Lit Generation
	int orig_cutoff;
	vec<int> var_free_list;
	vec<int> num_used;

	vec<vec<Lit> > trail;  // Boolean vars fix order
	vec<int> qhead;

	vec<vec<Clause*> > rtrail;  // List of temporary reason clauses

	// Intermediate state
	Clause* confl{nullptr};
	int index;
	vec<Lit> out_learnt;
	vec<int> out_learnt_level;
	vec<char> seen;
	vec<bool> ivseen;
	vec<int> ivseen_toclear;
	vec<Lit> analyze_stack;
	vec<Lit> analyze_toclear;
	vec<IntVar*> min_vars;
	SClause* temp_sc;

	Clause* short_expl;
	Clause* short_confl;

	// VSIDS
	double var_inc{1};     // Amount to bump variable with.
	double cla_inc{1};     // Amount to bump clause with.
	vec<double> activity;  // A heuristic measurement of the activity of a variable.
	Heap<VarOrderLt>
			order_heap;  // A priority queue of variables ordered with respect to the variable activity.
	vec<bool> polarity;

	void insertVarOrder(int x);   // Insert a variable in the decision order priority queue.
	void varDecayActivity();      // Decay all variables with the specified factor. Implemented by
																// increasing the 'bump' value instead.
	void varBumpActivity(Lit p);  // Increase a variable with the current 'bump' value.
	void claDecayActivity();      // Decay all clause activities with the specified factor
	void learntLenDecayActivity();
	void learntLenBumpActivity(int l);

	// Statistics
	int bin_clauses{0}, tern_clauses{0}, long_clauses{0}, learnt_clauses{0};
	long long int propagations{0}, back_jumps{0}, nrestarts{0}, next_simp_db{100000};
	long long int clauses_literals{0}, learnts_literals{0}, max_literals{0}, tot_literals{0};
	double avg_depth{100};
	double confl_rate{1000};

	// Parallel

	time_point ll_time;
	double ll_inc{1};
	double learnt_len_el{10};
	vec<double> learnt_len_occ;

	// Propagator methods

	SAT();
	~SAT();
	void init();
	int newVar(int n = 1, ChannelInfo ci = ci_null);
	int getLazyVar(ChannelInfo ci);
	void removeLazyVar(int v);
	void addClause(Lit p, Lit q);
	void addClause(vec<Lit>& ps, bool one_watch = false);
	void addClause(Clause& c, bool one_watch = false);
	void removeClause(Clause& c);
	void topLevelCleanUp();
	void simplifyDB();
	bool simplify(Clause& c) const;
	void enqueue(Lit p, Reason r = nullptr);
	void cEnqueue(Lit p, Reason r);
	void aEnqueue(Lit p, Reason r, int l);
	void untrailToPos(vec<Lit>& t, int p);
	void btToLevel(int level);
	void btToPos(int sat_pos, int core_pos);
	bool propagate();
	Clause* getExpl(Lit p);
	Clause* _getExpl(Lit p);
	Clause* getConfl(Reason& r, Lit p) const;

	void reduceDB();
	void printStats() const;
	void printLearntStats();

	// Branching methods

	bool finished() override;
	double getScore(VarBranch /*vb*/) override { NEVER; }
	DecInfo* branch() override;

	// Solution-based phase saving
	void saveCurrentPolarities() {
		for (int i = 0; i < assigns.size(); i++) {
			if (assigns[i] == toInt(l_True)) {
				polarity[i] = false;  // False means to branch 'true' on this SAT variable
			} else if (assigns[i] == toInt(l_False)) {
				polarity[i] = true;  // True means to branch 'false' on this SAT variable
			}
		}
	}

	// Conflict methods

	void analyze(int nodeid, std::set<int>& contributingNogoods);
	void getLearntClause(int nodeid, std::set<int>& contributingNogoods);
	int findConflictLevel();
	void explainUnlearnable(std::set<int>& contributingNogoods);
	void explainToExhaustion(std::set<int>& contributingNogoods);
	void clearSeen();
	int findBackTrackLevel();

	bool consistent() const { return qhead.last() == trail.last().size(); }
	int nVars() const { return assigns.size(); }
	int decisionLevel() const { return trail.size() - 1; }
	Lit decLit(int i) const { return trail[i][0]; }
	lbool value(Lit p) const { return toLbool(assigns[var(p)]) ^ sign(p); }
	bool locked(Clause& c) const { return reason[var(c[0])].pt() == &c && value(c[0]) == l_True; }

	void newDecisionLevel();
	void incVarUse(int v);
	void decVarUse(int v);
	void setConfl(Lit p = lit_False, Lit q = lit_False);

	bool isRootLevel(int v) const {
		return engine.trail_lim.size() == 0 || trailpos[v] < engine.trail_lim[0];
	}
	bool isCurLevel(int v) const { return trailpos[v] >= engine.trail_lim.last(); }
	int getLevel(int v) const {
		for (int i = engine.trail_lim.size(); (i--) != 0;) {
			if (trailpos[v] >= engine.trail_lim[i]) {
				return i;
			}
		}
		return 0;
	}

	// Debug Methods

	void printLit(Lit p);
	template <class T>
	void printClause(T& c);
	void checkConflict() const;
	void checkExplanation(Clause& c, int clevel, int index);
};

inline void SAT::newDecisionLevel() {
	trail.push();
	qhead.push(0);
	rtrail.push();
}

inline void SAT::incVarUse(int v) {
	v -= orig_cutoff;
	if (v >= 0) {
		num_used[v]++;
	}
}

inline void SAT::decVarUse(int v) {
	v -= orig_cutoff;
	if (v >= 0) {
		num_used[v]--;
	}
}

inline Clause* SAT::getExpl(Lit p) {
	const Reason& r = reason[var(p)];
	switch (r.type()) {
		case 0:
			return r.pt();
		case 1:
			btToPos(index, trailpos[var(p)]);
			return _getExpl(p);
		default:
			Clause& c = *short_expl;
			c.sz = r.type();
			c[1] = toLit(r.d1());
			if (c.sz == 3) {
				c[2] = toLit(r.d2());
			}
			return short_expl;
	}
}

extern SAT sat;

#endif
