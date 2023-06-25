#ifndef engine_h
#define engine_h

#include <chuffed/support/misc.h>

#include <functional>
#include <random>
#include <string>

#define DEBUG 0

enum OPT_TYPE { OPT_MIN = 0, OPT_MAX = 1 };
enum RESULT { RES_SAT, RES_LUN, RES_GUN, RES_UNK, RES_SEA };

class BranchGroup;
class Branching;
class BTPos;
class Checker;
class DecInfo;
class IntVar;
class Problem;
class Propagator;
class PseudoProp;
class TrailElem;
class BoolView;

//-----

class Engine {
public:
	static const int num_queues = 6;

	// Problem setup
	vec<IntVar*> vars;  // List of int vars
#ifdef HAS_VAR_IMPACT
	vec<int> var_sizes;  // List of int vars sizes
#endif
	vec<Branching*> outputs;        // List of output vars
	vec<Propagator*> propagators;   // List of propagators
	vec<PseudoProp*> pseudo_props;  // List of pseudo propagators
	vec<Checker*> checkers;         // List of constraint checkers
	vec<int> assumptions;           // List of assumption literals
	bool finished_init;

	Problem* problem;
	BranchGroup* branching;
	IntVar* opt_var;
	int opt_type;
	int best_sol;
	RESULT status;
	time_point time_out;
#ifdef HAS_VAR_IMPACT
	IntVar* last_int;  // Int var last branched on - for impact calculation
#endif

	// Intermediate propagation state
	vec<IntVar*> v_queue;            // List of changed vars
	vec<vec<Propagator*> > p_queue;  // Queue of propagators to run
	Propagator* last_prop;           // Last propagator run, set for idempotent propagators
	bool async_fail;                 // Asynchronous failure

	// Decision stack
	vec<DecInfo> dec_info;

	// Trails
	vec<TrailElem> trail;  // Raw data changes
	vec<int> trail_lim;

	// Statistics
	time_point start_time;
	duration init_time, opt_time;
	double base_memory;
	long long int conflicts, nodes, propagations, solutions, next_simp_db;
	int peak_depth;
	int restart_count;

	std::ostream* output_stream;
	std::function<void(Problem* p)> solution_callback;

	std::default_random_engine rnd;

private:
	// Init
	void init();
	void initMPI();

	// Engine core
	void newDecisionLevel();
	void doFixPointStuff();
	void makeDecision(DecInfo& di, int alt);
	bool constrain();
	bool propagate();
	void clearPropState();
	void topLevelCleanUp();
	void simplifyDB();
	void blockCurrentSol();
	static unsigned int getRestartLimit(unsigned int i);  // Return the restart limit for restart i
	void toggleVSIDS() const;
#if HAS_VAR_IMPACT
	vec<int>& getVarSizes(vec<int>& outVarSizes) const;
#endif

public:
	// Constructor
	Engine();

	// Trail methods
	void btToPos(int pos);
	void btToLevel(int level);

	// Solution-based phase saving
	void saveCurrentSolution();

	//Lookahead propagate
	std::tuple<int, int, bool> propagate_lookahead(int lit);
	int lookahead_conflicts = 0;

	// Interface methods
	RESULT search(const std::string& problemLabel = "chuffed");
	void solve(Problem* p, const std::string& problemLabel = "chuffed");

	void set_assumptions(vec<BoolView>& xs);
	static void retrieve_assumption_nogood(vec<BoolView>& xs);

	// Stats
	void printStats();
	void checkMemoryUsage();

	int decisionLevel() const { return trail_lim.size(); }
	int trailPos() const { return trail.size(); }
	int tpToLevel(int tp) const {
		for (int i = trail_lim.size(); (i--) != 0;) {
			if (tp >= trail_lim[i]) {
				return i + 1;
			}
		}
		return 0;
	}

	void setOutputStream(std::ostream& os) { output_stream = &os; }

	void setSolutionCallback(std::function<void(Problem*)> f) { solution_callback = std::move(f); }
};

extern Engine engine;

void optimize(IntVar* v, int t);

//-----

class TrailElem {
public:
	int* pt;
	int x;
	int sz;
	TrailElem(int* _pt, int _sz)
			: pt(_pt),
				x(_sz == 1   ? *((char*)pt)
					: _sz == 2 ? *((short*)pt)
										 : *pt),
				sz(_sz) {}
	void undo() const {
		switch (sz) {
			case 1:
				*((char*)pt) = x;
				break;
			case 2:
				*((short*)pt) = x;
				break;
			default:
				*pt = x;
				break;
		}
	}
};

template <class T, class U>
static inline void trailChange(T& v, const U u) {
	int* pt = (int*)&v;
	engine.trail.push(TrailElem(pt, sizeof(T)));
	if (sizeof(T) == 8) {
		engine.trail.push(TrailElem(pt + 1, sizeof(T)));
	}
	v = u;
}

// Like trailChange, but don't actually update the value.
template <class T>
static inline void trailSave(T& v) {
	int* pt = (int*)&v;
	engine.trail.push(TrailElem(pt, sizeof(T)));
	if (sizeof(T) == 8) {
		engine.trail.push(TrailElem(pt + 1, sizeof(T)));
	}
}

//------

// Auto-trailed int
// NOLINTBEGIN

#define AUTOTRAIL(t)                              \
	class T##t {                                    \
	public:                                         \
		t v;                                          \
		T##t() {}                                     \
		T##t(t _v) : v(_v) {}                         \
		operator t() const { return v; }              \
		t operator=(t o);                             \
		t operator=(T##t o) { return *this = o.v; }   \
		t operator+=(t o) { return *this = v + o; }   \
		t operator-=(t o) { return *this = v - o; }   \
		t operator*=(t o) { return *this = v * o; }   \
		t operator/=(t o) { return *this = v / o; }   \
		t operator%=(t o) { return *this = v % o; }   \
		t operator^=(t o) { return *this = v ^ o; }   \
		t operator&=(t o) { return *this = v & o; }   \
		t operator|=(t o) { return *this = v | o; }   \
		t operator<<=(t o) { return *this = v << o; } \
		t operator>>=(t o) { return *this = v >> o; } \
		t operator++() { return *this = v + 1; }      \
		t operator--() { return *this = v - 1; }      \
		t operator++(int dummy) {                     \
			int tmp = v;                                \
			*this = v + 1;                              \
			return tmp;                                 \
		}                                             \
		t operator--(int dummy) {                     \
			int tmp = v;                                \
			*this = v - 1;                              \
			return tmp;                                 \
		}                                             \
	};

AUTOTRAIL(char)
AUTOTRAIL(int)
AUTOTRAIL(int64_t)

cassert(sizeof(Tchar) == 1);
cassert(sizeof(Tint) == 4);
cassert(sizeof(Tint64_t) == 8);

inline char Tchar::operator=(char o) {
	int* pt = (int*)this;
	engine.trail.push(TrailElem(pt, 1));
	return v = o;
}

inline int Tint::operator=(int o) {
	int* pt = (int*)this;
	engine.trail.push(TrailElem(pt, 4));
	return v = o;
}

inline int64_t Tint64_t::operator=(int64_t o) {
	int* pt = (int*)this;
	engine.trail.push(TrailElem(pt, 4));
	engine.trail.push(TrailElem(pt + 1, 4));
	return v = o;
}

// NOLINTEND
//-----

class Problem {
public:
	virtual void print(std::ostream&) = 0;
	virtual void restrict_learnable(){};
};

#endif
