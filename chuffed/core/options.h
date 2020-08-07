#ifndef options_h
#define options_h

#include <cstdlib>
#include <cstring>
#include <string>
#include <chuffed/support/misc.h>

// When enabled, there is a command-line option -phase_saving=n, defaults to
// 0=none (1=some, 2=always, behaviour is exactly the same as MiniSat 2.2.0).
#define PHASE_SAVING 0

#define DEBUG_VERBOSE 0


enum RestartType { CHUFFED_DEFAULT, NONE, CONSTANT, LINEAR, LUBY, GEOMETRIC};

class Options {
public:
	// Solver options
	int nof_solutions;               // Number of solutions to find
	duration time_out;               // Amount of time before giving up
	int rnd_seed;                    // Random seed
	int verbosity;                   // Verbosity
	bool print_sol;                  // Print solutions
	unsigned int restart_scale;      // How many conflicts before restart
	bool restart_scale_override;     // Restart scale set from CLI
	double restart_base;             // How is the restart limit scaled (geometric)
	bool restart_base_override;      // Restart base set from CLI
	RestartType restart_type;        // How is the restart limit computed
	bool restart_type_override;      // Restart type set from CLI

	// Search options
	bool toggle_vsids;               // Alternate between search ann/vsids
	bool branch_random;              // Use randomization for tie-breaking
    int switch_to_vsids_after;       // Switch from search ann to vsids after a given number of conflicts
	int sat_polarity;                // Polarity of bool var to choose (0 = default, 1 = same, 2 = anti, 3 = random)

	// Propagator options
	bool prop_fifo;                  // Propagators are queued in FIFO, otherwise LIFO

	// Disjunctive propagator options
	bool disj_edge_find;             // Use edge finding
	bool disj_set_bp;                // Use set bounds propagation

	// Cumulative propagator options
	bool cumu_global;		 // Use the global cumulative propagator

	// Preprocessing options
	bool sat_simplify;               // Simplify clause database at top level
	bool fd_simplify;                // Simplify FD propagators at top level

	// Lazy clause options
	bool lazy;                       // Use lazy clause
	bool finesse;                    // Get better explanations sometimes
	bool learn;                      // Learn clauses
	bool vsids;                      // Use VSIDS as branching heuristic
#if PHASE_SAVING
	int phase_saving;                // Repeat same variable polarity (0=no, 1=recent, 2=always)
#endif
	bool sort_learnt_level;          // Sort lits in learnt clause based on level
	bool one_watch;                  // One watch learnt clauses

        bool exclude_introduced;         // Exclude introduced variables from learnt clauses
        bool decide_introduced;          // Search on introduced variables
        bool introduced_heuristic;       // Use name of variable to decide whether a variable is introduced
        bool use_var_is_introduced;      // Use var_is_introduced annotation to decide
                                         // whether a variable is introduced

  bool print_nodes;                // Print nodes as they are sent to the profiler (or
                                         // would be sent)
        bool print_implications;
        bool print_variable_list;
        bool send_skipped;               // Send skipped nodes?
        bool send_domains;               // Compute and send variable domains
        std::string filter_domains;
        bool learnt_stats;
        bool learnt_stats_nogood;
        bool debug;                      // Produce debug output
        bool exhaustive_activity;

        bool bin_clause_opt;          // Should length-2 learnt clauses be optimised?
        
	int eager_limit;                 // Max var range before we use lazy lit generation
	int sat_var_limit;               // Max number of sat vars before turning off lazy clause
	int nof_learnts;                 // Learnt clause no. limit
	int learnts_mlimit;              // Learnt clause mem limit

	// Language of explanation extension options
	bool lang_ext_linear;
    
    // MDD options 
	bool mdd;                        // Use MDD propagator

	// MIP options
	bool mip;                        // Use MIP propagator
	bool mip_branch;                 // Use MIP branching

	// Sym break options
	bool sym_static;
	bool ldsb;                       // Use lightweight dynamic symmetry breaking 1UIP crippled
	bool ldsbta;                     // Use lightweight dynamic symmetry breaking 1UIP
	bool ldsbad;                     // Use lightweight dynamic symmetry breaking all decision clause

	// Well founded semantics options
	bool well_founded;

	// Parallel options
	bool parallel;                   // Running in parallel mode
	int num_threads;                 // Number of worker threads
	int thread_no;                   // Thread number of this thread
	double share_param;              // Parameter for controlling which clauses are shared
	double bandwidth;                // How many lits per second we can share, counting all threads
	int trial_size;                  // Number of shared clauses put on trial (temp. immune to pruning)
	int share_act;                   // How to share clause activities between threads (0 = none, 1 = act, 2 = react)
	int num_cores;                   // Number of cpu cores in machine

	// Experimental
	int saved_clauses;
	bool use_uiv;

    // For circuit experiments
    // for all of these, 'highest' level means highest level number, which is actually
    // low in the search tree (recent).
    int circuitalg;         // 1-check, 2-prevent, 3-all, 4-scc
    int prevexpl;           // 1-equalities, 2-inside can't reach out
    int checkexpl;          // 1-equalities, 2-inside can't reach out, 
                            // 3-outside can't reach in, 4-smaller group can't reach bigger group, 
                            // 5-bigger group can't reach smaller group
    int checkfailure;       // 1-first, 2-smallest cycle, 3-largest cycle, 
                            // 4-cycle with lowest ave level, 5-cycle with highest ave level, 
                            // 6-cycle with lowest ave activity, 7-cycle with highest ave activity,
                            // 8-last, 9-highest min level, 10-lowest max level
    int checkevidence;      // for subcircuit: 1-first, 2-last, 3-high level, 4-low level
    int preventevidence;    // 1-first, 2-last, 3-high level, 4-low level, 5-other chain, 6-random
    int sccevidence;        // 1-first, 2-last, 3-high level, 4-low level, 6-random               
    int sccoptions;         // 1-standard, 2-within, 3-root, 4-root+within
    int rootSelection;      // 1-first non-fixed, 2-random unfixed, 3-end of shortest chain, 
                            // 4-end of longest chain, 5- start of shortest chain (+ collapse),
                            // 6-start of longest chain (+collapse), 7- first (even if fixed), 
                            // 8-random (even if fixed), 9-largest domain, 10-all not self cycles

	// for Nick's test (defaults probably work best in practice)
	bool alldiff_cheat;              // if n vars over n vals, enforce that all vals are taken
	bool alldiff_stage;              // if bounds or domain consistency, put value propagator too

#ifdef HAS_PROFILER
  // CP Profiler
  bool cpprofiler_enabled;
  int cpprofiler_id;
  int cpprofiler_port;
#endif

	Options();

};

extern Options so;

/// Parse command line options. If \a fileArg is not NULL, expect
/// a filename with extension \a fileExt.
void parseOptions(int& argc, char**& argv, std::string* fileArg=NULL, const std::string& fileExt=std::string());

#endif
