#ifndef options_h
#define options_h

#include "chuffed/support/misc.h"

#include <cstdlib>
#include <cstring>
#include <string>

// When enabled, there is a command-line option -phase_saving=n, defaults to
// 0=none (1=some, 2=always, behaviour is exactly the same as MiniSat 2.2.0).
#define PHASE_SAVING 0

#define DEBUG_VERBOSE 0

enum RestartType { CHUFFED_DEFAULT, NONE, CONSTANT, LINEAR, LUBY, GEOMETRIC };

class Options {
public:
	// Solver options
	int nof_solutions{1};                       // Number of solutions to find
	duration time_out;                          // Amount of time before giving up
	int rnd_seed{0};                            // Random seed
	int verbosity{0};                           // Verbosity
	bool print_sol{true};                       // Print solutions
	unsigned int restart_scale{1000000000};     // How many conflicts before restart
	bool restart_scale_override{true};          // Restart scale set from CLI
	double restart_base{1.5};                   // How is the restart limit scaled (geometric)
	bool restart_base_override{true};           // Restart base set from CLI
	RestartType restart_type{CHUFFED_DEFAULT};  // How is the restart limit computed
	bool restart_type_override{true};           // Restart type set from CLI

	// Search options
	bool toggle_vsids{false};   // Alternate between search ann/vsids
	bool branch_random{false};  // Use randomization for tie-breaking
	int switch_to_vsids_after{
			1000000000};  // Switch from search ann to vsids after a given number of conflicts
	int sat_polarity{
			0};            // Polarity of bool var to choose (0 = default, 1 = same, 2 = anti, 3 = random)
	bool sbps{false};  // Use Solution-based phase saving

	// Propagator options
	bool prop_fifo{false};  // Propagators are queued in FIFO, otherwise LIFO

	// Disjunctive propagator options
	bool disj_edge_find{true};  // Use edge finding
	bool disj_set_bp{true};     // Use set bounds propagation

	// Cumulative propagator options
	bool cumu_global{true};  // Use the global cumulative propagator

	// Preprocessing options
	bool sat_simplify{true};  // Simplify clause database at top level
	bool fd_simplify{true};   // Simplify FD propagators at top level

	// Lazy clause options
	bool lazy{true};     // Use lazy clause
	bool finesse{true};  // Get better explanations sometimes
	bool learn{true};    // Learn clauses
	bool vsids{false};   // Use VSIDS as branching heuristic
#if PHASE_SAVING
	int phase_saving{0};  // Repeat same variable polarity (0=no, 1=recent, 2=always)
#endif
	bool sort_learnt_level{false};  // Sort lits in learnt clause based on level
	bool one_watch{true};           // One watch learnt clauses

	bool exclude_introduced{false};  // Exclude introduced variables from learnt clauses
	bool decide_introduced{true};    // Search on introduced variables
	bool introduced_heuristic{
			false};  // Use name of variable to decide whether a variable is introduced
	bool use_var_is_introduced{false};  // Use var_is_introduced annotation to decide
																			// whether a variable is introduced

	bool print_nodes{false};  // Print nodes as they are sent to the profiler (or
														// would be sent)
	bool print_implications{false};
	bool print_variable_list{false};
	bool send_skipped{true};   // Send skipped nodes?
	bool send_domains{false};  // Compute and send variable domains
	std::string filter_domains;
	bool learnt_stats{false};
	bool learnt_stats_nogood{false};
	bool debug{false};  // Produce debug output
	bool exhaustive_activity{false};

	bool bin_clause_opt{true};  // Should length-2 learnt clauses be optimised?

	int eager_limit{1000};          // Max var range before we use lazy lit generation
	int sat_var_limit{2000000};     // Max number of sat vars before turning off lazy clause
	int nof_learnts{100000};        // Learnt clause no. limit
	int learnts_mlimit{500000000};  // Learnt clause mem limit

	// Language of explanation extension options
	bool lang_ext_linear{false};

	// MDD options
	bool mdd{false};  // Use MDD propagator

	// MIP options
	bool mip{false};         // Use MIP propagator
	bool mip_branch{false};  // Use MIP branching

	// Sym break options
	bool sym_static{false};
	bool ldsb{false};    // Use lightweight dynamic symmetry breaking 1UIP crippled
	bool ldsbta{false};  // Use lightweight dynamic symmetry breaking 1UIP
	bool ldsbad{false};  // Use lightweight dynamic symmetry breaking all decision clause

	// Well founded semantics options
	bool well_founded;

	// Experimental
	int saved_clauses{0};
	bool use_uiv{false};

	// For circuit experiments
	// for all of these, 'highest' level means highest level number, which is actually
	// low in the search tree (recent).
	int circuitalg{3};       // 1-check, 2-prevent, 3-all, 4-scc
	int prevexpl{1};         // 1-equalities, 2-inside can't reach out
	int checkexpl{2};        // 1-equalities, 2-inside can't reach out,
													 // 3-outside can't reach in, 4-smaller group can't reach bigger group,
													 // 5-bigger group can't reach smaller group
	int checkfailure{4};     // 1-first, 2-smallest cycle, 3-largest cycle,
													 // 4-cycle with lowest ave level, 5-cycle with highest ave level,
													 // 6-cycle with lowest ave activity, 7-cycle with highest ave activity,
													 // 8-last, 9-highest min level, 10-lowest max level
	int checkevidence{4};    // for subcircuit: 1-first, 2-last, 3-high level, 4-low level
	int preventevidence{1};  // 1-first, 2-last, 3-high level, 4-low level, 5-other chain, 6-random
	int sccevidence{1};      // 1-first, 2-last, 3-high level, 4-low level, 6-random
	int sccoptions{4};       // 1-standard, 2-within, 3-root, 4-root+within
	int rootSelection{1};    // 1-first non-fixed, 2-random unfixed, 3-end of shortest chain,
													 // 4-end of longest chain, 5- start of shortest chain (+ collapse),
													 // 6-start of longest chain (+collapse), 7- first (even if fixed),
													 // 8-random (even if fixed), 9-largest domain, 10-all not self cycles

	// for Nick's test (defaults probably work best in practice)
	bool alldiff_cheat{true};  // if n vars over n vals, enforce that all vals are taken
	bool alldiff_stage{true};  // if bounds or domain consistency, put value propagator too

	bool assump_int{false};  // Try and convert assumptions back to integer domain expressions.

#ifdef HAS_PROFILER
	// CP Profiler
	bool cpprofiler_enabled{false};
	int cpprofiler_id{-1};
	int cpprofiler_port{6565};
#endif

	Options();
};

extern Options so;

/// Parse command line options. If \a fileArg is not NULL, expect
/// a filename with extension \a fileExt.
void parseOptions(int& argc, char**& argv, std::string* fileArg = nullptr,
									const std::string& fileExt = std::string());

#endif
