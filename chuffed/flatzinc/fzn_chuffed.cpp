#include <cstdio>
#include <cstring>
#include <chuffed/core/options.h>
#include <chuffed/core/engine.h>
#include <chuffed/flatzinc/flatzinc.h>

// #include "version.h"

int main(int argc, char** argv) {
    // Make a copy of the arguments for posterity.
    std::string commandLine;
    for (int i = 0; i < argc ; i++) {
        if (i > 0) commandLine += " ";
        commandLine += argv[i];
    }

    // if (argc == 2 && strcmp(argv[1], "--version") == 0) {
    //   std::cout << versionString << "\n";
    //   return 0;
    // }

    
  std::string filename;
  parseOptions(argc, argv, &filename, "fzn");
/*
	if (argc < 2) {
		printf("usage: %s [options] infile.fzn
"
"options:
-nof_solutions=n
-time_out=n
-rnd_seed=n
-verbosity=n
-print_sol=true|false
-restart_base=n
"
-toggle_vsids=true|false
-branch_random=true|false
-switch_to_vsids_after=n
-sat_polarity=n
"
-prop_fifo=true|false
"
-disj_edge_find=true|false
-disj_set_bp=true|false
"
-cumu_global=true|false
"
-sat_simplify=true|false
-fd_simplify=true|false
"
-lazy=true|false
-finesse=true|false
-learn=true|false
-vsids=true|false
-phase_saving=0|1|2
-sort_learnt_level=true|false
-one_watch=true|false
"
-eager_limit=n
-sat_var_limit=n
-nof_learnts=n
-learnts_mlimit=n
"
-lang_ext_linear=true|false
"
-mdd=true|false
-mip=true|false
-mip_branch=true|false
"
-sym_static=true|false
-ldsb=true|false
-ldsbta=true|false
-ldsbad=true|false
"
-parallel=true|false
-share_param=n
-bandwidth=n
-trial_size=n
-share_act=n
"
-saved_clauses=n
-use_uiv=true|false
"
-alldiff_cheat=true|false
-alldiff_stage=true|false
"
-a|--all|--all-solutions
--free
--parallel
-S, argv[0]);
		exit(1);
	}
*/

	if (argc == 1) {
		FlatZinc::solve(std::cin, std::cerr);
	} else {
		FlatZinc::solve(filename);
	}

  if (engine.opt_var && so.nof_solutions!=0) {
    std::string os;
    std::stringstream oss(os);
    engine.setOutputStream(oss);
    engine.solve(FlatZinc::s, commandLine);
    std::cout << oss.str();
  } else {
    engine.solve(FlatZinc::s, commandLine);
  }

	return 0;
}
