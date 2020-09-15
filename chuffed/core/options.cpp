
#include <chuffed/core/options.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/sat.h>

#include <iostream>

Options so;

Options::Options() :
		nof_solutions(1)
	, time_out(0)
	, rnd_seed(0)
	, verbosity(0)
	, print_sol(true)
	, restart_scale(1000000000)
    , restart_scale_override(true)
    , restart_base(1.5)
    , restart_base_override(true)
    , restart_type(CHUFFED_DEFAULT)
    , restart_type_override(true)

	, toggle_vsids(false)
	, branch_random(false)
	, switch_to_vsids_after(1000000000)
	, sat_polarity(0)

	, prop_fifo(false)

	, disj_edge_find(true)
	, disj_set_bp(true)

	, cumu_global(true)

	, sat_simplify(true)
	, fd_simplify(true)

	, lazy(true)
	, finesse(true)
	, learn(true)
	, vsids(false)
#if PHASE_SAVING
	, phase_saving(0)
#endif
	, sort_learnt_level(false)
	, one_watch(true)

        , exclude_introduced(false)
        , decide_introduced(true)
        , introduced_heuristic(false)
        , use_var_is_introduced(false)
        , print_nodes(false)
        , print_implications(false)
        , print_variable_list(false)
        , send_skipped(true)
        , send_domains(false)

        , learnt_stats(false)
        , learnt_stats_nogood(false)
        , debug(false)
        , exhaustive_activity(false)

        , bin_clause_opt(true)

	, eager_limit(1000)
	, sat_var_limit(2000000)
	, nof_learnts(100000)
	, learnts_mlimit(500000000)

	, lang_ext_linear(false)
    
	, mdd(false)
	, mip(false)
	, mip_branch(false)

	, sym_static(false)
	, ldsb(false)
	, ldsbta(false)
	, ldsbad(false)

	, parallel(false)
	, num_threads(-1)
	, thread_no(-1)
	, share_param(10)
	, bandwidth(3000000)
	, trial_size(50000)
	, share_act(0)
	, num_cores(1)

	, saved_clauses(0)
	, use_uiv(false)

	, circuitalg(3)
	, prevexpl(1)
	, checkexpl(2)
	, checkfailure(4)
	, checkevidence(4)
	, preventevidence(1)
	, sccevidence(1)
    , sccoptions(4)
    , rootSelection(1)

	, alldiff_cheat(true)
	, alldiff_stage(true)
#ifdef HAS_PROFILER
  , cpprofiler_enabled(false)
  , cpprofiler_id(-1)
  , cpprofiler_port(6565)
#endif
{}


template <class T> inline bool assignStr(T*, const std::string ) { return false; }
template<> inline bool assignStr(std::string* pS, const std::string s ) {
  *pS = s;
  return true;
}

/// A simple per-cmdline option parser
class CLOParser {
  int& i;              // current item
  const int argc=0;
  const char* const* argv=0;
  
public:
  CLOParser( int& ii, const int ac, const char* const* av )
  : i(ii), argc(ac), argv(av) { }
  template <class Value=int>
  inline bool get(  const char* names, // space-separated option list
                  Value* pResult=nullptr, // pointer to value storage
                  bool fValueOptional=false // if pResult, for non-string values
  ) {
    return getOption( names, pResult, fValueOptional );
  }
  template <class Value=int>
  inline bool getOption(  const char* names, // space-separated option list
                        Value* pResult=nullptr, // pointer to value storage
                        bool fValueOptional=false // if pResult, for non-string values
  ) {
    assert(0 == strchr(names, ','));
    assert(0 == strchr(names, ';'));
    if( i>=argc )
      return false;
    assert( argv[i] );
    std::string arg( argv[i] );
    /// Separate keywords
    std::string keyword;
    std::istringstream iss( names );
    while ( iss >> keyword ) {
      if ( ((2<keyword.size() || 0==pResult) && arg!=keyword) ||  // exact cmp
          (0!=arg.compare( 0, keyword.size(), keyword )) )           // truncated cmp
        continue;
      /// Process it
      if ( keyword.size() < arg.size() ) {
        if ( 0==pResult )
          continue;
        arg.erase( 0, keyword.size() );
      } else {
        if ( 0==pResult )
          return true;
        i++;
        if( i>=argc )
          return fValueOptional;
        arg = argv[i];
      }
      assert( pResult );
      if ( assignStr( pResult, arg ) )
        return true;
      std::istringstream iss( arg );
      Value tmp;
      if ( !( iss >> tmp ) ) {
        --i;
        if ( fValueOptional ) {
          return true;
        }
        // Not print because another agent can handle this option
        //           cerr << "\nBad value for " << keyword << ": " << arg << endl;
        return false;
      }
      *pResult = tmp;
      return true;
    }
    return false;
  }
  inline bool getBool(const char* names, bool& result) {
    std::string buffer;
    std::string shortOptions;
    std::string longOptions;
    std::string negOptions;
    std::istringstream iss( names );
    std::string keyword;
    while (iss >> keyword) {
      if (keyword.size()<=2) {
        if (!shortOptions.empty())
          shortOptions+=" ";
        shortOptions+=keyword;
      } else {
        if (!longOptions.empty())
          longOptions+=" ";
        longOptions+=keyword;
        if (keyword[0]=='-' && keyword[1]=='-') {
          if (!negOptions.empty())
            negOptions+=" ";
          negOptions+="--no"+keyword.substr(1);
        }
      }
    }
    
    if (getOption(shortOptions.c_str())) {
      result = true;
      return true;
    }
    if (getOption(negOptions.c_str())) {
      result = false;
      return true;
    }
    
    if (getOption(longOptions.c_str(),&buffer)) {
      if (buffer.empty()) {
        result = true;
      } else if (buffer=="true" || buffer=="on" || buffer=="1") {
        result = true;
      } else if (buffer=="false" || buffer=="off" || buffer=="0") {
        result = false;
      } else {
        --i;
        result = true;
      }
      return true;
    }
    return false;
  }
};  // class CLOParser

void printHelp(int& argc, char**& argv, const std::string& fileExt) {
  Options def;
  std::cout << "Usage: " << argv[0] << " [options] ";
  if (fileExt.size()>0)
    std::cout << "<file>." << fileExt;
  std::cout << "\n";
  std::cout << "Options:\n";
  std::cout <<
  "  -h, --help\n"
  "     Print help for common options.\n"
  "  --help-all\n"
  "     Print help for all options.\n"
  "  -a\n"
  "     Satisfaction problems: Find and print all solutions.\n"
  "     Optimisation problems: Print all (sub-optimal) intermediate solutions.\n"
  "  -n <n>, --n-of-solutions <n>\n"
  "     An upper bound on the number of solutions (default " << def.nof_solutions << ").\n"
  "  -v, --verbose\n"
  "     Verbose mode (default " << (def.verbosity == 0 ? "off" : "on") << ").\n"
  "  -t, --time-out <n>\n"
  "     Time out in milliseconds (default " << def.time_out.count() << ", 0 = run indefinitely).\n"
  "  --rnd-seed <n>\n"
  "     Set random seed (default " << def.rnd_seed << "). If 0 then the current time\n"
  "     via std::time(0) is used.\n"
  "\n"
  "Search Options:\n"
  "  -f [on|off]\n"
  "     Free search. Alternates between user-specified and activity-based\n"
  "     search when search is restarted. Restart base is set to 100.\n"
#ifdef HAS_PROFILER
  "\n"
  "Profiler Options:\n"
  "  -cpprofiler id,port\n"
  "     Send search to CP Profiler with the given execution ID and port.\n"
#endif
  "\n"
  ;
}

void printLongHelp(int& argc, char**& argv, const std::string& fileExt) {
  printHelp(argc, argv, fileExt);
  Options def;
  std::cout <<
  "General Options:\n"
  "  --verbosity <n>\n"
  "     Set verbosity (default " << def.verbosity << ").\n"
  "  --print-sol [on|off], --no-print-sol\n"
  "     Print solutions (default " << (def.print_sol ? "on" : "off") << ").\n"
  "  --prop-fifo [on|off], --no-prop-fifo\n"
  "     Use FIFO (first in, first out) queues for propagation executions instead\n"
  "     of LIFO (last in, first out) queues (default " << (def.prop_fifo ? "on" : "off") << ").\n"
  "\n"
  "More Search Options:\n"
  "  --vsids [on|off], --no-vsids\n"
  "     Use activity-based search on the Boolean variables (default " << (def.vsids ? "on" : "off") << ").\n"
  "  --restart [chuffed|none|constant|linear|luby|geometric]\n"
  "     Restart sequence type (default chuffed).\n"
  "  --restart-scale <n>\n"
  "     Scale factor for restart sequence (default " << def.restart_scale << ").\n"
  "  --restart-base <n>\n"
  "     Base for geometric restart sequence (default " << def.restart_base << ").\n"
  "  --toggle-vsids [on|off], --no-toggle-vsids\n"
  "     Alternate search between user-specified and activity-based one when the\n"
  "     search is restarted. Starts by the user-specified search. Default restart\n"
  "     base is used, unless overwritten. (Default " << (def.toggle_vsids ? "on" : "off") << ").\n"
  "  --switch-to-vsids-after <n>\n"
  "     Search starts with the user-specified one and switches to the\n"
  "     activity-based one after a specified number of conflicts\n"
  "     (default " << def.switch_to_vsids_after << ").\n"
  "  --branch-random [on|off], --no-branch-random\n"
  "     Use random variable selection for tie breaking instead of input order (default " << (def.branch_random ? "on" : "off") << ").\n"
  "  --sat-polarity <n>\n"
  "     Selection of the polarity of Boolean variables\n"
  "     (0 = default, 1 = same, 2 = anti, 3 = random) (default " << def.sat_polarity << ").\n"
  "\n"
  "Learning Options:\n"
  "  --lazy [on|off], --no-lazy\n"
  "     Allow clause generation for domain updates (default " << (def.lazy ? "on" : "off") << ").\n"
  "  --finesse [on|off], --no-finesse\n"
  "     Try to generated stronger clauses (default " << (def.finesse ? "on" : "off") << ").\n"
  "  --learn [on|off], --no-learn\n"
  "     Compute nogoods when a conflict is encountered (default " << (def.learn ? "on" : "off") << ").\n"
#if PHASE_SAVING
  "  --phase-saving <n>\n"
  "     Repeat same Boolean variable polarity (0 = no, 1 = recent, 2 = always)\n"
  "     (default: " << def.phase_saving << ").\n"
#endif
  "  --eager-limit <n>\n"
  "     The maximal domain size of Integer variables for which the entire Boolean\n"
  "     variables' representation is created upfront (default " << def.eager_limit << ").\n"
  "     The Boolean variables' representation for Integer variables with larger\n"
  "     domain size will be created on demand (lazily).\n"
  "  --sat-var-limit <n>\n"
  "     The maximal number of Boolean variables (default " << def.sat_var_limit << ").\n"
  "  --n-of-learnts <n>\n"
  "     The maximal number of learnt clauses (default " << def.nof_learnts << ").\n"
  "     If this number is reached then some learnt clauses will be deleted.\n"
  "  --learnts-mlimit <n>\n"
  "     The maximal memory limit for learnt clauses in Bytes (default " << def.learnts_mlimit << ").\n"
  "     If the limit is reached then some learnt clauses will be deleted.\n"
  "  --sort-learnt-level [on|off], --no-sort-learnt-level\n"
  "     Sort literals in a learnt clause based on their decision level\n"
  "     (default " << (def.sort_learnt_level ? "on" : "off") << ").\n"
  "  --one-watch [on|off], --no-one-watch\n"
  "     Watch only one literal in a learn clause (default " << (def.one_watch ? "on" : "off") << ").\n"
  "  --bin-clause-opt [on|off], --no-bin-clause-opt\n"
  "     Optimise learnt clauses of length 2 (default " << (def.bin_clause_opt ? "on" : "off") << ").\n"
  "\n"
  "Introduced Variable Options:\n"
  "  --introduced-heuristic [on|off], --no-introduced-heuristic\n"
  "     Use a simple heuristic on the variable names for deciding whether a\n"
  "     variable was introduced by MiniZinc (default " << (def.introduced_heuristic ? "on" : "off") << ").\n"
  "  --use-var-is-introduced [on|off], --no-use-var-is-introduced\n"
  "     Use the FlatZinc annotation var_is_introduced for deciding whether a\n"
  "     variable was introduce by MiniZinc (default " << (def.use_var_is_introduced ? "on" : "off") << ").\n"
  "  --exclude-introduced [on|off], --no-exclude-introduced\n"
  "     Exclude introduced variables and their derived internal variables from\n"
  "     learnt clauses (default " << (def.exclude_introduced ? "on" : "off") << ").\n"
  "  --decide-introduced [on|off], --no-decide-introduced\n"
  "     Allow search decisions on introduced variables and their derived internal variables\n"
  "     (default " << (def.decide_introduced ? "on" : "off") << ").\n"
  "\n"
  "Pre-Processing Options:\n"
  "  --fd-simplify [on|off], --no-fd-simplify\n"
  "     Removal of FD propagators that are satisfied globally (default " << (def.fd_simplify ? "on" : "off") << ").\n"
  "  --sat-simplify [on|off], --no-sat-simplify\n"
  "     Removal of clauses that are satisfied globally default " << (def.sat_simplify ? "on" : "off") << ").\n"
  "\n"
#ifdef PARALLEL
  "Parallel Options:\n"
  "  --parallel [on|off], --no-parallel\n"
  "     Run Chuffed in parallel mode (default " << (def.parallel ? "on" : "off") << ").\n"
  "  -p <n>\n"
  "     Number of CPU cores in the machine (default " << def.num_cores << ").\n"
  "  --share-param <n>\n"
  "     Default: " << def.share_param << "\n"
  "  --bandwidth <n>\n"
  "     The total number of literals that can be shared between all threads per second\n"
  "     (default " << def.bandwidth << ").\n"
  "  --trial-size <n>\n"
  "     The maximal number of clauses on trial, i.e., temporary immune for pruning\n"
  "     (default " << def.trial_size << ").\n"
  "  --share-act <n>\n"
  "     How to share clause activities between threads (0 = none, 1 = act, 2 = react)\n"
  "     (default " << def.share_act << ").\n"
  "\n"
#endif
  "Propagator Options:\n"
  "  --cumu-global [on|off], --no-cumu-global\n"
  "     Use the global cumulative propagator if possible (default " << (def.cumu_global ? "on" : "off") << ").\n"
  "  --disj-edge-find [on|off], --no-disj-edge-find\n"
  "     Use the edge-finding propagator for disjunctive constraints (default " << (def.disj_edge_find ? "on" : "off") << ").\n"
  "  --disj-set-bp [on|off], --no-disj-set-bp\n"
  "     Use the set bounds propagator for disjunctive constraints (default " << (def.disj_set_bp ? "on" : "off") << ").\n"
  "  --mdd [on|off], --no-mdd\n"
  "     Use the MDD propagator if possible (default " << (def.mdd ? "on" : "off") << ").\n"
  "  --mip [on|off], --no-mip\n"
  "     Use the MIP propagator if possible (default " << (def.mip ? "on" : "off") << ").\n"
  "  --mip-branch [on|off], --no-mip-branch\n"
  "     Use MIP branching as the branching strategy (default " << (def.mip_branch ? "on" : "off") << ").\n"
  "\n"
  "Symmetry Breaking Options:\n"
  "  (only one of these can be chosen)\n"
  "  --sym-static [on|off], --no-sym-static\n"
  "     Use static symmetry breaking constraints (default " << (def.sym_static ? "on" : "off") << ").\n"
  "  --ldsb [on|off], --no-ldsb\n"
  "     Use lightweight dynamic symmetry breaking constraints \"1UIP crippled\"\n"
  "     (default " << (def.ldsb ? "on" : "off") << ").\n"
  "  --ldsbta [on|off], --no-ldsbta\n"
  "     Use lightweight dynamic symmetry breaking constraints \"1UIP\"\n"
  "     (default " << (def.ldsbta ? "on" : "off") << ").\n"
  "  --ldsbad [on|off], --no-ldsbad\n"
  "     Use lightweight dynamic symmetry breaking constraints \"all decision clause\"\n"
  "     (default " << (def.ldsbad ? "on" : "off") << ").\n"
#ifdef HAS_PROFILER
  "\n"
  "More Profiler Options:\n"
  "  --print-nodes [on|off], --no-print-nodes\n"
  "     Print search nodes to the node log file (default " << (def.print_nodes ? "on" : "off") << ").\n"
  "  --print-implications [on|off], --no-print-implications\n"
  "     Print implications encountered during conflict analysis to the implication\n"
  "     log file (default " << (def.print_implications ? "on" : "off") << ").\n"
  "  --print-variable-list [on|off], --no-print-variable-list\n"
  "     Print a variable list to a file (default " << (def.print_variable_list ? "on" : "off") << ").\n"
#endif
  // TODO Description f the listed options below
  //  "  --send-skipped [on|off], --no-send-skipped\n"
  //  "     <Description> (default " << (def.send_skipped ? "on" : "off") << ").\n"
  //  "  --filter-domains <string>\n"
  //  "     <Description> (default " << def.filter_domains << ").\n"
  //  "  --learnt-stats [on|off], --no-learn-stats\n"
  //  "     <Description> (default " << (def.learnt_stats ? "on" : "off") << ").\n"
  //  "  --learnt-stats-nogood [on|off], --no-learn-stats-nogood\n"
  //  "     <Description> (default " << (def.learnt_stats_nogood ? "on" : "off") << ").\n"
  //  "  --debug [on|off], --no-debug\n"
  //  "     <Description> (default " << (def.debug ? "on" : "off") << ").\n"
  //  "  --exhaustive-activity [on|off], --no-exhaustive-activity\n"
  //  "     <Description> (default " << (def.exhaustive_activity ? "on" : "off") << ").\n"
  //  "  --lang-ext-linear [on|off], --no-lang-ext-linear\n"
  //  "     <Description> (default " << (def.lang_ext_linear ? "on" : "off") << ").\n"
  //  "  --well-founded [on|off], --no-well-founded\n"
  //  "     <Description> (default " << (def.well_founded ? "on" : "off") << ").\n"
  ;
}

void parseOptions(int& argc, char**& argv, std::string* fileArg, const std::string& fileExt) {
  
  int j=1;
  for (int i=1; i<argc; i++) {
    CLOParser cop(i,argc,argv);
    int intBuffer;
    bool boolBuffer;
    std::string stringBuffer;
    if (cop.get("-h --help")) {
      printHelp(argc,argv,fileExt);
      std::exit(EXIT_SUCCESS);
    }
    if (cop.get("--help-all")) {
      printLongHelp(argc,argv,fileExt);
      std::exit(EXIT_SUCCESS);
    }
    if (cop.get("-n --n-of-solutions", &intBuffer)) {
      so.nof_solutions = intBuffer;
    } else if (cop.get("-t --time-out", &intBuffer)) {
      // TODO: Remove warning when appropriate
      std::cerr << "WARNING: the --time-out flag has recently been changed."
                << "The time-out is now provided in milliseconds instead of seconds"
                << std::endl;
      so.time_out = duration(intBuffer);
    } else if (cop.get("-r --rnd-seed", &intBuffer)) {
      so.rnd_seed = intBuffer;
    } else if (cop.getBool("-v --verbose", boolBuffer)) {
      so.verbosity = boolBuffer;
    } else if (cop.get("--verbosity", &intBuffer)) {
      so.verbosity = intBuffer;
    } else if (cop.getBool("--print-sol", boolBuffer)) {
      so.print_sol = boolBuffer;
    } else if (cop.get("--restart", &stringBuffer)) {
      if (stringBuffer == "chuffed") {
        so.restart_type = CHUFFED_DEFAULT;
      } else if (stringBuffer == "none") {
        so.restart_type = NONE;
      } else if (stringBuffer == "constant") {
        so.restart_type = CONSTANT;
      } else if (stringBuffer == "linear") {
        so.restart_type = LINEAR;
      } else if (stringBuffer == "luby") {
        so.restart_type = LUBY;
      } else if (stringBuffer == "geometric") {
        so.restart_type = GEOMETRIC;
      } else {
        std::cerr << argv[0] << ": Unknown restart strategy " << stringBuffer
                  << ". Chuffed will use its default strategy.\n";
      }
      so.restart_type_override = false;
    } else if (cop.get("--restart-scale", &intBuffer)) {
      so.restart_scale = static_cast<unsigned int>(intBuffer);
      so.restart_scale_override = false;
    } else if (cop.get("--restart-base", &stringBuffer)) {
      // TODO: Remove warning when appropriate
      std::cerr << "WARNING: the --restart-base flag has recently been changed."
                << "The old behaviour of \"restart base\" is now implemented by --restart-scale."
                << std::endl;
      so.restart_base = stod(stringBuffer);
      if (so.restart_base < 1.0) {
        CHUFFED_ERROR("Illegal restart base. Restart count will converge to zero.");
      }
      so.restart_base_override = false;
    } else if (cop.getBool("--toggle-vsids", boolBuffer)) {
      so.toggle_vsids = boolBuffer;
    } else if (cop.getBool("--branch-random", boolBuffer)) {
      so.branch_random = boolBuffer;
    } else if (cop.get("--switch-to-vsids-after", &intBuffer)) {
      so.switch_to_vsids_after = intBuffer;
    } else if (cop.get("--sat-polarity", &intBuffer)) {
      so.sat_polarity = intBuffer;
    } else if (cop.getBool("--prop-fifo", boolBuffer)) {
      so.prop_fifo = boolBuffer;
    } else if (cop.getBool("--disj-edge-find", boolBuffer)) {
      so.disj_edge_find = boolBuffer;
    } else if (cop.getBool("--disj-set-bp", boolBuffer)) {
      so.disj_set_bp = boolBuffer;
    } else if (cop.getBool("--cumu-global", boolBuffer)) {
      so.cumu_global = boolBuffer;
    } else if (cop.getBool("--sat-simplify", boolBuffer)) {
      so.sat_simplify = boolBuffer;
    } else if (cop.getBool("--fd-simplify", boolBuffer)) {
      so.fd_simplify = boolBuffer;
    } else if (cop.getBool("--lazy", boolBuffer)) {
      so.lazy = boolBuffer;
    } else if (cop.getBool("--finesse", boolBuffer)) {
      so.finesse = boolBuffer;
    } else if (cop.getBool("--learn", boolBuffer)) {
      so.learn = boolBuffer;
    } else if (cop.getBool("--vsids", boolBuffer)) {
      so.vsids = boolBuffer;
    } else if (cop.getBool("--sort-learnt-level", boolBuffer)) {
      so.sort_learnt_level = boolBuffer;
    } else if (cop.getBool("--one-watch", boolBuffer)) {
      so.one_watch = boolBuffer;
    } else if (cop.getBool("--exclude-introduced", boolBuffer)) {
      so.exclude_introduced = boolBuffer;
    } else if (cop.getBool("--decide-introduced", boolBuffer)) {
      so.decide_introduced = boolBuffer;
    } else if (cop.getBool("--introduced-heuristic", boolBuffer)) {
      so.introduced_heuristic = boolBuffer;
    } else if (cop.getBool("--use-var-is-introduced", boolBuffer)) {
      so.use_var_is_introduced = boolBuffer;
    } else if (cop.getBool("--print-nodes", boolBuffer)) {
      so.print_nodes = boolBuffer;
    } else if (cop.getBool("--print-variable-list", boolBuffer)) {
      so.print_variable_list = boolBuffer;
    } else if (cop.getBool("--print-implications", boolBuffer)) {
      so.print_implications = boolBuffer;
    } else if (cop.getBool("--send-skipped", boolBuffer)) {
      so.send_skipped = boolBuffer;
    } else if (cop.get("--filter-domains", &stringBuffer)) {
      so.filter_domains = stringBuffer;
    } else if (cop.getBool("--learnt-stats", boolBuffer)) {
      so.learnt_stats = boolBuffer;
    } else if (cop.getBool("--learnt-stats-nogood", boolBuffer)) {
      so.learnt_stats_nogood = boolBuffer;
    } else if (cop.getBool("--debug", boolBuffer)) {
      so.debug = boolBuffer;
    } else if (cop.getBool("--exhaustive-activity", boolBuffer)) {
      so.exhaustive_activity = boolBuffer;
    } else if (cop.getBool("--bin-clause-opt", boolBuffer)) {
      so.bin_clause_opt = boolBuffer;
    } else if (cop.get("--eager-limit", &intBuffer)) {
      so.eager_limit = intBuffer;
    } else if (cop.get("--sat-var-limit", &intBuffer)) {
      so.sat_var_limit = intBuffer;
    } else if (cop.get("--n-of-learnts", &intBuffer)) {
      so.nof_learnts = intBuffer;
    } else if (cop.get("--learnts-mlimit", &intBuffer)) {
      so.learnts_mlimit = intBuffer;
    } else if (cop.getBool("--lang-ext-linear", boolBuffer)) {
      so.lang_ext_linear = boolBuffer;
    } else if (cop.getBool("--mdd", boolBuffer)) {
      so.mdd = boolBuffer;
    } else if (cop.getBool("--mip", boolBuffer)) {
      so.mip = boolBuffer;
    } else if (cop.getBool("--mip-branch", boolBuffer)) {
      so.mip_branch = boolBuffer;
    } else if (cop.getBool("--sym-static", boolBuffer)) {
      so.sym_static = boolBuffer;
    } else if (cop.getBool("--ldsb", boolBuffer)) {
      so.ldsb = boolBuffer;
    } else if (cop.getBool("--ldsbta", boolBuffer)) {
      so.ldsbta = boolBuffer;
    } else if (cop.getBool("--ldsbad", boolBuffer)) {
      so.ldsbad = boolBuffer;
    } else if (cop.getBool("--well-founded", boolBuffer)) {
      so.well_founded = boolBuffer;
#ifdef PARALLEL
    } else if (cop.getBool("--parallel", boolBuffer)) {
      so.parallel = boolBuffer;
    } else if (cop.get("--share-param", &intBuffer)) {
      so.share_param = intBuffer;
    } else if (cop.get("--bandwidth", &intBuffer)) {
      so.bandwidth = intBuffer;
    } else if (cop.get("--trial-size", &intBuffer)) {
      so.trial_size = intBuffer;
    } else if (cop.get("--share-act", &intBuffer)) {
      so.share_act = intBuffer;
#endif
    } else if (cop.get("-a")) {
      so.nof_solutions = 0;
    } else if (cop.get("-f")) {
      so.toggle_vsids = true;
      so.restart_scale = 100;
    } else if (cop.get("-p", &intBuffer)) {
      so.parallel = true;
      so.num_cores = intBuffer;
    } else if (cop.get("-s -S")) {
      so.verbosity = 1;
#ifdef HAS_PROFILER
    } else if (cop.get("--cp-profiler", &stringBuffer)) {
      std::stringstream ss(stringBuffer);
      char sep;
      ss >> so.cpprofiler_id >> sep >> so.cpprofiler_port;
      if (sep == ',' && ss.eof()) {
        so.cpprofiler_enabled = true;
      } else {
        CHUFFED_ERROR("Invalid value for --cp-profiler.");
      }
#endif
    } else if (argv[i][0] == '-') {
      std::cerr << argv[0] << ": unrecognized option " << argv[i] << "\n";
      std::cerr << argv[0] << ": use --help for more information.\n";
      std::exit(EXIT_FAILURE);
    } else  {
      argv[j++] = argv[i];
    }
    
  }
  
  argc = j;
  
  if (fileArg != NULL) {
    if (argc==2) {
      std::string filename(argv[1]);
      if (fileExt.size() > 0) {
        if (filename.size() <= fileExt.size()+1 || filename.substr(filename.size()-fileExt.size()-1)!="."+fileExt) {
          std::cerr << argv[0] << ": cannot handle file extension for " << filename << "\n";
          std::cerr << argv[0] << ": use --help for more information.\n";
          std::exit(EXIT_FAILURE);
        }
      }
      *fileArg = filename;
      --argc;
    } else if (argc>2) {
      std::cerr << argv[0] << ": more than one file argument not supported\n";
      std::cerr << argv[0] << ": use --help for more information.\n";
      std::exit(EXIT_FAILURE);
    }
  }
  
  rassert(so.sym_static + so.ldsb + so.ldsbta + so.ldsbad <= 1);
  
  if (so.ldsbta || so.ldsbad) so.ldsb = true;
  if (so.ldsb) rassert(so.lazy);
  if (so.mip_branch) rassert(so.mip);
  if (so.vsids) engine.branching->add(&sat);
  
  if (so.learnt_stats_nogood) so.learnt_stats = true;
  
#ifndef PARALLEL
  if (so.parallel) {
    fprintf(stderr, "Parallel solving not supported! Please recompile with PARALLEL=true.\n");
    rassert(false);
  }
#endif
  
}
