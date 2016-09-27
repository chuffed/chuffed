
#include <chuffed/core/options.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/sat.h>

#include <iostream>

Options so;

Options::Options() :
		nof_solutions(1)
	, time_out(1800)
	, rnd_seed(0)
	, verbosity(0)
	, print_sol(true)
	, restart_base(1000000000)

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
        , use_profiler(false)
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
      } else if (buffer=="true" || buffer=="1") {
        result = true;
      } else if (buffer=="false" || buffer=="0") {
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
  "     Print this message.\n"
  "  -n <n>, --n-of-solutions <n>\n"
  "     An upper bound on the number of solutions (default " << def.nof_solutions << ").\n"
  "  -p <n>\n"
  "     Number of cores (default " << def.num_cores << ").\n"
  "  -f\n"
  "     Free search. Alternates search between user-specified and activity-based one"
  "     when search is restarted. Restart base is set to 100.\n"
  "  -v, --verbose\n"
  "     Verbose mode (default " << (def.verbosity == 0 ? "off" : "on") << ").\n"
  "  --verbosity <n>\n"
  "     Set verbosity (default " << def.verbosity << ").\n"
  "  --time-out <n>\n"
  "     Time out in seconds (default " << def.time_out << ").\n"
  "  --rnd-seed <n>\n"
  "     Set random seed (default " << def.rnd_seed << ").\n"
#ifdef HAS_PROFILER
  "  --profiling\n"
  "     Send search to CPProfiler (default " << (def.use_profiler ? "on" : "off") << ").\n"
#endif
  "\n"
  "Search Options:\n"
  " --vsids\n"
  "     Use activity-based search on the Boolean literals (default " << (def.vsids ? "on" : "off") << ").\n"
  " --restart-base <n>\n"
  "     Number of conflicts after which the search restarts (default " << def.restart_base << ").\n"
  " --toggle-vsids\n"
  "     Alternate search between user-specified and activity-based one when the search\n"
  "     is restarted. Starts by the user-specified search. Default restart base is used,\n"
  "     unless overwritten. (Default " << (def.toggle_vsids ? "on" : "off") << ").\n"
  " --switch-to-vsids-after <n>\n"
  "     Search starts with the user-specified one and switches to the activity-based one\n"
  "     after a specified number of conflicts (default " << def.switch_to_vsids_after << ").\n"
  " --branch-random\n"
  "     Random variable selection (default " << (def.branch_random ? "on" : "off") << ").\n"
  "\n"
  "Learning Options:\n"
  "  --lazy\n"
  "     Use nogood learning (default " << (def.lazy ? "on" : "off") << ").\n"
//  "  --finesse\n"
//  "     Default: " << (def.finesse ? "on" : "off") << "\n"
//  "  --learn\n"
//  "     Default: " << (def.learn ? "on" : "off") << "\n"
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
    if (cop.get("-n --n-of-solutions", &intBuffer)) {
      so.nof_solutions = intBuffer;
    } else if (cop.get("--time-out", &intBuffer)) {
      so.time_out = intBuffer;
    } else if (cop.get("--rnd-seed", &intBuffer)) {
      so.rnd_seed = intBuffer;
    } else if (cop.getBool("-v --verbose", boolBuffer)) {
      so.verbosity = boolBuffer;
    } else if (cop.get("--verbosity", &intBuffer)) {
      so.verbosity = intBuffer;
    } else if (cop.getBool("--print-sol", boolBuffer)) {
      so.print_sol = boolBuffer;
    } else if (cop.get("--restart-base", &intBuffer)) {
      so.restart_base = intBuffer;
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
#ifdef HAS_PROFILER
    } else if (cop.getBool("--profiling", boolBuffer)) {
      so.use_profiler = boolBuffer;
#endif
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
    } else if (cop.get("--saved-clauses", &intBuffer)) {
      so.saved_clauses = intBuffer;
    } else if (cop.getBool("--use-uiv", boolBuffer)) {
      so.use_uiv = boolBuffer;
    } else if (cop.getBool("--alldiff-cheat", boolBuffer)) {
      so.alldiff_cheat = boolBuffer;
    } else if (cop.getBool("--alldiff-stage", boolBuffer)) {
      so.alldiff_stage = boolBuffer;
    } else if (cop.get("--circuit-alg", &intBuffer)) {
      so.circuitalg = intBuffer;
    } else if (cop.get("--prev-expl", &intBuffer)) {
      so.prevexpl = intBuffer;
    } else if (cop.get("--check-expl", &intBuffer)) {
      so.checkexpl = intBuffer;
    } else if (cop.get("--check-failure", &intBuffer)) {
      so.checkfailure = intBuffer;
    } else if (cop.get("--check-evidence", &intBuffer)) {
      so.checkevidence = intBuffer;
    } else if (cop.get("--prevent-evidence", &intBuffer)) {
      so.preventevidence = intBuffer;
    } else if (cop.get("--scc-evidence", &intBuffer)) {
      so.sccevidence = intBuffer;
    } else if (cop.get("--scc-options", &intBuffer)) {
      so.sccoptions = intBuffer;
    } else if (cop.get("--root-selection", &intBuffer)) {
      so.rootSelection = intBuffer;
    } else if (cop.get("-a")) {
      so.nof_solutions = 0;
    } else if (cop.get("-f")) {
      so.toggle_vsids = true;
      so.restart_base = 100;
    } else if (cop.get("-p", &intBuffer)) {
      so.parallel = true;
      so.num_cores = intBuffer;
    } else if (cop.get("-s -S")) {
      so.verbosity = 1;
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
    if (j==2) {
      std::string filename(argv[1]);
      if (fileExt.size() > 0) {
        if (filename.size() <= fileExt.size()+1 || filename.substr(filename.size()-fileExt.size()-1)!="."+fileExt) {
          std::cerr << argv[0] << ": cannot handle file extension for " << filename << "\n";
          std::cerr << argv[0] << ": use --help for more information.\n";
          std::exit(EXIT_FAILURE);
        }
      }
      *fileArg = filename;
    } else if (j>2) {
      std::cerr << argv[0] << ": more than one file argument not supported\n";
      std::cerr << argv[0] << ": use --help for more information.\n";
      std::exit(EXIT_FAILURE);
    }
  } else {
    if (j != 1) {
      std::cerr << argv[0] << ": unrecognized option " << argv[j] << "\n";
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
