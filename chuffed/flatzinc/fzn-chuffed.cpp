#include <cstdio>
#include <csignal>
#include <cstring>
#include <chuffed/core/options.h>
#include <chuffed/core/engine.h>
#include <chuffed/flatzinc/flatzinc.h>

std::stringstream output_buffer;

#ifdef WIN32
    /// Handler for catching Ctrl-C
    static BOOL SIGINT_handler(DWORD t) throw() {
      if (t == CTRL_C_EVENT) {
				fprintf(stderr, "*** INTERRUPTED ***\n");
				// Flush last solution
				if(engine.opt_var && so.nof_solutions!=0) {
						std::cout << output_buffer.str();
				}
				if (so.verbosity >= 1) {
					engine.printStats();
				}
				SetConsoleCtrlHandler( (PHANDLER_ROUTINE) SIGINT_handler, false);
      }
      return false;
    }
#else
	/// Handler for catching Ctrl-C
	void SIGINT_handler(int signum) {
		fprintf(stderr, "*** INTERRUPTED ***\n");
		// Flush last solution
		if(engine.opt_var && so.nof_solutions!=0) {
				std::cout << output_buffer.str();
		}
		if (so.verbosity >= 1) {
			engine.printStats();
		}
		signal(SIGINT, SIG_DFL);
		raise(SIGINT);
	}
#endif

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
  
  if (argc != 1) {
    std::cerr << argv[0] << ": unrecognized option " << argv[1] << "\n";
    std::cerr << argv[0] << ": use --help for more information.\n";
    std::exit(EXIT_FAILURE);
  }

	if (filename.empty()) {
		FlatZinc::solve(std::cin, std::cerr);
	} else {
		FlatZinc::solve(filename);
	}

	// Install signal handler
#ifdef WIN32
	SetConsoleCtrlHandler( (PHANDLER_ROUTINE) SIGINT_handler, true);
#else
	std::signal(SIGINT, SIGINT_handler);
#endif

  if (engine.opt_var && so.nof_solutions!=0) {
    engine.setOutputStream(output_buffer);
    engine.solve(FlatZinc::s, commandLine);
    std::cout << output_buffer.str();
  } else {
    engine.solve(FlatZinc::s, commandLine);
  }

	return 0;
}
