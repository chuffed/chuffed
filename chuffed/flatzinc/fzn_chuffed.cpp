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
