#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/core/sat.h"
#include "chuffed/flatzinc/flatzinc.h"
#include "chuffed/support/vec.h"

#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <iostream>
#include <ostream>
#include <sstream>
#include <string>

std::stringstream output_buffer;

#ifdef WIN32
/// Handler for catching Ctrl-C
static BOOL SIGINT_handler(DWORD t) throw() {
	if (t == CTRL_C_EVENT) {
		fprintf(stderr, "*** INTERRUPTED ***\n");
		// Flush last solution
		if (engine.opt_var && so.nof_solutions != 0) {
			std::cout << output_buffer.str();
		}
		if (so.verbosity >= 1) {
			engine.printStats();
		}
		SetConsoleCtrlHandler((PHANDLER_ROUTINE)SIGINT_handler, false);
	}
	return false;
}
#else
/// Handler for catching Ctrl-C
void SIGINT_handler(int signum) {
	fprintf(stderr, "*** INTERRUPTED ***\n");
	// Flush last solution
	if ((engine.opt_var != nullptr) && so.nof_solutions != 0) {
		std::cout << output_buffer.str();
	}
	if (so.verbosity >= 1) {
		engine.printStats();
	}
	signal(SIGINT, SIG_DFL);
	raise(SIGINT);
}
#endif

const char* irel_str[] = {" = ", " != ", " <= ", " > "};

std::string get_bv_string(const BoolView& b, bool tryIntDom) {
	std::string s;

	if (tryIntDom) {
		// Alternate version: prioritise intvars.
		Lit l(b.getLit(true));
		ChannelInfo ci(sat.c_info[var(l)]);
		s = intVarString[engine.vars[ci.cons_id]];
		if (ci.cons_type == 1 && !s.empty()) {
			// Int literal
			std::stringstream ss;
			ss << s;
			ss << irel_str[2 * ci.cons_type + static_cast<int>(b.getSign())];
			ss << ci.val;
			return ss.str();
		}
		s = boolVarString[b];
		if (s.empty()) {
			BoolView o(b);
			o.setSign(!o.getSign());
			std::string ostring = boolVarString[o];
			if (!ostring.empty()) {
				s = "~ " + ostring;
			} else {
				s = "<UNKNOWN>";
			}
		}
		return s;

	}  // See if b or ~b have names.
	std::string bvstring = boolVarString[b];
	if (bvstring.empty()) {
		BoolView o(b);
		o.setSign(!o.getSign());
		std::string ostring = boolVarString[o];
		if (ostring.empty()) {
			// Maybe it's attached to a (named) intvar.
			Lit l(b.getLit(true));
			ChannelInfo ci(sat.c_info[var(l)]);
			std::string ivstring = intVarString[engine.vars[ci.cons_id]];
			if (ci.cons_type == 1 && !ivstring.empty()) {
				// If it is, return the denotation of b.
				std::stringstream ss;
				ss << ivstring;
				ss << irel_str[2 * ci.cons_type + static_cast<int>(b.getSign())];
				ss << ci.val;
				return ss.str();
			}
			return "<UNKNOWN>";
		}
		return "~ " + ostring;
	}
	return bvstring;
}

int main(int argc, char** argv) {
	try {
		// Make a copy of the arguments for posterity.
		std::string commandLine;
		for (int i = 0; i < argc; i++) {
			if (i > 0) {
				commandLine += " ";
			}
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
		SetConsoleCtrlHandler((PHANDLER_ROUTINE)SIGINT_handler, true);
#else
		// TODO: Make signal handler use C linkage
		std::signal(SIGINT, SIGINT_handler);  // NOLINT(bugprone-signal-handler)
#endif

		engine.set_assumptions(FlatZinc::s->assumptions);
		if (engine.opt_var != nullptr && so.nof_solutions != 0) {
			engine.setOutputStream(output_buffer);
			engine.solve(FlatZinc::s, commandLine);
			std::cout << output_buffer.str();
		} else {
			engine.solve(FlatZinc::s, commandLine);
		}

		if (engine.status == RES_LUN) {
			vec<BoolView> ng;
			Engine::retrieve_assumption_nogood(ng);
			std::cout << "% [";
			if (ng.size() > 0) {
				std::cout << get_bv_string(ng[0], so.assump_int);
				for (int ii = 1; ii < ng.size(); ii++) {
					std::cout << ", " << get_bv_string(ng[ii], so.assump_int);
				}
			}
			std::cout << "]" << '\n';
		}
	} catch (const std::exception& e) {
		std::cerr << e.what() << '\n';
		std::exit(EXIT_FAILURE);
	} catch (const FlatZinc::Error& e) {
		std::cerr << e.toString() << '\n';
		std::exit(EXIT_FAILURE);
	} catch (...) {
		std::cerr << "  UNKNOWN EXCEPTION." << '\n';
		std::exit(EXIT_FAILURE);
	}
	return 0;
}
