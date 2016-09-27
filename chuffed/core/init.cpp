#include <cstdio>
#include <cassert>
#include <signal.h>
#include <iostream>
#include <chuffed/core/options.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/sat.h>
#include <chuffed/core/propagator.h>
#include <chuffed/branching/branching.h>
#include <chuffed/mip/mip.h>
#include <chuffed/parallel/parallel.h>
#include <chuffed/ldsb/ldsb.h>

void process_ircs();

void SIGINT_handler(int signum) {
	if (so.thread_no == -1) fprintf(stderr, "*** INTERRUPTED ***\n");
	engine.printStats();
	exit(1);
}

void Engine::init() {
	signal(SIGINT,SIGINT_handler);
	//	signal(SIGHUP,SIGINT_handler);

	if (so.parallel) master.initMPI();

	// Get the vars ready

	for (int i = 0; i < vars.size(); i++) {
		IntVar *v = vars[i];
		if (v->pinfo.size() == 0) v->in_queue = true;
		else v->pushInQueue();
	}

	if (so.lazy) {
		for (int i = 0; i < vars.size(); i++) {
			if (vars[i]->getMax() - vars[i]->getMin() <= so.eager_limit) {
				vars[i]->specialiseToEL();
			} else {
                            std::cerr << "using lazy literal\n";
				vars[i]->specialiseToLL();
			}
		}
	} else {
		for (int i = 0; i < vars.size(); i++) vars[i]->initVals(true);
	}

	// Get the propagators ready

	process_ircs();

	// Get well founded propagators ready

	wf_init();

	// Get MIP propagator ready

	if (so.mip) mip->init();

	// Get SAT propagator ready

	sat.init();

	// Set lits allowed to be in learnt clauses
	problem->restrict_learnable();

	// Get LDSB ready

	if (so.ldsb) ldsb.init();

	// Do MIP presolve

	if (so.mip) mip->presolve();

	// Ready

	finished_init = true;
}
