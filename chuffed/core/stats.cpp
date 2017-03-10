#include <cstdio>
#include <cassert>
#include <chuffed/core/options.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/sat.h>
#include <chuffed/parallel/parallel.h>
#include <chuffed/mip/mip.h>
#include <chuffed/ldsb/ldsb.h>


void Engine::printStats() {
	if (so.thread_no != -1) return;

	search_time = wallClockTime() - start_time - init_time;

	if (so.verbosity >= 2) {
		int nl = 0, el = 0, ll = 0;
		for (int i = 0; i < vars.size(); i++) {
			switch (vars[i]->getType()) {
				case INT_VAR: nl++; break;
				case INT_VAR_EL: el++; break;
				case INT_VAR_LL: ll++; break;
				case INT_VAR_SL: el++; break;
				default: NEVER;
			}
		}

		fprintf(stderr, "%d vars (%d no lits, %d eager lits, %d lazy lits)\n", vars.size(), nl, el, ll);
		fprintf(stderr, "%d propagators\n", propagators.size());
		fprintf(stderr, "%lld conflicts\n", conflicts);
		fprintf(stderr, "%lld nodes\n", nodes);
		fprintf(stderr, "%lld propagations\n", propagations);
		fprintf(stderr, "%lld solutions\n", solutions);
		fprintf(stderr, "%.2f seconds init time\n", init_time);
		if (opt_var) fprintf(stderr, "%.2f seconds opt time\n", opt_time);
		fprintf(stderr, "%.2f seconds search time\n", search_time);
		fprintf(stderr, "%.2fMb base memory usage\n", base_memory);
		fprintf(stderr, "%.2fMb trail memory usage\n", trail.capacity() * sizeof(TrailElem) / 1048576.0);
		fprintf(stderr, "%.2fMb peak memory usage\n", memUsed());
        fprintf(stderr, "%d random seed used\n", so.rnd_seed);
		if (so.ldsb) fprintf(stderr, "%.2f seconds ldsb time\n", ldsb.ldsb_time);
		if (so.parallel) master.printStats();
		fprintf(stderr, "\n");
		sat.printStats();
		/* sat.printLearntStats(); */
		if (so.mip) mip->printStats();
		for (int i = 0; i < engine.propagators.size(); i++)
			engine.propagators[i]->printStats();
	}
	else {
		if (engine.opt_var != NULL) fprintf(stderr, "%d,", best_sol);
		fprintf(stderr, "%d,%d,%d,%lld,%lld,%lld,%lld,%.2f,%.2f\n", vars.size(), sat.nVars(), propagators.size(), conflicts, sat.back_jumps, propagations, solutions, init_time, search_time);
	}
}

void Engine::checkMemoryUsage() {
	fprintf(stderr, "%d int vars, %d sat vars, %d propagators\n", vars.size(), sat.nVars(), propagators.size());
	fprintf(stderr, "%.2fMb memory usage\n", memUsed());

	fprintf(stderr, "Size of IntVars: %d %d %d\n", static_cast<int>(sizeof(IntVar)), static_cast<int>(sizeof(IntVarEL)), static_cast<int>(sizeof(IntVarLL)));
	fprintf(stderr, "Size of Propagator: %d\n", static_cast<int>(sizeof(Propagator)));

	long long var_mem = 0;
	for (int i = 0; i < vars.size(); i++) {
		var_mem += sizeof(IntVarLL);
/*
		var_mem += vars[i]->sz;
		if (vars[i]->getType() == INT_VAR_LL) {
			var_mem += 24 * ((IntVarLL*) vars[i])->ld.size();
		}
*/
	}
	fprintf(stderr, "%lld bytes used by vars\n", var_mem);

	long long prop_mem = 0;
	for (int i = 0; i < propagators.size(); i++) {
		prop_mem += sizeof(*propagators[i]);
	}
	fprintf(stderr, "%lld bytes used by propagators\n", prop_mem);
/*
	long long var_range_sum = 0;
	for (int i = 0; i < vars.size(); i++) {
		var_range_sum += vars[i]->max - vars[i]->min;
	}
	fprintf(stderr, "%lld range sum in vars\n", var_range_sum);
*/
	long long clause_mem = 0;
	for (int i = 0; i < sat.clauses.size(); i++) {
		clause_mem += sizeof(Lit) * sat.clauses[i]->size();
	}
	fprintf(stderr, "%lld bytes used by sat clauses\n", clause_mem);
/*
	int constants, hundred, thousand, large;
	constants = hundred = thousand = large = 0;
	for (int i = 0; i < vars.size(); i++) {
		int sz = vars[i]->max - vars[i]->min;
		if (sz == 0) constants++;
		else if (sz <= 100) hundred++;
		else if (sz <= 1000) thousand++;
		else large++;
	}
	fprintf(stderr, "Int sizes: %d %d %d %d\n", constants, hundred, thousand, large);
*/
}
