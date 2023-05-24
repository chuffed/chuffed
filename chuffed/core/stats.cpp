#include <chuffed/core/engine.h>
#include <chuffed/core/options.h>
#include <chuffed/core/sat.h>
#include <chuffed/ldsb/ldsb.h>
#include <chuffed/mip/mip.h>

#include <cassert>
#include <cstdio>

void Engine::printStats() {
	auto total_time = std::chrono::duration_cast<duration>(chuffed_clock::now() - start_time);
	duration search_time = total_time - init_time;

	// MiniZinc standard statistics
	printf("%%%%%%mzn-stat: nodes=%lld\n", nodes);
	printf("%%%%%%mzn-stat: failures=%lld\n", conflicts);
	printf("%%%%%%mzn-stat: restarts=%d\n", restart_count);
	printf("%%%%%%mzn-stat: variables=%d\n", vars.size() + sat.nVars());
	printf("%%%%%%mzn-stat: intVars=%d\n", vars.size());
	printf("%%%%%%mzn-stat: boolVariables=%d\n", sat.nVars() - 2);  // Do not count constant
																																	// True/False
	//    printf("%%%%%%mzn-stat: floatVariables=%d\n", );
	//    printf("%%%%%%mzn-stat: setVariables=%d\n", );
	printf("%%%%%%mzn-stat: propagators=%d\n", propagators.size());
	printf("%%%%%%mzn-stat: propagations=%lld\n", propagations);
	printf("%%%%%%mzn-stat: peakDepth=%d\n", peak_depth);
	printf("%%%%%%mzn-stat: nogoods=%lld\n",
				 conflicts);  // TODO: Is this correct (e.g., sat.learnts.size())
	printf("%%%%%%mzn-stat: backjumps=%lld\n", sat.back_jumps);
	printf("%%%%%%mzn-stat: peakMem=%.2f\n", memUsed());
	printf("%%%%%%mzn-stat: time=%.3f\n", to_sec(total_time));
	printf("%%%%%%mzn-stat: initTime=%.3f\n", to_sec(init_time));
	printf("%%%%%%mzn-stat: solveTime=%.3f\n", to_sec(search_time));

	// Chuffed specific statistics
	if (opt_var != nullptr) {
		printf("%%%%%%mzn-stat: objective=%d\n", best_sol);
		printf("%%%%%%mzn-stat: optTime=%.3f\n", to_sec(opt_time));
	}
	printf("%%%%%%mzn-stat: baseMem=%.2f\n", base_memory);
	printf("%%%%%%mzn-stat: trailMem=%.2f\n", trail.capacity() * sizeof(TrailElem) / 1048576.0);
	printf("%%%%%%mzn-stat: randomSeed=%d\n", so.rnd_seed);

	if (so.verbosity >= 2) {
		int nl = 0;
		int el = 0;
		int ll = 0;
		int sl = 0;
		for (int i = 0; i < vars.size(); i++) {
			switch (vars[i]->getType()) {
				case INT_VAR:
					nl++;
					break;
				case INT_VAR_EL:
					el++;
					break;
				case INT_VAR_LL:
					ll++;
					break;
				case INT_VAR_SL:
					sl++;
					break;
				default:
					NEVER;
			}
		}
		printf("%%%%%%mzn-stat: noLitIntVars=%d\n", nl);
		printf("%%%%%%mzn-stat: eagerLitIntVars=%d\n", el);
		printf("%%%%%%mzn-stat: lazyLitIntVars=%d\n", ll);
		printf("%%%%%%mzn-stat: sparseLitIntVars=%d\n", sl);
		printf("%%%%%%mzn-stat: solutions=%lld\n", solutions);

		if (so.ldsb) {
			printf("%%%%%%mzn-stat: ldsbTime=%.3f\n", to_sec(ldsb.ldsb_time));
		}
		sat.printStats();
		/* sat.printLearntStats(); */
		if (so.mip) {
			mip->printStats();
		}
		for (int i = 0; i < engine.propagators.size(); i++) {
			engine.propagators[i]->printStats();
		}
	}
	printf("%%%%%%mzn-stat-end\n");
}

void Engine::checkMemoryUsage() {
	fprintf(stderr, "%d int vars, %d sat vars, %d propagators\n", vars.size(), sat.nVars(),
					propagators.size());
	fprintf(stderr, "%.2fMb memory usage\n", memUsed());

	fprintf(stderr, "Size of IntVars: %d %d %d\n", static_cast<int>(sizeof(IntVar)),
					static_cast<int>(sizeof(IntVarEL)), static_cast<int>(sizeof(IntVarLL)));
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
