#include <chuffed/core/assume.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/options.h>
#include <chuffed/core/propagator.h>
#include <chuffed/core/sat.h>
#include <chuffed/ldsb/ldsb.h>

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <fstream>
#include <iostream>

#define PRINT_ANALYSIS 0

std::ofstream implication_stream;

//---------
// inline methods

inline void SAT::learntLenBumpActivity(int l) {
	if (l >= MAX_SHARE_LEN) {
		return;
	}
	if (engine.conflicts % 16 == 0) {
		time_point new_ll_time = chuffed_clock::now();
		auto diff = std::chrono::duration_cast<duration>(new_ll_time - ll_time);
		double factor = exp(to_sec(diff) / learnt_len_el);
		ll_inc *= factor;
		if (ll_inc > 1e100) {
			for (int i = 0; i < MAX_SHARE_LEN; i++) {
				learnt_len_occ[i] *= 1e-100;
			}
			ll_inc *= 1e-100;
		}
		ll_time = new_ll_time;
		confl_rate /= factor;
	}
	learnt_len_occ[l] += ll_inc;
	confl_rate += 1 / learnt_len_el;
}

inline void SAT::varDecayActivity() {
	var_inc *= 1.05;
	if (var_inc > 1e100) {
		for (int i = 0; i < nVars(); i++) {
			activity[i] *= 1e-100;
		}
		for (int i = 0; i < engine.vars.size(); i++) {
			engine.vars[i]->activity *= 1e-100;
		}
		var_inc *= 1e-100;
	}
}

inline void SAT::varBumpActivity(Lit p) {
	int v = var(p);
	if (so.vsids) {
		activity[v] += var_inc;
		if (order_heap.inHeap(v)) {
			order_heap.decrease(v);
		}
		if (so.sat_polarity == 1) {
			polarity[v] = ((static_cast<int>(sign(p)) ^ 1) != 0);
		}
		if (so.sat_polarity == 2) {
			polarity[v] = sign(p);
		}
	}
	if (c_info[v].cons_type == 1) {
		int var_id = c_info[v].cons_id;
		if (!ivseen[var_id]) {
			engine.vars[var_id]->activity += var_inc;
			ivseen[var_id] = true;
			ivseen_toclear.push(var_id);
		}
	}
}

inline void SAT::claDecayActivity() {
	// Increase the increment by 0.1%.  This introduces "activity
	// inflation", making all previous activity counts have less value.
	cla_inc *= 1.001;
	// If inflation has become too much, normalise all the activity
	// counts by scaling everything down by a factor of 1e20.
	if (cla_inc > 1e20) {
		cla_inc *= 1e-20;
		for (int i = 0; i < learnts.size(); i++) {
			learnts[i]->activity() *= 1e-20;
		}
	}
}

//---------
// main methods

Clause* SAT::_getExpl(Lit p) {
	//	fprintf(stderr, "L%d - %d\n", decisionLevel(), trailpos[var(p)]);
	Reason& r = reason[var(p)];
	return engine.propagators[r.d.d2]->explain(p, r.d.d1);
}

Clause* SAT::getConfl(Reason& r, Lit p) const {
	switch (r.d.type) {
		case 0:
			return r.pt;
		case 1:
			return engine.propagators[r.d.d2]->explain(p, r.d.d1);
		default:
			Clause& c = *short_expl;
			c.sz = r.d.type;
			c[1] = toLit(r.d.d1);
			if (c.sz == 3) {
				c[2] = toLit(r.d.d2);
			}
			return short_expl;
	}
}

void SAT::analyze(int nodeid, std::set<int>& contributingNogoods) {
	avg_depth += 0.01 * (decisionLevel() - avg_depth);

	/* if (so.debug) { */
	/*   std::cerr << "trail:\n"; */
	/*   for (int i = 0 ; i < trail.size() ; i++) { */
	/*     std::cerr << "level " << i << ":"; */
	/*     for (int j = 0 ; j < trail[i].size() ; j++) { */
	/*       Lit& lit = trail[i][j]; */
	/*       std::cerr << " " << getLitString(toInt(lit)); */
	/*     } */
	/*     std::cerr << "\n"; */
	/*   } */
	/* } */

	checkConflict();
	varDecayActivity();
	claDecayActivity();
	getLearntClause(nodeid, contributingNogoods);
	explainUnlearnable(contributingNogoods);
	if (so.exhaustive_activity) {
		explainToExhaustion(contributingNogoods);
	}
	clearSeen();

	int btlevel = findBackTrackLevel();
	back_jumps += decisionLevel() - 1 - btlevel;
	//	fprintf(stderr, "btlevel = %d\n", btlevel);
	btToLevel(btlevel);
	confl = nullptr;

	if (so.sort_learnt_level && out_learnt.size() >= 4) {
		std::sort((Lit*)out_learnt + 2, (Lit*)out_learnt + out_learnt.size(), lit_sort);
	}

#if DEBUG_VERBOSE
	std::cerr << "out_learnt:";
	for (int i = 0; i < out_learnt.size(); i++) std::cerr << " " << toInt(out_learnt[i]);
	std::cerr << "\n";
	std::cerr << "out_learnt (interpreted):";
	for (int i = 0; i < out_learnt.size(); i++) std::cerr << " " << litString[toInt(out_learnt[i])];
	std::cerr << "\n";
#endif

	Clause* c = Clause_new(out_learnt, true);
	c->activity() = cla_inc;
	c->rawActivity() = 1;
	c->clauseID() = nodeid;

	learntLenBumpActivity(c->size());

	/* std::cerr << "conflict found clause of length " << c->size() << "\n"; */

	/* if (c->size() == 1) { */
	/*     std::cerr << "learntfact: " << getLitString(toInt((*c)[0])) << "\n"; */
	/* } */

	if (so.learn && c->size() >= 2) {
		addClause(*c, so.one_watch);
	}

	if (!so.learn || (so.bin_clause_opt && c->size() <= 2)) {
		rtrail.last().push(c);
	}

	enqueue(out_learnt[0], (so.bin_clause_opt && c->size() == 2) ? Reason(out_learnt[1]) : c);

	if (PRINT_ANALYSIS) {
		printClause(*c);
	}

	if (so.ldsbad) {
		vec<Lit> out_learnt2;
		out_learnt2.push(out_learnt[0]);
		for (int i = 0; i < decisionLevel(); i++) {
			out_learnt2.push(~decLit(decisionLevel() - i));
		}
		c = Clause_new(out_learnt2, true);
		rtrail.last().push(c);
	}

	if (so.ldsb && !ldsb.processImpl(c)) {
		engine.async_fail = true;
	}

	if (learnts.size() >= so.nof_learnts || learnts_literals >= so.learnts_mlimit / 4) {
		reduceDB();
	}
}

void SAT::getLearntClause(int nodeid, std::set<int>& contributingNogoods) {
	Lit p = lit_Undef;
	int pathC = 0;
	int clevel = findConflictLevel();
	vec<Lit>& ctrail = trail[clevel];
	Clause* expl = confl;
	Reason last_reason = nullptr;

	if (so.debug) {
		std::cerr << "trail of conflict level:";
		for (int i = 0; i < ctrail.size(); i++) {
			std::cerr << " ";
			std::cerr << getLitString(toInt(ctrail[i]));
		}
		std::cerr << "\n";
	}

	index = ctrail.size();
	out_learnt.clear();
	out_learnt_level.clear();
	out_learnt.push();  // (leave room for the asserting literal)
	out_learnt_level.push();

	while (true) {
		assert(expl != nullptr);  // (otherwise should be UIP)
		Clause& c = *expl;

		if (PRINT_ANALYSIS) {
			if (p != lit_Undef) {
				c[0] = p;
			}
			printClause(c);
		}

		if (c.learnt) {
			c.activity() += cla_inc;
			c.rawActivity() += 1;
			contributingNogoods.insert(c.clauseID());
		}

		/* if (so.debug) { */
		/*   if (p == lit_Undef) { */
		/*     std::cerr << "explaining away failure (" << decisionLevel() << ")\n"; */
		/*   } else { */
		/*     std::cerr << "explaining away " << getLitString(toInt(p)) << " (lit number " << toInt(p)
		 * << ", level " << getLevel(var(p)) << ")\n"; */
		/*   } */
		/*   std::cerr << "expl:"; */
		/*   for (int i = (p == lit_Undef ? 0 : 1) ; i < c.size() ; i++) */
		/*     std::cerr << " " << getLitString(toInt(~c[i])); */
		/*   std::cerr << "\n"; */
		/* } */

		if (so.print_implications) {
			if (!implication_stream.is_open()) {
				implication_stream.open("implication-log.csv");
			}

			implication_stream << nodeid;
			implication_stream << ",";
			if (p == lit_Undef) {
				implication_stream << "false";
			} else {
				implication_stream << getLitString(toInt(p));
			}
			implication_stream << ",";
			for (int i = (p == lit_Undef ? 0 : 1); i < c.size(); i++) {
				implication_stream << " " << getLitString(toInt(~c[i]));
			}
			implication_stream << "\n";
		}

		if (so.debug) {
			if (c.learnt) {
				std::cerr << "L" << c.clauseID() << " ";
			}
			std::cerr << "\t";

			if (p == lit_Undef) {
				std::cerr << "false";
			} else {
				std::cerr << getLitString(toInt(p));
			}
			std::cerr << "  <-";
			for (int i = (p == lit_Undef ? 0 : 1); i < c.size(); i++) {
				std::cerr << "  \t" << getLitString(toInt(~c[i]));
			}
			std::cerr << "\n";
		}

		for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++) {
			Lit q = c[j];
			int x = var(q);
			/* if (so.debug) { */
			/*   std::cerr << "adding " << getLitString(toInt(~q)) << " (lit number " << toInt(~q) << ",
			 * var " << x << ") from level " << getLevel(x); */
			/* } */
			if (seen[x] == 0) {
				varBumpActivity(q);
				seen[x] = 1;
				if (isCurLevel(x)) {
					pathC++;
					if (so.debug) {
						std::cerr << getLitString(toInt(~q)) << " is from current level; incremented pathC to "
											<< pathC << "\n";
					}
				} else {
					if (so.debug) {
						std::cerr << "added " << getLitString(toInt(~q)) << " to nogood\n";
					}
					out_learnt.push(q);
					out_learnt_level.push(getLevel(x));
				}
			} else {
				if (so.debug) {
					//                            std::cerr << " but already seen this variable";
					std::cerr << getLitString(toInt(~q)) << " already marked as seen; skipping explanation\n";
				}
			}
			/* if (so.debug) { */
			/*   std::cerr << ", pathC is now " << pathC << "\n"; */
			/* } */
		}

	FindNextExpl:

		assert(pathC > 0);

		// Select next clause to look at:
		while (seen[var(ctrail[--index])] == 0) {
			;
		}
		assert(index >= 0);
		p = ctrail[index];
		seen[var(p)] = 0;
		pathC--;

		if (so.debug) {
			std::cerr << "selected " << getLitString(toInt(p)) << " as next literal to explain away\n";
		}

		if (pathC == 0 && flags[var(p)].uipable) {
			if (so.debug) {
				std::cerr << "one only literal left at current level; finished\n";
			}
			break;
		}

		// This appears to be just an optimisation.
		if (last_reason == reason[var(p)]) {
			if (so.debug) {
				std::cerr << "same reason as previously explained literal; skipping\n";
			}
			goto FindNextExpl;
		}
		last_reason = reason[var(p)];
		expl = getExpl(p);
	}

	out_learnt[0] = ~p;
	out_learnt_level[0] = decisionLevel() - 1;
}

int SAT::findConflictLevel() {
	int tp = -1;
	for (int i = 0; i < confl->size(); i++) {
		int l = trailpos[var((*confl)[i])];
		if (l > tp) {
			tp = l;
		}
	}
	int clevel = engine.tpToLevel(tp);

	if (so.sym_static && clevel == 0) {
		btToLevel(0);
		engine.async_fail = true;
		NOT_SUPPORTED;
		// need to abort analyze as well
		return 0;
	}
	assert(clevel > 0);

	// duplicate conflict clause in case it gets freed
	if (clevel < decisionLevel() && confl->temp_expl) {
		confl = Clause_new(*confl);
		confl->temp_expl = 1;
		rtrail[clevel].push(confl);
	}
	btToLevel(clevel);

	//	fprintf(stderr, "clevel = %d\n", clevel);

	if (PRINT_ANALYSIS) {
		printf("Conflict: level = %d\n", clevel);
	}

	return clevel;
}

void SAT::explainUnlearnable(std::set<int>& contributingNogoods) {
	time_point start = chuffed_clock::now();

	vec<Lit> removed;
	for (int i = 1; i < out_learnt.size(); i++) {
		Lit p = out_learnt[i];
		if (flags[var(p)].learnable) {
			continue;
		}
		assert(!reason[var(p)].isLazy());
		Clause& c = *getExpl(~p);
		removed.push(p);
		out_learnt[i] = out_learnt.last();
		out_learnt.pop();
		out_learnt_level.pop();
		i--;
		for (int j = 1; j < c.size(); j++) {
			Lit q = c[j];
			if (seen[var(q)] == 0) {
				seen[var(q)] = 1;
				out_learnt.push(q);
				out_learnt_level.push(getLevel(var(q)));
			}
		}
	}

	for (int i = 0; i < removed.size(); i++) {
		seen[var(removed[i])] = 0;
	}

	pushback_time += std::chrono::duration_cast<duration>(chuffed_clock::now() - start);
}

template <class P>
void push_back(const P& is_extractable, Lit p, vec<Lit>& out_nogood) {
	assert(sat.value(p) == l_False);

	out_nogood.push(~p);

	vec<Lit> removed;
	assert(!sat.reason[var(p)].isLazy());
	Clause* cp = sat.getExpl(~p);
	if (!cp) {
		// Two possibilities here: either p is false at the root,
		// or somebody pushed inconsistent assumptions.
		// * This may happen if, in an optimization problem, the user
		// * provided an objective lower bound which is achieved.
		if (sat.trailpos[var(p)] >= 0) {
			// If p and ~p are assumptions, we just return a
			// tautological clause.
			out_nogood.push(p);
		}
		return;
	}  // Otherwise, fill in the reason for ~p...
	for (int i = 1; i < cp->size(); i++) {
		Lit q((*cp)[i]);
		out_nogood.push(q);
		// Only look at the first bit of seen, because
		// we're using the second bit for assumption-ness.
		sat.seen[var(q)] |= 1;
	}
	// then push it back to assumptions.
	for (int i = 1; i < out_nogood.size(); i++) {
		Lit q(out_nogood[i]);
		if (is_extractable(q)) {
			continue;
		}
		assert(!sat.reason[var(p)].isLazy());
		Clause* c = sat.getExpl(~q);
		assert(c != nullptr);
		removed.push(q);
		out_nogood[i] = out_nogood.last();
		out_nogood.pop();
		--i;

		for (int j = 1; j < c->size(); j++) {
			Lit r((*c)[j]);
			if (!(sat.seen[var(r)] & 1)) {
				sat.seen[var(r)] = true;
				out_nogood.push(r);
			}
		}
	}

	// Clear the 'seen' bit.
	for (int i = 0; i < removed.size(); i++) {
		sat.seen[var(removed[i])] &= (~1);
	}
	for (int i = 1; i < out_nogood.size(); i++) {
		sat.seen[var(out_nogood[i])] &= (~1);
	}
}

void SAT::explainToExhaustion(std::set<int>& contributingNogoods) {
	vec<char> oldseen(seen);
	vec<Lit> old_out_learnt(out_learnt);
	vec<int> old_out_learnt_level(out_learnt_level);

	for (int i = 0; i < out_learnt.size(); i++) {
		Lit p = out_learnt[i];
		assert(!reason[var(p)].isLazy());
		Clause* cp = getExpl(~p);
		if (so.debug) {
			std::cerr << "checking literal " << getLitString(toInt(~p)) << "\n";
		}
		if (cp == nullptr) {
			if (so.debug) {
				std::cerr << "it has no reason\n";
			}
			continue;
		}
		Clause& c = *cp;
		if (c.learnt) {
			c.rawActivity() += 1;
			contributingNogoods.insert(c.clauseID());
		}
		out_learnt[i] = out_learnt.last();
		out_learnt.pop();
		out_learnt_level.pop();
		i--;
		for (int j = 1; j < c.size(); j++) {
			Lit q = c[j];
			if (so.debug) {
				std::cerr << "adding literal " << getLitString(toInt(q));
			}
			if (seen[var(q)] == 0) {
				seen[var(q)] = 1;
				out_learnt.push(q);
				out_learnt_level.push(getLevel(var(q)));
			} else {
				if (so.debug) {
					std::cerr << " but already seen it";
				}
			}
			if (so.debug) {
				std::cerr << "\n";
			}
		}
	}

	oldseen.moveTo(seen);
	old_out_learnt.moveTo(out_learnt);
	old_out_learnt_level.moveTo(out_learnt_level);
}

void SAT::clearSeen() {
	for (int i = 0; i < ivseen_toclear.size(); i++) {
		ivseen[ivseen_toclear[i]] = false;
	}
	ivseen_toclear.clear();

	for (int i = 0; i < out_learnt.size(); i++) {
		seen[var(out_learnt[i])] = 0;  // ('seen[]' is now cleared)
	}
}

int SAT::findBackTrackLevel() {
	if (out_learnt.size() < 2) {
		nrestarts++;
		return 0;
	}

	int max_i = 1;
	for (int i = 2; i < out_learnt.size(); i++) {
		if (trailpos[var(out_learnt[i])] > trailpos[var(out_learnt[max_i])]) {
			max_i = i;
		}
	}
	Lit p = out_learnt[max_i];
	int plevel = out_learnt_level[max_i];
	out_learnt[max_i] = out_learnt[1];
	out_learnt_level[max_i] = out_learnt_level[1];
	out_learnt[1] = p;
	out_learnt_level[1] = plevel;

	return engine.tpToLevel(trailpos[var(p)]);
}

//---------
// debug

// Lit:meaning:value:level

void SAT::printLit(Lit p) {
	if (isRootLevel(var(p))) {
		return;
	}
	printf("%d:", toInt(p));
	ChannelInfo& ci = c_info[var(p)];
	if (ci.cons_type == 1) {
		engine.vars[ci.cons_id]->printLit(ci.val, ci.val_type * 3 ^ static_cast<int>(sign(p)));
	} else if (ci.cons_type == 2) {
		engine.propagators[ci.cons_id]->printLit(ci.val, sign(p));
	} else {
		printf(":%d:%d, ", static_cast<int>(sign(p)), trailpos[var(p)]);
	}
}

template <class T>
void SAT::printClause(T& c) {
	printf("Size:%d - ", c.size());
	printLit(c[0]);
	printf(" <- ");
	for (int i = 1; i < c.size(); i++) {
		printLit(~c[i]);
	}
	printf("\n");
}

void SAT::checkConflict() const {
	assert(confl != nullptr);
	for (int i = 0; i < confl->size(); i++) {
		if (value((*confl)[i]) != l_False) {
			printf("Analyze: %dth lit is not false\n", i);
		}
		assert(value((*confl)[i]) == l_False);
	}

	/*
		printf("Clause %d\n", learnts.size());
		printf("Conflict clause: ");
		printClause(*confl);
	*/
}

void SAT::checkExplanation(Clause& c, int clevel, int index) {
	NOT_SUPPORTED;
	for (int i = 1; i < c.size(); i++) {
		assert(value(c[i]) == l_False);
		assert(trailpos[var(c[i])] < engine.trail_lim[clevel]);
		vec<Lit>& ctrail = trail[trailpos[var(c[i])]];
		int pos = -1;
		for (int j = 0; j < ctrail.size(); j++) {
			if (var(ctrail[j]) == var(c[i])) {
				pos = j;
				if (trailpos[var(c[i])] == clevel) {
					assert(j <= index);
				}
				break;
			}
		}
		assert(pos != -1);
	}
}
