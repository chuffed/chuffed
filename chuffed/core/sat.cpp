#include <chuffed/core/engine.h>
#include <chuffed/core/options.h>
#include <chuffed/core/propagator.h>
#include <chuffed/core/sat.h>
#include <chuffed/mip/mip.h>

#include <algorithm>
#include <cassert>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>

#define PRINT_ANALYSIS 0

SAT sat;

std::map<int, std::string> litString;

std::map<int, string> learntClauseString;
std::ofstream learntStatsStream;

cassert(sizeof(Lit) == 4);
cassert(sizeof(Clause) == 4);
cassert(sizeof(WatchElem) == 8);
cassert(sizeof(Reason) == 8);

//---------
// inline methods

inline void SAT::insertVarOrder(int x) {
	if (lookahead && lookahead_var == x) return;
	if (!order_heap.inHeap(x) && flags[x].decidable) {
		order_heap.insert(x);
	}
}

inline void SAT::setConfl(Lit p, Lit q) {
	(*short_confl)[0] = p;
	(*short_confl)[1] = q;
	confl = short_confl;
}

inline void SAT::untrailToPos(vec<Lit>& t, int p) {
	int dl = decisionLevel();

	for (int i = t.size(); i-- > p;) {
		int x = var(t[i]);
		assigns[x] = toInt(l_Undef);
#if PHASE_SAVING
		if (so.phase_saving >= 1 || (so.phase_saving == 1 && dl >= l0)) polarity[x] = sign(t[i]);
#endif
		insertVarOrder(x);
	}
	t.resize(p);
}

//---------
// main methods

SAT::SAT()
		: lit_sort(trailpos),
			pushback_time(duration::zero()),
			trail(1),
			qhead(1, 0),
			rtrail(1),
			confl(nullptr),
			var_inc(1),
			cla_inc(1),
			order_heap(VarOrderLt(activity)),
			bin_clauses(0),
			tern_clauses(0),
			long_clauses(0),
			learnt_clauses(0),
			propagations(0),
			back_jumps(0),
			nrestarts(0),
			next_simp_db(100000),
			clauses_literals(0),
			learnts_literals(0),
			max_literals(0),
			tot_literals(0),
			avg_depth(100),
			confl_rate(1000),
			ll_time(chuffed_clock::now()),
			ll_inc(1),
			learnt_len_el(10),
			learnt_len_occ(MAX_SHARE_LEN, learnt_len_el * 1000 / MAX_SHARE_LEN) {
	newVar();
	enqueue(Lit(0, true));
	newVar();
	enqueue(Lit(1, false));
	temp_sc = (SClause*)malloc(TEMP_SC_LEN * sizeof(int));
	short_expl = (Clause*)malloc(sizeof(Clause) + 3 * sizeof(Lit));
	short_confl = (Clause*)malloc(sizeof(Clause) + 2 * sizeof(Lit));
	short_expl->clearFlags();
	short_confl->clearFlags();
	short_confl->sz = 2;
}

SAT::~SAT() {
	for (int i = 0; i < clauses.size(); i++) {
		free(clauses[i]);
	}
	for (int i = 0; i < learnts.size(); i++) {
		free(learnts[i]);
	}
}

void SAT::init() {
	orig_cutoff = nVars();
	ivseen.growTo(engine.vars.size(), false);
}

int SAT::newVar(int n, ChannelInfo ci) {
	int s = assigns.size();

	watches.growBy(n);
	watches.growBy(n);
	assigns.growBy(n, toInt(l_Undef));
	reason.growBy(n, nullptr);
	trailpos.growBy(n, -1);
	seen.growBy(n, 0);
	activity.growBy(n, 0);
	polarity.growBy(n, true);
	flags.growBy(n, 7);

	for (int i = 0; i < n; i++) {
		c_info.push(ci);
		ci.val++;
		insertVarOrder(s + i);
	}

	return s;
}

int SAT::getLazyVar(ChannelInfo ci) {
	int v;
	if (var_free_list.size() != 0) {
		v = var_free_list.last();
		var_free_list.pop();
		fprintf(stderr, "reuse %d\n", v);
		assert(assigns[v] == toInt(l_Undef));
		assert(watches[2 * v].size() == 0);
		assert(watches[2 * v + 1].size() == 0);
		assert(num_used[v] == 0);
		c_info[v] = ci;
		activity[v] = 0;
		polarity[v] = true;
		flags[v] = 7;
	} else {
		v = newVar(1, ci);
		num_used.push(0);
	}
	//	flags[v].setDecidable(false);
	return v;
}

void SAT::removeLazyVar(int v) {
	return;
	ChannelInfo& ci = c_info[v];
	assert(assigns[v] == toInt(l_Undef));
	assert(watches[2 * v].size() == 0);
	assert(watches[2 * v + 1].size() == 0);
	fprintf(stderr, "free %d\n", v);
	var_free_list.push(v);
	if (ci.cons_type == 1) {
		((IntVarLL*)engine.vars[ci.cons_id])->freeLazyVar(ci.val);
	} else if (ci.cons_type == 2) {
		engine.propagators[ci.cons_id]->freeLazyVar(ci.val);
	} else {
		NEVER;
	}
}

void SAT::addClause(Lit p, Lit q) {
	if (value(p) == l_True || value(q) == l_True) {
		return;
	}
	if (value(p) == l_False && value(q) == l_False) {
		assert(false);
		TL_FAIL();
	}
	if (value(p) == l_False) {
		assert(decisionLevel() == 0);
		enqueue(q);
		return;
	}
	if (value(q) == l_False) {
		assert(decisionLevel() == 0);
		enqueue(p);
		return;
	}
	bin_clauses++;
	watches[toInt(~p)].push(q);
	watches[toInt(~q)].push(p);
}

void SAT::addClause(vec<Lit>& ps, bool one_watch) {
	int i;
	int j;
	for (i = j = 0; i < ps.size(); i++) {
		if (value(ps[i]) == l_True) {
			return;
		}
		if (value(ps[i]) == l_Undef) {
			ps[j++] = ps[i];
		}
	}
	ps.resize(j);
	if (ps.size() == 0) {
		assert(false);
		TL_FAIL();
	}
	addClause(*Clause_new(ps), one_watch);
}

void SAT::addClause(Clause& c, bool one_watch) {
	assert(c.size() > 0);
	if (c.size() == 1) {
		assert(decisionLevel() == 0);
		if (DEBUG) {
			fprintf(stderr, "warning: adding length 1 clause!\n");
		}
		if (value(c[0]) == l_False) {
			TL_FAIL();
		}
		if (value(c[0]) == l_Undef) {
			enqueue(c[0]);
		}
		free(&c);
		return;
	}
	if (!c.learnt) {
		if (c.size() == 2) {
			bin_clauses++;
		} else if (c.size() == 3) {
			tern_clauses++;
		} else {
			long_clauses++;
		}
	}

	// Mark lazy lits which are used
	if (c.learnt) {
		for (int i = 0; i < c.size(); i++) {
			incVarUse(var(c[i]));
		}
	}

	if (c.size() == 2 && ((!c.learnt) || (so.bin_clause_opt))) {
		if (!one_watch) {
			watches[toInt(~c[0])].push(c[1]);
		}
		watches[toInt(~c[1])].push(c[0]);
		if (!c.learnt) {
			free(&c);
		}
		return;
	}
	if (!one_watch) {
		watches[toInt(~c[0])].push(&c);
	}
	watches[toInt(~c[1])].push(&c);
	if (c.learnt) {
		learnts_literals += c.size();
	} else {
		clauses_literals += c.size();
	}
	if (c.learnt) {
		learnts.push(&c);
		if (so.learnt_stats) {
			std::set<int> levels;
			for (int i = 0; i < c.size(); i++) {
				levels.insert(out_learnt_level[i]);
			}
			std::stringstream s;
			//            s << "learntclause,";
			s << c.clauseID() << "," << c.size() << "," << levels.size();
			if (so.learnt_stats_nogood) {
				s << ",";
				for (int i = 0; i < c.size(); i++) {
					s << (i == 0 ? "" : " ") << getLitString(toInt(c[i]));
					//              s << " (" << out_learnt_level[i] << ")";
				}
			}
			// std::cerr << "\n";
			learntClauseString[c.clauseID()] = s.str();
		}
	} else {
		clauses.push(&c);
	}
}

void SAT::removeClause(Clause& c) {
	assert(c.size() > 1);
	watches[toInt(~c[0])].remove(&c);
	watches[toInt(~c[1])].remove(&c);
	if (c.learnt) {
		learnts_literals -= c.size();
	} else {
		clauses_literals -= c.size();
	}

	if (c.learnt) {
		for (int i = 0; i < c.size(); i++) {
			decVarUse(var(c[i]));
		}
	}

	if (c.learnt) {
		//            learntClauseScore[c.clauseID()] = c.rawActivity();
		/* if (so.debug) { */
		if (so.learnt_stats) {
			int id = c.clauseID();
			learntStatsStream << learntClauseString[id];
			learntStatsStream << ",";
			learntStatsStream << c.rawActivity();
			learntStatsStream << "\n";
			/* std::cerr << "clausescore," <<  << "," << c.rawActivity() << "\n"; */
		}
		/* } */
	}

	free(&c);
}

void SAT::topLevelCleanUp() {
	assert(decisionLevel() == 0);

	for (int i = rtrail[0].size(); i-- > 0;) {
		free(rtrail[0][i]);
	}
	rtrail[0].clear();

	if (so.sat_simplify && propagations >= next_simp_db) {
		simplifyDB();
	}

	for (int i = 0; i < trail[0].size(); i++) {
		if (so.debug) {
			std::cerr << "setting true at top-level: " << getLitString(toInt(trail[0][i])) << "\n";
		}
		seen[var(trail[0][i])] = 1;
		trailpos[var(trail[0][i])] = -1;
	}
	trail[0].clear();
	qhead[0] = 0;
}

void SAT::simplifyDB() {
	int i;
	int j;
	for (i = j = 0; i < learnts.size(); i++) {
		if (simplify(*learnts[i])) {
			removeClause(*learnts[i]);
		} else {
			learnts[j++] = learnts[i];
		}
	}
	learnts.resize(j);
	next_simp_db = propagations + clauses_literals + learnts_literals;
}

bool SAT::simplify(Clause& c) const {
	if (value(c[0]) == l_True) {
		return true;
	}
	if (value(c[1]) == l_True) {
		return true;
	}
	int i;
	int j;
	for (i = j = 2; i < c.size(); i++) {
		if (value(c[i]) == l_True) {
			return true;
		}
		if (value(c[i]) == l_Undef) {
			c[j++] = c[i];
		}
	}
	c.resize(j);
	return false;
}

string showReason(Reason r) {
	std::stringstream ss;
	switch (r.d.type) {
		case 0:
			if (r.pt == nullptr) {
				ss << "no reason";
			} else {
				Clause& c = *r.pt;
				ss << "clause";
				for (int i = 0; i < c.size(); i++) {
					ss << " " << getLitString(toInt(~c[i]));
				}
			}
			break;
		case 1:
			ss << "absorbed binary clause?";
			break;
		case 2:
			ss << "single literal " << getLitString(toInt(~toLit(r.d.d1)));
			break;
		case 3:
			ss << "two literals " << getLitString(toInt(~toLit((r.d.d1)))) << " & "
				 << getLitString(toInt(~toLit((r.d.d2))));
			break;
	}
	return ss.str();
}

// Use cases:
// enqueue from decision   , value(p) = u  , r = NULL , channel
// enqueue from analyze    , value(p) = u  , r != NULL, channel
// enqueue from unit prop  , value(p) = u  , r != NULL, channel

void SAT::enqueue(Lit p, Reason r) {
	/* if (so.debug) { */
	/*   std::cerr << "enqueue literal " << getLitString(toInt(p)) << " because " << showReason(r) <<
	 * "\n"; */
	/* } */
	assert(value(p) == l_Undef);
	int v = var(p);
	assigns[v] = toInt(lbool(!sign(p)));
	trailpos[v] = engine.trailPos();
	reason[v] = r;
	trail.last().push(p);
	ChannelInfo& ci = c_info[v];
	if (ci.cons_type == 1) {
		engine.vars[ci.cons_id]->channel(ci.val, static_cast<LitRel>(ci.val_type),
																		 static_cast<int>(sign(p)));
	}
}

// enqueue from FD variable, value(p) = u/f, r = ?, don't channel

void SAT::cEnqueue(Lit p, Reason r) {
	/* if (so.debug) { */
	/*   std::cerr << "c-enqueue literal " << getLitString(toInt(p)) << " because " << showReason(r)
	 * << "\n"; */
	/* } */
	assert(value(p) != l_True);
	int v = var(p);
	if (value(p) == l_False) {
		if (so.lazy) {
			if (r == nullptr) {
				assert(decisionLevel() == 0);
				setConfl();
			} else {
				confl = getConfl(r, p);
				(*confl)[0] = p;
			}
		} else {
			setConfl();
		}
		return;
	}
	assigns[v] = toInt(lbool(!sign(p)));
	trailpos[v] = engine.trailPos();
	reason[v] = r;
	trail.last().push(p);
}

void SAT::aEnqueue(Lit p, Reason r, int l) {
	if (so.debug) {
		std::cerr << "a-enqueue literal " << getLitString(toInt(p)) << " because " << showReason(r)
							<< " and l=" << l << "\n";
	}
	assert(value(p) == l_Undef);
	int v = var(p);
	assigns[v] = toInt(lbool(!sign(p)));
	trailpos[v] = engine.trail_lim[l] - 1;
	reason[v] = r;
	trail[l].push(p);
}

void SAT::btToLevel(int level) {
#if DEBUG_VERBOSE
	std::cerr << "SAT::btToLevel( " << level << ")\n";
#endif
	if (decisionLevel() <= level || (lookahead && confl != NULL)) {
		return;
	}

	for (int l = trail.size(); l-- > level + 1;) {
		untrailToPos(trail[l], 0);
		for (int i = rtrail[l].size(); (i--) != 0;) {
			free(rtrail[l][i]);
		}
	}
	trail.resize(level + 1);
	qhead.resize(level + 1);
	rtrail.resize(level + 1);

	engine.btToLevel(level);
	if (so.mip) {
		mip->btToLevel(level);
	}
}

void SAT::btToPos(int sat_pos, int core_pos) {
	untrailToPos(trail.last(), sat_pos);
	engine.btToPos(core_pos);
}

// Propagator methods:

bool SAT::propagate() {
	int num_props = 0;

	int& qhead = this->qhead.last();
	vec<Lit>& trail = this->trail.last();

	while (qhead < trail.size()) {
		num_props++;

		Lit p = trail[qhead++];  // 'p' is enqueued fact to propagate.
		vec<WatchElem>& ws = watches[toInt(p)];

		if (ws.size() == 0) {
			continue;
		}

		WatchElem* i;
		WatchElem* j;
		WatchElem* end;

		for (i = j = ws, end = i + ws.size(); i != end;) {
			WatchElem& we = *i;
			switch (we.d.type) {
				case 1: {
					// absorbed binary clause
					*j++ = *i++;
					Lit q = toLit(we.d.d2);
					switch (toInt(value(q))) {
						case 0:
							enqueue(q, ~p);
							break;
						case -1:
							setConfl(q, ~p);
							qhead = trail.size();
							while (i < end) {
								*j++ = *i++;
							}
							break;
						default:;
					}
					continue;
				}
				case 2: {
					// wake up FD propagator
					*j++ = *i++;
					engine.propagators[we.d.d2]->wakeup(we.d.d1, 0);
					continue;
				}
				default:
					Clause& c = *we.pt;
					i++;

					// Check if already satisfied
					if (value(c[0]) == l_True || value(c[1]) == l_True) {
						*j++ = &c;
						continue;
					}

					Lit false_lit = ~p;

					// Make sure the false literal is data[1]:
					if (c[0] == false_lit) {
						c[0] = c[1], c[1] = false_lit;
					}

					// Look for new watch:
					for (int k = 2; k < c.size(); k++) {
						if (value(c[k]) != l_False) {
							c[1] = c[k];
							c[k] = false_lit;
							watches[toInt(~c[1])].push(&c);
							goto FoundWatch;
						}
					}

					// Did not find watch -- clause is unit under assignment:
					*j++ = &c;
					if (value(c[0]) == l_False) {
						confl = &c;
						qhead = trail.size();
						while (i < end) {
							*j++ = *i++;
						}
					} else {
						enqueue(c[0], &c);
					}
				FoundWatch:;
			}
		}
		ws.shrink(i - j);
	}
	propagations += num_props;

	return (confl == nullptr);
}

struct activity_lt {
	bool operator()(Clause* x, Clause* y) { return x->activity() < y->activity(); }
};
void SAT::reduceDB() {
	int i;
	int j;

	std::sort((Clause**)learnts, (Clause**)learnts + learnts.size(), activity_lt());

	for (i = j = 0; i < learnts.size() / 2; i++) {
		if (!locked(*learnts[i])) {
			removeClause(*learnts[i]);
		} else {
			learnts[j++] = learnts[i];
		}
	}
	for (; i < learnts.size(); i++) {
		learnts[j++] = learnts[i];
	}
	learnts.resize(j);

	if (so.verbosity >= 1) {
		printf("%% Pruned %d learnt clauses\n", i - j);
	}
}

std::string showClause(Clause& c) {
	std::stringstream ss;
	for (int i = 0; i < c.size(); i++) {
		ss << " " << getLitString(toInt(c[i]));
	}
	return ss.str();
}

struct raw_activity_gt {
	bool operator()(Clause* x, Clause* y) { return x->rawActivity() > y->rawActivity(); }
};
// This is wrong, because probably most of the clauses have been
// removed by the time we do this.
void SAT::printLearntStats() {
	/* std::ofstream clausefile("clause-info.csv"); */
	/* for (int i = 0 ; i < learnts.size() ; i++) { */
	/*   clausefile << learnts[i]->clauseID() << "," << learnts[i]->rawActivity() << "," <<
	 * showClause(*learnts[i]) << "\n"; */
	/* } */

	std::sort((Clause**)learnts, (Clause**)learnts + learnts.size(), raw_activity_gt());
	std::cerr << "top ten clauses:\n";
	for (int i = 0; i < 10 && i < learnts.size(); i++) {
		std::cerr << i << ": " << learnts[i]->rawActivity() << " " << showClause(*learnts[i]) << "\n";
	}
}

void SAT::printStats() const {
	printf("%%%%%%mzn-stat: binClauses=%d\n", bin_clauses);
	printf("%%%%%%mzn-stat: ternClauses=%d\n", tern_clauses);
	printf("%%%%%%mzn-stat: longClauses=%d\n", long_clauses);
	printf("%%%%%%mzn-stat: avgLongClauseLen=%.2f\n",
				 long_clauses != 0
						 ? (double)(clauses_literals - static_cast<long long>(3 * tern_clauses)) / long_clauses
						 : 0);
	printf("%%%%%%mzn-stat: learntClauses=%d\n", learnts.size());
	printf("%%%%%%mzn-stat: avgLearntClauseLen=%.2f\n",
				 learnts.size() != 0 ? (double)learnts_literals / learnts.size() : 0);
	printf("%%%%%%mzn-stat: satPropagations=%lld\n", propagations);
	printf("%%%%%%mzn-stat: naturalRestarts=%lld\n", nrestarts);
	if (so.ldsb) {
		printf("%%%%%%mzn-stat: pushbackTime=%.3f\n", to_sec(pushback_time));
	}
}

//-----
// Branching methods

bool SAT::finished() {
	assert(so.vsids);
	while (!order_heap.empty()) {
		int x = order_heap[0];
		if ((assigns[x] == 0) && flags[x].decidable) {
			return false;
		}
		order_heap.removeMin();
	}
	return true;
}

int SAT::get_lookahead_next() {
	//Ensure the same integer variable is not picked repeatedly.
	double prev_activity;
	bool dec_activity = false;
	int next = order_heap[0];

	if (c_info[next].cons_type != BOOL_VAR) {
		for (int i = 0; i < order_heap.size(); i++) {
			int li = order_heap[i];
			if (activity[next] > activity[li]) break;
			if (c_info[li].cons_type == BOOL_VAR && !assigns[li] && flags[li].decidable) {
				prev_activity = activity[li];
				dec_activity = true;
				activity[li] = nextafter(prev_activity, HUGE_VAL); //Increment activity by a small amount
				//activity[li] += std::max(var_inc * 10e-8, 1e-100);
				order_heap.decrease(li);
				break;
			}
		}
	}
	next = order_heap.removeMin();
	if (dec_activity) activity[next] = prev_activity;
	return next;
}
int SAT::lookahead_branch(int next) {
	assert(!assigns[next]);
	assert(flags[next].decidable);
	ChannelInfo& ci = c_info[next];
	lookahead = true;
	lookahead_var = next;

	int opt_type = engine.opt_type ? 1 : -1;

	int l_0, d_0;
	bool c_0;

	std::tie(l_0, d_0, c_0) = engine.propagate_lookahead(2 * next + static_cast<int>(!polarity[next]));
	l_0 *= opt_type;
	if (c_0) {
		lookahead = false;
		return  2 * next + static_cast<int>(polarity[next]);
	}

	int l_1, d_1;
	bool c_1;

	std::tie(l_1, d_1, c_1) = engine.propagate_lookahead(2 * next + static_cast<int>(polarity[next]));
	l_1 *= opt_type;
	lookahead = false;

	if (!c_1 && (l_0 > l_1) || (l_0 == l_1 && d_0 < d_1)) {
		return 2 * next + static_cast<int>(!polarity[next]);
	}
	return 2 * next + static_cast<int>(polarity[next]);
}

DecInfo* SAT::branch() {
	if (!so.vsids) {
		return nullptr;
	}

	assert(!order_heap.empty());

	if (so.lookahead) {
		int next = get_lookahead_next();
		return new DecInfo(nullptr, lookahead_branch(next));
	}

	int next = order_heap.removeMin();

	assert(!assigns[next]);
	assert(flags[next].decidable);

	return new DecInfo(nullptr, 2 * next + static_cast<int>(polarity[next]));
}

void Clause::debug() const {
	for (size_t i = 0; i < size(); i++) {
		if (i > 0) {
			std::cerr << " \\/ ";
		}
		std::cerr << getLitString(toInt(operator[](i)));
	}
	std::cerr << "\n";
}
