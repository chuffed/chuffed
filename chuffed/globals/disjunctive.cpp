#include <chuffed/core/propagator.h>

#define DISJ_DEBUG 0

using namespace std;

// propagates bounds given precedences
class DisjunctiveBP : public Propagator {
	// structure to store propagation info for lazy explanation
	struct Pinfo {
		int var;  // which var's bound changed
		int est;  // est of set which forced the bound
		Pinfo(int v, int e) : var(v), est(e) {}
	};

	bool trailed_pinfo_sz;

public:
	// constant data
	vec<IntVar*>& x;  // start times
	vec<int>& dur;    // durations of tasks
	BoolView** pred;  // precedence literals

	// Persistent non-trailed state
	int* ests;  // task no. sorted according to est in ascending order
	int* lets;  // task no. sorted according to let in descending order

	// Persistent trailed state
	Tint* old_est;  // est's before any propagations are made

	vec<Pinfo> p_info;  // memory for propagation info

	int est(int i) { return x[i]->getMin(); }
	int let(int i) { return x[i]->getMax() + dur[i]; }

	DisjunctiveBP(vec<IntVar*>& _x, vec<int>& _dur, BoolView** _pred, int* _ests, int* _lets)
			: x(_x), dur(_dur), pred(_pred), ests(_ests), lets(_lets) {
		priority = 3;

		old_est = (Tint*)malloc(x.size() * sizeof(Tint));
	}

	Reason createReason(int var, int est) {
		if (!trailed_pinfo_sz) {
			engine.trail.push(TrailElem(&p_info._size(), 4));
			trailed_pinfo_sz = true;
		}
		p_info.push(Pinfo(var, est));
		return Reason(prop_id, p_info.size() - 1);
	}

	bool propagate() override {
		trailed_pinfo_sz = false;

		for (int i = 0; i < x.size(); i++) {
			old_est[i] = est(i);
		}
		for (int i = 0; i < x.size(); i++) {
			int b = INT_MIN;
			int e = INT_MIN;
			for (int ests_i = 0; ests_i < x.size(); ests_i++) {
				int j = ests[ests_i];
				if (!pred[j][i].isTrue()) {
					continue;
				}
				if (old_est[j] >= b) {
					e = b = old_est[j];
				}
				b += dur[j];
			}
			if (x[i]->setMinNotR(b)) {
				if (engine.decisionLevel() == 0) {
					fprintf(stderr, "%% prop_id = %d, var_id = %d, i = %d, b = %d\n", prop_id, x[i]->var_id,
									i, b);
				}
				if (!x[i]->setMin(b, createReason(i, e))) {
					return false;
				}
			}
		}
		return true;
	}

	Clause* explain(Lit p, int inf_id) override {
		Pinfo& pi = p_info[inf_id];
		/*
				fprintf(stderr, "var = %d, est = %d\n", pi.var, pi.est);

				for (int i = 0; i < x.size(); i++) {
					fprintf(stderr, "x[%d]: est = %d, let = %d, dur = %d\n", i, est(i), let(i), dur[i]);
				}

				fprintf(stderr, "Old est: ");
				for (int i = 0; i < x.size(); i++) {
					fprintf(stderr, "%d ", old_est[i]);
				}
				fprintf(stderr, "\n");

				fprintf(stderr, "Preds: ");
				for (int i = 0; i < x.size(); i++) {
					fprintf(stderr, "%d ", pred[i][pi.var].isTrue());
				}
				fprintf(stderr, "\n");

				fprintf(stderr, "in: ");
		*/
		vec<Lit> ps(1);

		// can lift!
		int lb = pi.est;
		for (int i = 0; i < x.size(); i++) {
			BoolView& p = pred[i][pi.var];
			if (p.isTrue() && old_est[i] >= pi.est) {
				ps.push(p.getValLit());
				ps.push(x[i]->getMinLit());
				lb += dur[i];
				//				fprintf(stderr, "%d ", i);
			}
		}
		//		fprintf(stderr, "\n");
		//		fprintf(stderr, "lb = %d, inf_lb = %d\n", lb, (sat.c_info[var(p)].v>>2)+1);
		assert(lb > sat.c_info[var(p)].val);

		/*
				for (int i = 0; i < x.size(); i++) {
					BoolView& p = pred[i][pi.var];
					if (p.isTrue() && est(i) >= pi.est) {
						ps.push(p.getValLit());
						ps.push(x[i]->getLit(pi.est-1, LR_LE));
					}
				}
		*/

		Clause* expl = Clause_new(ps);
		expl->temp_expl = 1;
		sat.rtrail.last().push(expl);

		if (DISJ_DEBUG) {
			fprintf(stderr, "BP explain: length %d\n", expl->size());
		}

		return expl;
	}
};

// Finds precedences only
class DisjunctiveEF : public Propagator {
	// structure to store propagation info for lazy explanation
	struct Pinfo {
		int ps_i;      // point in pre-emptive schedule that inference was made
		int var;       // task which has to be after set of other tasks
		int let;       // let of set used to make inference
		Clause* expl;  // explanation for inference
		Pinfo(int _ps_i, int _var, int _let) : ps_i(_ps_i), var(_var), let(_let), expl(nullptr) {}
	};

	bool trailed_pinfo_sz;

public:
	// constant data
	vec<IntVar*> x;   // start times
	vec<int> dur;     // durations of tasks
	BoolView** pred;  // precedence literals

	DisjunctiveBP* bp;  // bounds propagation part of propagator

	// Persistent trailed state

	Tint* ps_times;  // times in pre-emptive schedule
	Tint* ps_tasks;  // tasks in pre-emptive schedule
	Tint* residual;  // residual of task i in current pre-emptive schedule

	vec<Pinfo> p_info;  // memory for propagation info

	// Persistent non-trailed state
	int* ests;  // task no. sorted according to est in ascending order
	int* lets;  // task no. sorted according to let in descending order

	// Inline functions

	int est(int i) { return x[i]->getMin(); }
	int let(int i) { return x[i]->getMax() + dur[i]; }

	struct SortEstAsc {
		DisjunctiveEF* p;
		bool operator()(int i, int j) const { return p->est(i) < p->est(j); }
		SortEstAsc(DisjunctiveEF* _p) : p(_p) {}
	} sort_est_asc;

	struct SortEstDsc {
		DisjunctiveEF* p;
		bool operator()(int i, int j) const { return p->est(i) > p->est(j); }
		SortEstDsc(DisjunctiveEF* _p) : p(_p) {}
	} sort_est_dsc;

	struct SortLetAsc {
		DisjunctiveEF* p;
		bool operator()(int i, int j) const { return p->let(i) < p->let(j); }
		SortLetAsc(DisjunctiveEF* _p) : p(_p) {}
	} sort_let_asc;

	struct SortLetDsc {
		DisjunctiveEF* p;
		bool operator()(int i, int j) const { return p->let(i) > p->let(j); }
		SortLetDsc(DisjunctiveEF* _p) : p(_p) {}
	} sort_let_dsc;

	DisjunctiveEF(vec<IntVar*>& _x, vec<int>& _dur)
			: x(_x),
				dur(_dur),
				sort_est_asc(this),
				sort_est_dsc(this),
				sort_let_asc(this),
				sort_let_dsc(this) {
		// set priority
		priority = 3;

		// create all intermediate precedence literals
		pred = (BoolView**)malloc(x.size() * sizeof(BoolView*));
		for (int i = 0; i < x.size(); i++) {
			pred[i] = (BoolView*)malloc(x.size() * sizeof(BoolView));
		}
		for (int i = 0; i < x.size(); i++) {
			for (int j = i + 1; j < x.size(); j++) {
				BoolView r = newBoolVar();
				pred[i][j] = r;
				pred[j][i] = ~r;
				int_rel_half_reif(x[j], IRT_GE, x[i], r, dur[i]);
				int_rel_half_reif(x[i], IRT_GE, x[j], ~r, dur[j]);
			}
			pred[i][i] = bv_false;
		}

		// initialise data structures
		ps_times = (Tint*)malloc(static_cast<size_t>(4 * x.size()) * sizeof(Tint));
		ps_tasks = (Tint*)malloc(static_cast<size_t>(4 * x.size()) * sizeof(Tint));
		residual = (Tint*)malloc(x.size() * sizeof(Tint));

		ests = (int*)malloc(x.size() * sizeof(int));
		lets = (int*)malloc(x.size() * sizeof(int));

		for (int i = 0; i < x.size(); i++) {
			ests[i] = lets[i] = i;
		}

		// attach to var events
		for (int i = 0; i < x.size(); i++) {
			x[i]->attach(this, i, EVENT_LU);
		}

		bp = new DisjunctiveBP(x, dur, pred, ests, lets);
	}

	bool findBasicPrecedences() {
		int* eet = new int[x.size()];
		int* lst = new int[x.size()];
		//		int eet[x.size()];
		//		int lst[x.size()];

		for (int i = 0; i < x.size(); i++) {
			eet[i] = x[i]->getMin() + dur[i];
			lst[i] = x[i]->getMax();
		}

		for (int i = 0; i < x.size(); i++) {
			for (int j = i + 1; j < x.size(); j++) {
				// Can lift these explanations
				//				if (prop_id == 1 && i == 0 && j == 2) {
				//					fprintf(stderr, "lst(0) = %d, eet(0) = %d, lst(2) = %d, eet(2) = %d\n", lst[0],
				// eet[0], lst[2], eet[2]);
				//				}
				if (lst[i] < eet[j]) {
					setDom(pred[i][j], setVal, 1, x[i]->getMaxLit(), x[j]->getMinLit());
				}
				if (lst[j] < eet[i]) {
					setDom(pred[j][i], setVal, 1, x[j]->getMaxLit(), x[i]->getMinLit());
				}
			}
		}

		delete[] eet;
		delete[] lst;
		return true;
	}

	Reason createReason(int ps_i, int var, int let) {
		if (!trailed_pinfo_sz) {
			engine.trail.push(TrailElem(&p_info._size(), 4));
			trailed_pinfo_sz = true;
		}
		p_info.push(Pinfo(ps_i, var, let));
		return Reason(prop_id, p_info.size() - 1);
	}

	bool doEdgeFinding() {
		for (int i = 0; i < x.size(); i++) {
			residual[i] = dur[i];
		}

		// create pre-emptive schedule

		int ests_i = 0;
		int ps_i = 0;
		int cur_time = est(ests[0]);
		int next_lb = 0;
		int lets_comp = x.size();

		Heap<SortLetAsc> pqueue(sort_let_asc);

		//		fprintf(stderr, "Forming schedule\n");

		while (true) {
			ps_times[ps_i] = cur_time;

			if (let(lets[lets_comp - 1]) <= cur_time) {
				explainFailure(lets[lets_comp - 1], ps_i);
				return false;
			}

			// process newly available tasks
			for (; ests_i < x.size(); ests_i++) {
				int task = ests[ests_i];
				if (x[task]->getMin() > cur_time) {
					break;
				}
				assert(x[task]->getMin() == cur_time);

				// add task to priority queue
				pqueue.insert(task);

				// no inference possible when zero time elapses
				if (dur[task] == 0) {
					continue;
				}

				// infer precedences by looking for bound b s.t.
				// cur_time + dur[task] + sum_{t | let(t) <= b} residual[t] > b
				int lets_i;
				int eet = cur_time + dur[task];
				for (lets_i = lets_comp; let(lets[--lets_i]) < let(task);) {
					eet += residual[lets[lets_i]];
					if (eet > let(lets[lets_i])) {
						break;
					}
				}

				// no precedences can be inferred
				if (let(lets[lets_i]) == let(task)) {
					continue;
				}

				// precedences can be inferred
				Reason r = createReason(ps_i, task, let(lets[lets_i]));
				for (int i = lets_i; i < lets_comp; i++) {
					if (residual[lets[i]] == 0) {
						continue;
					}
					BoolView& v = pred[lets[i]][task];
					if (v.setValNotR(true)) {
						if (!v.setVal(true, r)) {
							return false;
						}
					}
				}
			}

			// move to next time point

			next_lb = (ests_i == x.size() ? INT_MAX : est(ests[ests_i]));

			ps_tasks[ps_i] = pqueue.empty() ? -1 : pqueue[0];
			ps_i++;

			if (pqueue.empty()) {
				// do nothing until next available task
				assert(next_lb != INT_MAX);
				//				fprintf("w%d, ", next_lb - cur_time);
				cur_time = next_lb;
			} else {
				Tint& res = residual[pqueue[0]];
				if (cur_time + res <= next_lb) {
					//					fprintf("f%d, ", res);
					// can finish off highest priority task
					cur_time += res;
					res = 0;
					pqueue.removeMin();
					while ((lets_comp != 0) && residual[lets[lets_comp - 1]] == 0) {
						lets_comp--;
					}
					//					fprintf(stderr, "lets_comp = %d\n", lets_comp);
					if (lets_comp == 0) {
						break;
					}
				} else {
					// do some of highest priority task
					//					fprintf("f%d, ", next_lb - cur_time);
					res = res - next_lb + cur_time;
					cur_time = next_lb;
				}
			}
		}

		return true;
	}

	void explainFailure(int task, int ps_i) {
		// find set which forced the precedence
		//		bool in[x.size()];
		bool* in = new bool[x.size()];
		int set_est = est(task);
		/*
				for (int i = 0; i < x.size(); i++) {
					fprintf(stderr, "x[%d]: est = %d, let = %d, dur = %d\n", i, est(i), let(i), dur[i]);
				}

				fprintf(stderr, "ests: ");
				for (int i = 0; i < x.size(); i++) fprintf(stderr, "%d ", ests[i]);
				fprintf(stderr, "\n");

				fprintf(stderr, "lets: ");
				for (int i = 0; i < x.size(); i++) fprintf(stderr, "%d ", lets[i]);
				fprintf(stderr, "\n");

				fprintf(stderr, "Schedule:\n");
				for (int i = 0; i < ps_i; i++) {
					fprintf(stderr, "%d: %d, ", ps_times[i], ps_tasks[i]);
				}
				fprintf(stderr, "\n");

				fprintf(stderr, "task = %d, cur_time = %d, in: \n", task, ps_times[ps_i]);
		*/
		for (int i = 0; i < x.size(); i++) {
			in[i] = false;
		}
		in[task] = true;

		while (ps_times[ps_i--] > set_est) {
			if (!in[ps_tasks[ps_i]]) {
				in[ps_tasks[ps_i]] = true;
				if (est(ps_tasks[ps_i]) < set_est) {
					set_est = est(ps_tasks[ps_i]);
				}
			}
		}
		/*
				for (int i = 0; i < x.size(); i++) {
					if (in[i]) fprintf(stderr, "%d ", i);
				}
				fprintf(stderr, "\n");
		*/
		// create explanation
		vec<Lit> ps;

		// can lift!
		for (int i = 0; i < x.size(); i++) {
			if (!in[i]) {
				continue;
			}
			ps.push(x[i]->getMinLit());
			ps.push(x[i]->getMaxLit());
		}

		/*
				ps.push(x[pi.var]->getLit(set_est, LR_GE));
				for (int i = 0; i < x.size(); i++) {
					if (!in[i]) continue;
					ps.push(x[i]->getLit(set_est, LR_GE));
					ps.push(x[i]->getLit(set_let - dur[i], LR_LE));
				}
		*/

		Clause* expl = Clause_new(ps);
		expl->temp_expl = 1;
		sat.rtrail.last().push(expl);
		sat.confl = expl;

		if (DISJ_DEBUG) {
			fprintf(stderr, "EF fail: length %d\n", expl->size());
		}
		delete[] in;
	}

	bool propagate() override {
		trailed_pinfo_sz = false;

		// sort vars based on est and let
		sort(ests, ests + x.size(), sort_est_asc);
		sort(lets, lets + x.size(), sort_let_dsc);

		//		if (!findBasicPrecedences()) return false;
		if (so.disj_edge_find && !doEdgeFinding()) {
			return false;
		}
		if (so.disj_set_bp && !bp->propagate()) {
			return false;
		}

		return true;
	}

	Clause* explain(Lit p, int inf_id) override {
		Pinfo& pi = p_info[inf_id];

		if (pi.expl != nullptr) {
			return pi.expl;
		}

		// find set which forced the precedence
		//		bool in[x.size()];
		bool* in = new bool[x.size()];
		int ps_i = pi.ps_i;
		int set_est = ps_times[ps_i];

		for (int i = 0; i < x.size(); i++) {
			if (let(i) <= pi.let && residual[i] > 0) {
				in[i] = true;
				if (est(i) < set_est) {
					set_est = est(i);
				}
			} else {
				in[i] = false;
			}
		}

		//		fprintf(stderr, "task = %d, cur_time = %d, let = %d, in: \n", pi.var, ps_times[pi.ps_i],
		// pi.let);

		while (ps_times[ps_i--] > set_est) {
			if (!in[ps_tasks[ps_i]]) {
				in[ps_tasks[ps_i]] = true;
				if (est(ps_tasks[ps_i]) < set_est) {
					set_est = est(ps_tasks[ps_i]);
				}
			}
		}

		/*
				for (int i = 0; i < x.size(); i++) {
					fprintf(stderr, "x[%d]: est = %d, let = %d, dur = %d\n", i, est(i), let(i), dur[i]);
				}

				fprintf(stderr, "ests: ");
				for (int i = 0; i < x.size(); i++) fprintf(stderr, "%d ", ests[i]);
				fprintf(stderr, "\n");

				fprintf(stderr, "lets: ");
				for (int i = 0; i < x.size(); i++) fprintf(stderr, "%d ", lets[i]);
				fprintf(stderr, "\n");

				fprintf(stderr, "Schedule:\n");
				for (int i = 0; i < pi.ps_i; i++) {
					fprintf(stderr, "%d: %d, ", ps_times[i], ps_tasks[i]);
				}
				fprintf(stderr, "\n");

				fprintf(stderr, "residual: ");
				for (int i = 0; i < x.size(); i++) fprintf(stderr, "%d ", residual[i]);
				fprintf(stderr, "\n");


				for (int i = 0; i < x.size(); i++) {
					if (in[i]) fprintf(stderr, "%d ", i);
				}
				fprintf(stderr, "\n");
		*/

		// create explanation
		vec<Lit> ps(1);

		// can lift!
		ps.push(x[pi.var]->getMinLit());
		for (int i = 0; i < x.size(); i++) {
			if (!in[i]) {
				continue;
			}
			ps.push(x[i]->getMinLit());
			ps.push(x[i]->getMaxLit());
		}

		/*
				ps.push(x[pi.var]->getLit(set_est, LR_GE));
				for (int i = 0; i < x.size(); i++) {
					if (!in[i]) continue;
					ps.push(x[i]->getLit(set_est, LR_GE));
					ps.push(x[i]->getLit(pi.let - dur[i], LR_LE));
				}
		*/

		Clause* expl = Clause_new(ps);
		expl->temp_expl = 1;
		sat.rtrail.last().push(expl);

		pi.expl = expl;

		if (DISJ_DEBUG) {
			fprintf(stderr, "EF explain: length %d\n", expl->size());
		}

		delete[] in;

		return expl;
	}
};

void disjunctive(vec<IntVar*>& x, vec<int>& dur) { new DisjunctiveEF(x, dur); }
