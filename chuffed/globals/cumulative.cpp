#include <chuffed/core/propagator.h>
#include <list>
#include <queue>
#include <set>
#include <iostream>

using namespace std;

	// Time Decomposition of the cumulative constraint
void timed_cumulative(vec<IntVar*>& s, vec<int>& d, vec<int>& r, int b) {
	assert(s.size() == d.size() && s.size() == r.size());
	int min = INT_MAX;
	int max = INT_MIN;
	//	bool in[s.size()];
	bool* in = new bool[s.size()];
	vec<int> a;
	for (int i = 0; i < s.size(); i++) {
		in[i] = (d[i] > 0 && r[i] > 0);
		if (!in[i]) continue;
		if (s[i]->getMin() < min) min = s[i]->getMin();
		if (s[i]->getMax() + d[i] > max) max = s[i]->getMax() + d[i];
		s[i]->specialiseToEL();
		a.push(r[i]);
	}
	for (int t = min; t <= max; t++) {
		vec<IntVar*> x;
		for (int i = 0; i < s.size(); i++) {
			if (!in[i]) continue;
			BoolView b1(s[i]->getLit(t,3));
			BoolView b2(s[i]->getLit(t-d[i]+1,2));
			BoolView b3 = newBoolVar();
			IntVar* v = newIntVar(0,1);
			bool_rel(b1, BRT_AND, b2, b3);
			bool2int(b3, v);
			x.push(v);
		}
		int_linear(a, x, IRT_LE, b);
	}
	delete[] in;

}

#define CUMUVERB 0

	// Data types for the Chuffed solver
#define CUMU_ARR_INTVAR vec<IntVar*>
#define CUMU_ARR_INT vec<int>
#define CUMU_INTVAR IntVar*
#define CUMU_INT int
#define CUMU_BOOL bool
#define CUMU_GETMIN(x) x.getMin()
#define CUMU_GETMAX(x) x.getMax()
#define CUMU_GETMAX0(x) x.getMax()
#define CUMU_PT_GETMIN(x) x->getMin()
#define CUMU_PT_GETMAX(x) x->getMax()
#define CUMU_PT_GETMIN0(x) x->getMin0()
#define CUMU_PT_GETMAX0(x) x->getMax0()
#define CUMU_PT_ISFIXED(x) x->isFixed()

class CumulativeProp : public Propagator {
	enum ExplDeg {
		ED_NAIVE,
		ED_NORMAL,
		ED_LIFT
	};
	// Task-Duration tuple
	struct TaskDur {
		int task;
		int dur_in;
		TaskDur(int _task, int _dur_in) : task(_task), dur_in(_dur_in) {}
	};
	// TTEF Update Structure
	struct TTEFUpdate {
		int task;
		int bound_new;
		int tw_begin;
		int tw_end;
		bool is_lb_update;
		TTEFUpdate(int _t, int _n, int _b, int _e, int _l) : task(_t), bound_new(_n), 
			tw_begin(_b), tw_end(_e), is_lb_update(_l) {}
	};
	// Compulsory Part of a Task
	struct CompPart {
		CUMU_INT begin;
		CUMU_INT end;
		CUMU_INT level;
		CUMU_INT task;
		CompPart(CUMU_INT b, CUMU_INT e, CUMU_INT l, CUMU_INT t)
		: begin(b), end(e), level(l), task(t) {}
	};

	// Resource profile of the resource
	struct ProfilePart {
		CUMU_INT begin;
		CUMU_INT end;
		CUMU_INT level;
		set<CUMU_INT> tasks;
		ProfilePart(CUMU_INT b, CUMU_INT e, CUMU_INT l, CUMU_INT t)
		: begin(b), end(e), level(l) { tasks.insert(t); };
		ProfilePart() : begin(0), end(0), level(0) {}
	};

	enum ProfileChange { PROFINC, PROFDEC };
	struct ProfileChangePt {
		CUMU_INT time;
		ProfileChange change;
		ProfileChangePt(CUMU_INT t, ProfileChange c) : time(t), change(c) {}
	};

	Tint last_unfixed;

public:
    string name; // Name of the cumulative constraint for printing statistics

	// Constant Data
	CUMU_ARR_INTVAR	start;	// Start time variables of the tasks
	CUMU_ARR_INTVAR	dur;	// Durations of the tasks
	CUMU_ARR_INTVAR	usage;	// Resource usage of the tasks
	CUMU_INTVAR	    limit;	// Resource capacity of the resource

	// Options
	CUMU_BOOL	idem;	// Whether the cumulative propagator should be idempotent
	CUMU_BOOL	tt_check;
	CUMU_BOOL	tt_filt;
	CUMU_BOOL	ttef_check;
	CUMU_BOOL	ttef_filt;

	ExplDeg     ttef_expl_deg;

    // Counters
    long nb_tt_incons;      // Number of timetabling inconsistencies
    long nb_tt_filt;        // Number of timetabling propagations
    long nb_ttef_incons;    // Number of timetabling-edge-finding inconsistencies
    long nb_ttef_filt;      // Number of timetabling-edge-finding propagations

	// Parameters
	CUMU_BOOL	bound_update;

	// Structures
	CUMU_ARR_INT task_id;		// Unfixed tasks on the left-hand side and fixed tasks on the right-hand size
	int * task_id_est;
	int * task_id_lct;
	int * tt_after_est;
	int * tt_after_lct;
	int * new_est;
	int * new_lct;
	int tt_profile_size;
	struct ProfilePart * tt_profile;

	// Inline functions
	struct SortEstAsc {
		CumulativeProp *p;
		bool operator() (int i, int j) { return p->est(i) < p->est(j); }
		SortEstAsc(CumulativeProp *_p) : p(_p) {}
	} sort_est_asc;

	struct SortLctAsc {
		CumulativeProp *p;
		bool operator() (int i, int j) { return p->lct(i) < p->lct(j); }
		SortLctAsc(CumulativeProp *_p) : p(_p) {}
	} sort_lct_asc;

	// Constructor
	//
	CumulativeProp(CUMU_ARR_INTVAR & _start, CUMU_ARR_INTVAR & _dur, CUMU_ARR_INTVAR & _usage, 
			CUMU_INTVAR _limit, list<string> opt)
	: name(""), start(_start), dur(_dur), usage(_usage), limit(_limit), 
		idem(false), tt_check(true), tt_filt(true), ttef_check(false), ttef_filt(false),
        nb_tt_incons(0), nb_tt_filt(0), nb_ttef_incons(0), nb_ttef_filt(0), 
		bound_update(false),
		sort_est_asc(this), sort_lct_asc(this)
	{
        // Overriding option defaults
        for (list<string>::iterator it = opt.begin(); it != opt.end(); it++) {
            if (!(*it).compare("tt_filt_on")) 
                tt_filt = true;
            else if (!(*it).compare("tt_filt_off")) 
                tt_filt = false;
            if (!(*it).compare("ttef_check_on"))
                ttef_check = true;
            else if (!(*it).compare("ttef_check_off"))
                ttef_check = false;
            if (!(*it).compare("ttef_filt_on"))
                ttef_filt = true;
            else if (!(*it).compare("ttef_filt_off"))
                ttef_filt = false;
            else if ((*it).find("__name__") == 0)
                name = (*it).substr(8);
        }
		//ttef_expl_deg = ED_NAIVE;
		//ttef_expl_deg = ED_NORMAL;
		ttef_expl_deg = ED_LIFT;
		// Allocation of the memory
		tt_profile = new ProfilePart[2 * start.size()];
		tt_profile_size = 0;
		// XXX Check for successful memory allocation
		if (ttef_check || ttef_filt) {
			task_id_est  = (int *) malloc(start.size() * sizeof(int));
			task_id_lct  = (int *) malloc(start.size() * sizeof(int));
			tt_after_est = (int *) malloc(start.size() * sizeof(int));
			tt_after_lct = (int *) malloc(start.size() * sizeof(int));
			if (ttef_filt) {
				new_est = (int *) malloc(start.size() * sizeof(int));
				new_lct = (int *) malloc(start.size() * sizeof(int));
			} else {
				new_est = NULL;
				new_lct = NULL;
			}
			// XXX Check for successful memory allocation
		} else {
			task_id_est  = NULL;
			task_id_lct  = NULL;
			tt_after_est = NULL;
		}
		
		// Priority of the propagator
		priority = 3;
#if CUMUVERB>0
		fprintf(stderr, "\tCumulative with n = %d\n", start.size());
#endif
        // Attach to var events
		for (int i = 0; i < start.size(); i++) {
#if CUMUVERB>1
			fprintf(stderr, "\t%d: %p\n", i, start[i]);
#endif
			start[i]->attach(this, i, EVENT_LU);
            if (min_dur(i) < max_dur(i)) dur[i]->attach(this, i, EVENT_LF);
            if (min_usage(i) < max_usage(i)) usage[i]->attach(this, i, EVENT_LF);
		}
		limit->attach(this, start.size(), EVENT_UF);
	
		for (int i = 0; i < start.size(); i++) {
			task_id.push(i);
		}
		last_unfixed = start.size() - 1;
	}
	
    // Statistics
	void printStats() {
        fprintf(stderr, "%% Cumulative propagator statistics");
        if (name != "")
            cerr << " for " << name;
        fprintf(stderr, ":\n");
        fprintf(stderr, "%%\t#TT incons.: %ld\n", nb_tt_incons);
        if (tt_filt) 
            fprintf(stderr, "%%\t#TT prop.: %ld\n", nb_tt_filt);
        if (ttef_check || ttef_filt)
            fprintf(stderr, "%%\t#TTEF incons.: %ld\n", nb_ttef_incons);
        if (ttef_filt) {
            fprintf(stderr, "%%\t#TTEF prop.: %ld\n", nb_ttef_filt);
		}
    }

	/**
	 * Inline function for parameters of tasks
	 **/
		// Earliest start time of task i
	inline CUMU_INT 
	est(CUMU_INT i) { return CUMU_PT_GETMIN(start[i]); }
		// Latest start time of task i
	inline CUMU_INT 
	lst(CUMU_INT i) { return CUMU_PT_GETMAX(start[i]); }
		// Earliest completion time of task i
	inline CUMU_INT 
	ect(CUMU_INT i) { return CUMU_PT_GETMIN(start[i]) + CUMU_PT_GETMIN(dur[i]); }
		// Latest completion time of task i
	inline CUMU_INT 
	lct(CUMU_INT i) { return CUMU_PT_GETMAX(start[i]) + CUMU_PT_GETMIN(dur[i]); }
		// Minimal resource usage of task i
	inline CUMU_INT
	min_usage(CUMU_INT i) { return CUMU_PT_GETMIN(usage[i]); }
		// Minimal energy of task i
	inline CUMU_INT
	min_energy(CUMU_INT i) { return min_usage(i) * min_dur(i); }
		// Free Energy
	inline CUMU_INT
	free_energy(CUMU_INT i) {
		return min_energy(i) - min_usage(i) * max(0, ect(i) - lst(i));
	}

	/**
	 * Inline functions for receiving the minimum and maximum of integer
	 * variables
	 **/
	inline CUMU_INT
	min_start0(CUMU_INT i) { return CUMU_PT_GETMIN0(start[i]); }
	inline CUMU_INT
	max_start0(CUMU_INT i) { return CUMU_PT_GETMAX0(start[i]); }
	inline CUMU_INT
	min_dur(CUMU_INT i) { return CUMU_PT_GETMIN(dur[i]); }
	inline CUMU_INT
	max_dur(CUMU_INT i) { return CUMU_PT_GETMAX(dur[i]); }
	inline CUMU_INT
	min_dur0(CUMU_INT i) { return CUMU_PT_GETMIN0(dur[i]); }
	inline CUMU_INT
	max_usage(CUMU_INT i) { return CUMU_PT_GETMAX(usage[i]); }
	inline CUMU_INT
	min_usage0(CUMU_INT i) { return CUMU_PT_GETMIN0(usage[i]); }

	inline CUMU_INT
	min_limit() { return CUMU_PT_GETMIN(limit); }
	inline CUMU_INT
	max_limit() { return CUMU_PT_GETMAX(limit); }
	inline CUMU_INT
	max_limit0() { return CUMU_PT_GETMAX0(limit); }

	// Cumulative Propagator
	CUMU_BOOL 
	propagate() {
#if CUMUVERB>0
		fprintf(stderr, "Entering cumulative propagation\n");
#endif
		int new_unfixed = last_unfixed;
		for (int ii = new_unfixed; ii >= 0; ii--) {
			int i = task_id[ii];
			if ((CUMU_PT_ISFIXED(start[i]) && CUMU_PT_ISFIXED(dur[i]) && CUMU_PT_ISFIXED(usage[i])) || max_dur(i) <= 0 || max_usage(i) <= 0) {
				// Swaping the id's
				task_id[ii] = task_id[new_unfixed];
				task_id[new_unfixed] = i;
				new_unfixed--;
			}
		}
		// Trailing the index of the last unfixed task
		last_unfixed = new_unfixed;
#if CUMUVERB>0
		fprintf(stderr, "\tEntering cumulative propagation loop\n");
#endif
		// idempotent
		do {
			bound_update = false;
			// Reseting the profile size
			tt_profile_size = 0;
			// Time-table propagators
			if (tt_check || tt_filt) {
				// Time-table propagation
				if (! time_table_propagation(task_id) ) {
					// Inconsistency was detected
#if CUMUVERB > 10
					fprintf(stderr, "Leaving cumulative propagation with failure\n");
#endif
					return false;
				}
			}
			// TODO Time-table-edge-finding propagation
			if (!bound_update && last_unfixed > 0 && (ttef_check || ttef_filt)) {
				// Initialisation of necessary structures
				// - Unfixed tasks sorted according earliest start time
				// - Unfixed tasks sorted according latest completion time
				// - Energy of the compulsory parts after the latest completion 
				// 	 time of unfixed tasks
				// - Energy of the compulsory parts after the earliest start
				//   time of unfixed tasks
				ttef_initialise_parameters();
				// TTEF consistency check
				//if (!ttef_consistency_check(get_free_dur_right_shift)) {
				//	// Inconsistency was detected
				//	return false;
				//}
				// TODO TTEF start time filtering algorithm
				if (ttef_filt) {
					if (!ttef_bounds_propagation(get_free_dur_right_shift, get_free_dur_left_shift)) {
						// Inconsistency was detected
						return false;
					}
				} else {
					if (!ttef_consistency_check(get_free_dur_right_shift)) {
						// Inconsistency was detected
						return false;
					}
				}
			}
            // TODO Optional task propagation
            if (!bound_update) {
                if (tt_filt && tt_profile_size > 0) {
                    if (!tt_optional_task_propagation()) {
                        // Inconsistency was detected
                        return false;
                    }
                }
            }
		} while (idem && bound_update);
#if CUMUVERB > 0
		fprintf(stderr, "\tLeaving cumulative propagation loop\n");
		fprintf(stderr, "Leaving cumulative propagation without failure\n");
#endif
		return true;
	}

	// Comparison between two compulsory parts
	static bool
	compare_CompParts(CompPart cp1, CompPart cp2) {
		if (cp1.begin < cp2.begin) return true;
		if (cp1.begin > cp2.begin) return false;
		// ASSUMPTION
		// - cp1.begin == cp2.begin
		if (cp1.end < cp2.end) return true;
		if (cp1.end > cp2.end) return false;
		// ASSUMPTION
		// - cp1.end == cp2.end
		if (cp1.task < cp2.task) return true;
		return false;
	}


	// Creation of the resource profile for the time-table consistency check
	// and propagator
	CUMU_BOOL
	time_table_propagation(CUMU_ARR_INT & task) {
		list<ProfileChangePt> changes;
		list<CUMU_INT> comp_task;
		//int size_profile = 0;

#if CUMUVERB>10
		fprintf(stderr, "\tCompulsory Parts ...\n");
#endif
		get_compulsory_parts2(changes, comp_task, task, 0, task.size());
		// Proceed if there are compulsory parts
		if (!changes.empty()) {
#if CUMUVERB>1
			fprintf(stderr, "\tSorting (size %d)...\n", (int) changes.size());
#endif
			// Sorting the start and end points of all the profile
			changes.sort(compare_ProfileChangePt);
#if CUMUVERB>1
			fprintf(stderr, "\tSorting (size %d)...\n", (int) changes.size());
#endif
			// Counting the number of different profiles
			tt_profile_size = count_profile(changes);
#if CUMUVERB>1
			fprintf(stderr, "\t#profile parts = %d\n", tt_profile_size);
#endif
#if CUMUVERB>1
			fprintf(stderr, "\tProfile Parts ...\n");
#endif
			// Creating the different profile parts
			create_profile(changes);
			int i_max_usage = 0;
#if CUMUVERB>1
			fprintf(stderr, "\tFilling of Profile Parts ...\n");
#endif
			// Filling the profile parts with tasks
			if (!fill_in_profile_parts(tt_profile, tt_profile_size, comp_task, i_max_usage)) {
				return false;
			}
#if CUMUVERB>10
			fprintf(stderr, "\tFiltering Resource Limit ...\n");
#endif
			// Filtering of resource limit variable
			if (!filter_limit(tt_profile, i_max_usage)) {
				return false;
			}
			if (tt_filt) {
#if CUMUVERB>10
				fprintf(stderr, "\tFiltering Start Times ...\n");
#endif
				// Time-table filtering
				if (!time_table_filtering(tt_profile, tt_profile_size, task, 0, last_unfixed, tt_profile[i_max_usage].level)) {
					return false;
				}
			}
		}
#if CUMUVERB>10
		fprintf(stderr, "\tEnd of time-table propagation ...\n");
#endif
		return true;
	}

	void
	get_compulsory_parts2(
		list<ProfileChangePt> &changes, list<CUMU_INT> &comp_task, CUMU_ARR_INT & task, 
		CUMU_INT i_start, CUMU_INT i_end
	);

	// Sets for each profile part its begin and end time in chronological order
	// Runtime complexity: O(n)
	//
	void
	create_profile(list<ProfileChangePt> &changes) {
		list<ProfileChangePt>::iterator iter = changes.begin();
		int cur_profile = 0;
		int cur_time = iter->time;
		ProfileChange cur_change = iter->change;
		int no_starts = 1;
		for (; iter != changes.end(); iter++) {
			if (iter->time > cur_time && no_starts > 1) {
#if CUMUVERB>20
				fprintf(stderr, "Set times for profile part %d = [%d, %d)\n", cur_profile, cur_time, iter->time);
				fprintf(stderr, "\t%p; %p; %d\n", tt_profile, this, start.size());
#endif
				set_times_for_profile(cur_profile, cur_time, iter->time);
				cur_profile++;
			}
			no_starts += (iter->change == PROFINC ? 1 : -1);
			cur_change = iter->change;
			cur_time = iter->time;
		}
	}
	
	inline void
	set_times_for_profile(int i, CUMU_INT begin, CUMU_INT end) {
		tt_profile[i].begin = begin;
		tt_profile[i].end = end;
		tt_profile[i].level = 0;
		//fprintf(stderr, "blxxx %d\n", (int) tt_profile[i].tasks.size());
		tt_profile[i].tasks.clear();
	}

	// Filling the profile parts with compulsory parts and checking for a resource
	// overload
	CUMU_BOOL
	fill_in_profile_parts(ProfilePart * profile, int size, list<CUMU_INT> comp_task, int & i_max_usage) {
		list<CUMU_INT>::iterator iter;
		int i = 0;
		CUMU_INT lst_i, ect_i;
		
#if CUMUVERB>2
		fprintf(stderr, "\t\tstart filling profiles (size %d)\n", size);
#endif
		for (iter = comp_task.begin(); iter != comp_task.end(); iter++) {
#if CUMUVERB>2
			fprintf(stderr, "\t\tcomp part = %d\n", *iter);
#endif
			lst_i = lst(*iter);
			ect_i = ect(*iter);
#if CUMUVERB>2
			fprintf(stderr, "\t\tFinding first profile part\n");
#endif
			// Find first profile
			i = find_first_profile(profile, 0, size - 1, lst_i);
#if CUMUVERB>2
			fprintf(stderr, "\t\tAdding comp parts of level %d\n", min_usage(*iter));
#endif
			// Add compulsory part to the profile
			while (i < size && profile[i].begin < ect_i) {
#if CUMUVERB>2
				fprintf(stderr, "\t\t\tAdding comp parts in profile part %d\n", i);
#endif
				profile[i].level += min_usage(*iter);
				profile[i].tasks.insert(*iter);
				// Checking if the profile part i is the part with the maximal level
				//
				if (profile[i].level > profile[i_max_usage].level) {
					i_max_usage = i;
				}
				// Time-table consistency check
				//
				if (profile[i].level > max_limit()) {
#if CUMUVERB > 20
					fprintf(stderr, "\t\t\tResource overload (%d > %d) in profile part %d\n", profile[i].level, max_limit(), i);
#endif
                    // Increment the inconsistency counter
                    nb_tt_incons++;

					// The resource is overloaded in this part
					vec<Lit> expl;
					if (so.lazy) {
						CUMU_INT lift_usage = profile[i].level - max_limit() - 1;
						CUMU_INT begin1, end1;
						// TODO Different choices to pick the interval
						// Pointwise explanation
						begin1 = profile[i].begin + ((profile[i].end - profile[i].begin) / 2);
						end1 = begin1 + 1;
						// Generation of the explanation
						analyse_limit_and_tasks(
							expl, profile[i].tasks, lift_usage, begin1, end1
						);
					}
					// Submitting of the conflict explanation
					submit_conflict_explanation(expl);
#if CUMUVERB > 20
					fprintf(stderr, "\t\tend filling (conflict)\n");
#endif
					return false;
				}
				i++;
			}
		}
#if CUMUVERB>2
		fprintf(stderr, "\t\tend filling (successful)\n");
#endif
		return true;
	}

	// Finds the profile part that begins at the time unit "lst"
	// Complexity: O(log(high - low + 1))
	//
	int
	find_first_profile(ProfilePart * profile, int low, int high, CUMU_INT lst) {
		int median = 0;
		while (profile[low].begin != lst) {
			median = low + (high - low + 1) / 2;
			if (profile[median].begin > lst) {
				high = median;
			} else {
				low = median;
			}
		}
		return low;
	}

	// Counting the number of profiles
	//
	int
	count_profile(list<ProfileChangePt> &changes) {
		list<ProfileChangePt>::iterator iter = changes.begin();
		int cur_time = iter->time;
		int next_time;
		ProfileChange cur_change = iter->change;
		int no_starts = ( iter->change == PROFINC ? 1 : 0 );
		int no_profile = no_starts;
		iter++;

#if CUMUVERB>2
		fprintf( stderr, "\t\t\ttime = %d; change = %d; no_starts = %d; no_profile = %d;\n", cur_time, cur_change, no_starts, no_profile);
#endif
		for (; iter != changes.end(); iter++) {
			if (iter->change == PROFINC) {
				if (cur_time < iter->time || cur_change == PROFDEC) {
					no_profile++;
				}
				no_starts++;
			} else {
				// ASSUMPTION
				// - iter->change = PROFDEC
				no_starts--;
				next_time = iter->time;
				iter++;
				if (iter != changes.end() && no_starts > 0 && iter->time > next_time) {
					no_profile++;
				}
				iter--;
			}
			cur_time = iter->time;
			cur_change = iter->change;
#if CUMUVERB>2
			fprintf( stderr, "\t\t\ttime = %d; change = %d; no_starts = %d; no_profile = %d;\n", cur_time, cur_change, no_starts, no_profile);
#endif
		}
		return no_profile;
	}

	static bool
	compare_ProfileChangePt(ProfileChangePt & pt1, ProfileChangePt & pt2) {
		if (pt1.time == pt2.time && pt1.change == PROFDEC && pt2.change == PROFINC) return true;
		return pt1.time < pt2.time;
	}

	// Time-table filtering on the lower bound of the resource limit variable
	// Complexity:
	CUMU_BOOL
	filter_limit(ProfilePart * profile, int & i_max_usage);

	// Time-table filtering on the start time variables
	// Complexity:
	CUMU_BOOL
	time_table_filtering(ProfilePart profile[], int size, CUMU_ARR_INT & task, int start, int end, CUMU_INT max_usage);
	CUMU_BOOL
	time_table_filtering_lb(ProfilePart profile[], int low, int high, int task);
	CUMU_BOOL
	time_table_filtering_ub(ProfilePart profile[], int low, int high, int task);
	
	int
	find_first_profile_for_lb(ProfilePart profile[], int low, int high, CUMU_INT t);
	int
	find_first_profile_for_ub(ProfilePart profile[], int low, int high, CUMU_INT t);

    // Time-table filtering for optional tasks
    CUMU_BOOL
    tt_optional_task_propagation();

	// Analysing the conflict and generation of the explanations
	// NOTE: Fixed durations and resource usages are assumed!!!
	// 
	// Explanation is created for the time interval [begin, end), i.e., exluding end.
	//
	void
	analyse_limit_and_tasks(vec<Lit> & expl, set<CUMU_INT> & tasks, CUMU_INT lift_usage, CUMU_INT begin, CUMU_INT end);
	void
	analyse_tasks(vec<Lit> & expl, set<CUMU_INT> & tasks, CUMU_INT lift_usage, CUMU_INT begin, CUMU_INT end);
	void
	submit_conflict_explanation(vec<Lit> & expl);
	Clause *
	get_reason_for_update(vec<Lit> & expl);

	// TODO Disentailment check
	//CUMU_INT 
	//checkSatisfied() {
	//	// XXX Until no cumulative propagator is implemented the constraint
	//	// is always ?satisfied?
	//	return 1;
	//}

	// Wrapper to get the negated literal -[[v <= val]] = [[v >= val + 1]]
	inline Lit
	getNegLeqLit(CUMU_INTVAR v, CUMU_INT val) { 
		//return v->getLit(val + 1, 2); 
		return (INT_VAR_LL == v->getType() ? v->getMaxLit() : v->getLit(val + 1, 2));
	}
	// Wrapper to get the negated literal -[[v >= val]] = [[ v <= val - 1]]
	inline Lit
	getNegGeqLit(CUMU_INTVAR v, CUMU_INT val) { 
		//return v->getLit(val - 1, 3); 
		return (INT_VAR_LL == v->getType() ? v->getMinLit() : v->getLit(val - 1, 3));
	}

	// TTEF Propagator
	//
	void ttef_initialise_parameters();
	bool ttef_consistency_check(int shift_in(const int, const int, const int, const int, const int, const int, const int));
	bool ttef_bounds_propagation(int shift_in1(const int, const int, const int, const int, const int, const int, const int),
			int shift_in2(const int, const int, const int, const int, const int, const int, const int));
	bool ttef_bounds_propagation_lb(int shift_in(const int, const int, const int, const int, const int, const int, const int),
			std::queue<TTEFUpdate> & update_queue);
	bool ttef_bounds_propagation_ub(int shift_in(const int, const int, const int, const int, const int, const int, const int),
			std::queue<TTEFUpdate> & update_queue);
	bool ttef_update_bounds(int shift_in(const int, const int, const int, const int, const int, const int, const int), 
			std::queue<TTEFUpdate> & queue_update);

	int
	ttef_retrieve_tasks(int shift_in(const int, const int, const int, const int, const int, const int, const int), 
		int begin, int end, int fb_id, list<TaskDur> & tasks_tw, list<TaskDur> & tasks_cp);

		// TTEF Generation of explanations
		//
	void
	ttef_analyse_limit_and_tasks(const int begin, const int end, list<TaskDur> & tasks_tw,
		list<TaskDur> & tasks_cp, int & en_lift, vec<Lit> & expl);
	void
	ttef_analyse_tasks(const int begin, const int end, list<TaskDur> & tasks, int & en_lift, vec<Lit> & expl);

	inline bool
	is_intersecting(const int begin1, const int end1, const int begin2, const int end2);

		// Shift functions
		//
	static inline int
	get_free_dur_right_shift(const int tw_begin, const int tw_end, const int est, const int ect, 
		const int lst, const int lct, const int dur_fixed_in)
	{
		return (tw_begin <= est ? max(0, tw_end - lst - dur_fixed_in) : 0);
	}

	static inline int
	get_free_dur_left_shift(const int tw_begin, const int tw_end, const int est, const int ect, 
		const int lst, const int lct, const int dur_fixed_in)
	{
		return (tw_end >= lct ? max(0, ect - tw_begin - dur_fixed_in) : 0);
	}

	static inline int
	get_no_shift(const int tw_begin, const int tw_end, const int est, const int ect, 
		const int lst, const int lct, const int dur_fixed_in)
	{ 
		return 0;
	}
};

/****
 * Functions related to the Time-Table Consistency Check and Propagation
 ****/

void
CumulativeProp::get_compulsory_parts2(
	list<ProfileChangePt> &changes, list<CUMU_INT> &comp_task, CUMU_ARR_INT & task, CUMU_INT i_start, CUMU_INT i_end
) {
	CUMU_INT i;
#if CUMUVERB>2
	fprintf(stderr, "\tstart get_compulsory_part from %d to %d\n", i_start, i_end);
#endif
	for (i = i_start; i < i_end; i++) {
#if CUMUVERB>2
		fprintf(stderr, "\t\ti = %d; task[i] = %d\n", i, task[i]);
#endif
		// Check whether the task creates a compulsory part
		if (min_dur(task[i]) > 0 && min_usage(task[i]) > 0 && lst(task[i]) < ect(task[i])) {
#if CUMUVERB>2
			fprintf(stderr, "\t\ttask[i] = %d, comp part [%d, %d)\n", task[i], lst(task[i]), ect(task[i]));
#endif
			// Add task to the list
			comp_task.push_back(task[i]);
			// Add time points to change lists
			changes.push_back( ProfileChangePt(lst(task[i]), PROFINC) );
			changes.push_back( ProfileChangePt(ect(task[i]), PROFDEC) );
		}
	}
#if CUMUVERB>2
	fprintf(stderr, "\tend get_compulsory_part\n");
#endif
}


/***************************************************************************************
 * Function for time-table filtering on the lower bound of the resource limit variable *
 ***************************************************************************************/

CUMU_BOOL
CumulativeProp::filter_limit(ProfilePart * profile, int & i) {
	if (min_limit() < profile[i].level) {
		Clause * reason = NULL;
        nb_tt_filt++;
		if (so.lazy) {
			// Lower bound can be updated
			// XXX Determining what time period is the best
			int expl_begin = profile[i].begin + ((profile[i].end - profile[i].begin - 1)/2);
			int expl_end = expl_begin + 1;
			vec<Lit> expl;
			// Get the negated literals for the tasks in the profile
			analyse_tasks(expl, profile[i].tasks, 0, expl_begin, expl_end);
			// Transform literals to a clause
			reason = get_reason_for_update(expl);
		}
		if (! limit->setMin(profile[i].level, reason)) {
			// Conflict occurred
			return false;
		}
		// Set bound_update to true
		bound_update = true;
	}
	return true;
}

/******************************************************************
 * Functions for Time-Table Filtering on the start time variables *
 ******************************************************************/

CUMU_BOOL
CumulativeProp::time_table_filtering(ProfilePart profile[], int size, CUMU_ARR_INT & task, int i_start, int i_end, CUMU_INT max_usage) {
	for (int i = i_start; i <= i_end; i++) {
        // Skipping tasks with zero duration or usage
        if (min_dur(task[i]) <= 0 || min_usage(task[i]) <= 0)
            continue;
#if CUMUVERB>0
		fprintf(stderr, "TT Filtering of task %d\n", task[i]);
#endif
		// Check if the sum of max_usage and the task's usage are greater then the upper bound
		// on the resource limit
		if (min_usage(task[i]) + max_usage > max_limit()) {
			int index;
#if CUMUVERB>0
			fprintf(stderr, "Finding the first index for LB ...\n");
#endif
				// Find initial profile part for lower bound propagation
				//
			index = find_first_profile_for_lb(profile, 0, size - 1, est(task[i]));
#if CUMUVERB>0
			fprintf(stderr, "Lower bound starting from index %d till index %d\n", index, size - 1);
#endif
			// Update the lower bound if possible
			if (! time_table_filtering_lb(profile, index, size - 1, task[i])) {
				return false;
			}
#if CUMUVERB>0
			fprintf(stderr, "Finding the first index for UB ...\n");
#endif
			// Find initial profile part for upper bound propagation
			index = find_first_profile_for_ub(profile, 0, size - 1, lct(task[i]));
#if CUMUVERB>0
			fprintf(stderr, "Upper bound starting from index %d till index 0\n", index);
#endif
			// Update the upper bound if possible
			if (! time_table_filtering_ub(profile, 0, index, task[i])) {
				return false;
			}
		}
	}
	return true;
}

	// Time-Table Filtering on the Lower Bound of Start Times Variables
	//
CUMU_BOOL
CumulativeProp::time_table_filtering_lb(ProfilePart profile[], int low, int high, int task) {
	int i;
#if CUMUVERB>5
    fprintf(stderr, "task %d: start [%d, %d], end [%d, %d], min usage %d\n", task, est(task), lst(task), ect(task), lct(task), min_usage(task));
#endif
	for (i = low; i <= high; i++) {
#if CUMUVERB>5
        fprintf(stderr, "\tprofile[%d]: begin %d; end %d; level %d;\n", i, profile[i].begin, profile[i].end, profile[i].level);
#endif
		if (ect(task) <= profile[i].begin) {
			// No lower bound update possible
			break;
		}
		// ASSUMPTION
		// - ect(task) > profile[i].begin
		if (est(task) < profile[i].end && profile[i].level + min_usage(task) > max_limit()) {
			// Possibly a lower bound update if "task" as no compulsory part in the profile
			if (lst(task) < ect(task) && lst(task) <= profile[i].begin && profile[i].end <= ect(task)) {
				// No lower bound update possible for this profile part, because 
				// "task" has a compulsory part in it
				continue ;
			}
#if CUMUVERB>1
			fprintf(stderr, "\n----\n");
			fprintf(stderr, "setMin of task %d in profile part [%d, %d)\n", task, profile[i].begin, profile[i].end);
			fprintf(stderr, "task %d: lst = %d; ect = %d; dur = %d;\n", task, lst(task), ect(task), min_dur(task));
#endif
			int expl_end = profile[i].end;
			Clause * reason = NULL;
			if (so.lazy) {
				// XXX Assumption for the remaining if-statement
				//   No compulsory part of task in profile[i]!
				int lift_usage = profile[i].level + min_usage(task) - max_limit() - 1;
				// TODO Choices of different explanation
				// Pointwise explanation
				expl_end = min(ect(task), profile[i].end);
				int expl_begin = expl_end - 1;
				vec<Lit> expl;
				// Get the negated literal for [[start[task] >= ex_end - min_dur(task)]]
#if CUMUVERB>1
				fprintf(stderr, "start[%d] => %d ", task, expl_end - min_dur(task));
#endif
				expl.push(getNegGeqLit(start[task], expl_end - min_dur(task)));
                // Get the negated literal for [[dur[task] >= min_dur(task)]]
                if (min_dur0(task) < min_dur(task)) 
                    expl.push(getNegGeqLit(dur[task], min_dur(task)));
                // Get the negated literal for [[usage[task] >= min_usage(task)]]
                if (min_usage0(task) < min_usage(task)) 
                    expl.push(getNegGeqLit(usage[task], min_usage(task)));
				// Get the negated literals for the tasks in the profile and the resource limit
				analyse_limit_and_tasks(expl, profile[i].tasks, lift_usage, expl_begin, expl_end);
#if CUMUVERB>1
				fprintf(stderr, " -> start[%d] => %d\n", task, expl_end);
#endif
				// Transform literals to a clause
				reason = get_reason_for_update(expl);
			}
            nb_tt_filt++;
			// Impose the new lower bound on start[task]
			if (! start[task]->setMin(expl_end, reason)) {
				// Conflict occurred
				return false;
			}
			// Set bound_update to true
			bound_update = true;
			// Check for the next profile
			if (expl_end < profile[i].end) {
				i--;
			}
		}
	}
	return true;
}

	// Time-table filtering on the upper bound of start times variables
	//
CUMU_BOOL
CumulativeProp::time_table_filtering_ub(ProfilePart profile[], int low, int high, int task) {
	int i;
#if CUMUVERB>5
    fprintf(stderr, "task %d: start [%d, %d], end [%d, %d], min usage %d\n", task, est(task), lst(task), ect(task), lct(task), min_usage(task));
#endif
	for (i = high; i >= low; i--) {
#if CUMUVERB>5
        fprintf(stderr, "\tprofile[%d]: begin %d; end %d; level %d;\n", i, profile[i].begin, profile[i].end, profile[i].level);
#endif
		if (profile[i].end <= lst(task)) {
			// No upper bound update possible
			break;
		}
		// ASSUMPTION for the remaining for-loop
		// - profile[i].end > lst(task)
		if (profile[i].begin < lct(task) && profile[i].level + min_usage(task) > max_limit()) {
			// Possibly a upper bound update possible if "task" has no compulsory part 
			// in this profile part
			if (lst(task) < ect(task) && lst(task) <= profile[i].begin && profile[i].end <= ect(task)) {
				// No lower bound update possible for this profile part, because 
				// "task" has a compulsory part in it
				continue ;
			}
			int expl_begin = profile[i].begin;
			Clause * reason = NULL;
			if (so.lazy) {
				// ASSUMPTION for the remaining if-statement
				// - No compulsory part of task in profile[i]
				int lift_usage = profile[i].level + min_usage(task) - max_limit() - 1;
				// TODO Choices of different explanations
				// Pointwise explanation
				expl_begin = max(profile[i].begin, lst(task));
				int expl_end = expl_begin + 1;
				vec<Lit> expl;
				// Get the negated literal for [[start[task] <= expl_begin]]
				expl.push(getNegLeqLit(start[task], expl_begin));
                // Get the negated literal for [[dur[task] >= min_dur(task)]]
                if (min_dur0(task) < min_dur(task)) 
                    expl.push(getNegGeqLit(dur[task], min_dur(task)));
                // Get the negated literal for [[usage[task] >= min_usage(task)]]
                if (min_usage0(task) < min_usage(task)) 
                    expl.push(getNegGeqLit(usage[task], min_usage(task)));
				// Get the negated literals for the tasks in the profile and the resource limit
				analyse_limit_and_tasks(expl, profile[i].tasks, lift_usage, expl_begin, expl_end);
				// Transform literals to a clause
				reason = get_reason_for_update(expl);
			}
            nb_tt_filt++;
			// Impose the new lower bound on start[task]
			if (! start[task]->setMax(expl_begin - min_dur(task), reason)) {
				// Conflict occurred
				return false;
			}
			// Set bound_update to true
			bound_update = true;
			// Check for the next profile
			if (profile[i].begin < expl_begin) {
				i++;
			}
		}
	}
	return true;
}

CUMU_BOOL
CumulativeProp::tt_optional_task_propagation() {
    for (int ii = 0; ii <= last_unfixed; ii++) {
        const int i = task_id[ii];
        assert(max_dur(i) > 0 && max_usage(i) > 0);
        if (min_dur(i) <= 0 || min_usage(i) <= 0) {
            //fprintf(stderr, "task %d: start [%d, %d], dur %d, usage %d\n", i, est(i), lst(i), min_dur(i), min_usage(i));
            // Getting the smallest non-zero value for the duration
            const int dur_smallest = max(1, min_dur(i));
            // Getting the smallest non-zero value for the usage
            const int usage_smallest = max(1, min_usage(i));
            // XXX Only for the moment to make the propagation easier
            if (est(i) < lst(i))
                continue;
            // Getting the starting profile index
			const int index = find_first_profile_for_lb(tt_profile, 0, tt_profile_size - 1, est(i));
            // TODO Check whether a task with a duration 'dur_smallest' and a usage 'usage_smallest'
            // can be scheduled
            //fprintf(stderr, "%d: start %d; profile (%d, %d, %d)\n", i, est(i), tt_profile[index].begin, tt_profile[index].end, tt_profile[index].level);
            if (est(i) < tt_profile[index].end && tt_profile[index].begin < est(i) + dur_smallest 
                && tt_profile[index].level + usage_smallest > max_limit()) {
                // Tasks cannot be performed on this resource

                Clause * reason = NULL;
                if (so.lazy) {
                    // Explanation for the propagation required
				    vec<Lit> expl;

                    // Lifting the usage
                    int lift_usage = tt_profile[index].level + usage_smallest - max_limit() - 1;
                    // Defining explanation time interval
                    const int overlap_begin = max(tt_profile[index].begin, est(i));
                    const int overlap_end   = min(tt_profile[index].end, est(i) + dur_smallest);
                    const int expl_begin = overlap_begin + ((overlap_end - overlap_begin - 1)/2);
                    const int expl_end   = expl_begin + 1;
				    
                    // Explanation parts for task 'i'
                    // Get the negated literal for [[start[i] >= expl_end - dur_smallest]]
				    expl.push(getNegGeqLit(start[i], expl_end - dur_smallest));
				    // Get the negated literal for [[start[task] <= expl_begin]]
				    expl.push(getNegLeqLit(start[i], expl_begin));
                    // Get the negated literal for [[dur[i] >= min_dur(i)]]
                    if (min_dur0(i) < min_dur(i) && 0 < min_dur(i)) 
                        expl.push(getNegGeqLit(dur[i], min_dur(i)));
                    // Get the negated literal for [[usage[i] >= min_usage(i)]]
                    if (min_usage0(i) < min_usage(i) && 0 < min_usage(i)) 
                        expl.push(getNegGeqLit(usage[i], min_usage(i)));

				    // Get the negated literals for the tasks in the profile and the resource limit
				    analyse_limit_and_tasks(expl, tt_profile[index].tasks, lift_usage, expl_begin, expl_end);
				    // Transform literals to a clause
				    reason = get_reason_for_update(expl);
                }
                // Increment filtering counter
                nb_tt_filt++;
                if (min_usage(i) <= 0) {
			        // Impose the new upper bound on usage[i]
			        if (! usage[i]->setMax(0, reason)) {
			        	// Conflict occurred
			        	return false;
			        }
                }
                else {
			        // Impose the new upper bound on usage[i]
			        if (! dur[i]->setMax(0, reason)) {
			        	// Conflict occurred
			        	return false;
			        }
                }
            }
        }
    }
    return true;
}

int
CumulativeProp::find_first_profile_for_lb(ProfilePart profile[], int low, int high, CUMU_INT t) {
	int median;
	if (profile[low].end > t || low == high) {
		return low;
	}
	if (profile[high].begin <= t) {
		return high;
	}
#if CUMUVERB>0
	fprintf(stderr, "time = %d\n", t);
	fprintf(stderr, "profile[low = %d] = [%d, %d); ", low, profile[low].begin, profile[low].end);
	fprintf(stderr, "profile[high = %d] = [%d, %d);\n", high, profile[high].begin, profile[high].end);
#endif
	// ASSUMPTIONS:
	// - profile[low].end <= t
	// - profile[high].begin > t
	// - low < high
	//
	while (!(profile[low].end <= t && t <= profile[low + 1].end)) {
		median = low + (high - low + 1) / 2;
#if CUMUVERB>0
		fprintf(stderr, "profile[lo = %d] = [%d, %d); ", low, profile[low].begin, profile[low].end);
		fprintf(stderr, "profile[me = %d] = [%d, %d); ", median, profile[median].begin, profile[median].end);
		fprintf(stderr, "profile[hi = %d] = [%d, %d);\n", high, profile[high].begin, profile[high].end);
#endif
		if (t < profile[median].end) {
			high = median;
			//high = median - 1;
			low++;
		} else {
			low = median;
		}
	}
	return low;
}

int
CumulativeProp::find_first_profile_for_ub(ProfilePart profile[], int low, int high, CUMU_INT t) {
	int median;
	if (profile[high].begin <= t || low == high) {
		return high;
	}
	if (t < profile[low].end) {
		return low;
	}
	// ASSUMPTIONS:
	// - profile[high].begin > t
	// - profile[low].end <= t
	// - low < high
	//
	while (!(profile[high - 1].begin <= t && t < profile[high].begin)) {
		median = low + (high - low + 1) / 2;
		if (t < profile[median].begin) {
			high = median;
		} else {
			low = median;
			high--;
		}
	}
	return high;
}


/************************************************************************
 * Functions for Analysing Conflicts or Bound Updates and Generation of *
 * their explanations                                                   *
 ************************************************************************/

void
CumulativeProp::analyse_limit_and_tasks(vec<Lit> & expl, set<CUMU_INT> & tasks, CUMU_INT lift_usage, CUMU_INT begin, CUMU_INT end) {
	CUMU_INT diff_limit = max_limit0() - max_limit();
	if (diff_limit > 0) {
		// Lifting of limit variable if possible
		if (diff_limit <= lift_usage) {
			// No explanation literal is needed
			lift_usage -= diff_limit;
		} else {
			lift_usage = 0;
			// Get explanation for [[limit <= max_limit() + lift_usage]]
#if CUMUVERB > 10
			fprintf(stderr, "/\\ limit <= %d ", max_limit() + lift_usage);
#endif
			expl.push(getNegLeqLit(limit, max_limit() + lift_usage));
		}
	}
	analyse_tasks(expl, tasks, lift_usage, begin, end);
}

void
CumulativeProp::analyse_tasks(vec<Lit> & expl, set<CUMU_INT> & tasks, CUMU_INT lift_usage, CUMU_INT begin, CUMU_INT end) {
	set<CUMU_INT>::iterator iter;
	for (iter = tasks.begin(); iter != tasks.end(); iter++) {
#if CUMUVERB > 10
		fprintf(stderr, "\ns[%d] in [%d..%d]\n", *iter, start[*iter]->getMin(), start[*iter]->getMax());
#endif
		if (min_usage(*iter) <= lift_usage) {
			// Task is not relevant for the resource overload
			lift_usage -= min_usage(*iter);
		} else {
			// Task is relevant for the resource overload
			if (min_start0(*iter) + min_dur(*iter) <= end) {
				// Lower bound of the start time variable matters
				// Get explanation for [[start[*iter] >= end - min_dur(*iter)]]
#if CUMUVERB > 10
				fprintf(stderr, "/\\ start[%d] => %d ", *iter, end - min_dur(*iter));
#endif
				expl.push(getNegGeqLit(start[*iter], end - min_dur(*iter)));
			}
			if (begin < max_start0(*iter)) {
				// Upper bound of the start time variable matters
				// Get explanation for [[start[*iter] <= begin]]
#if CUMUVERB > 10
				fprintf(stderr, "/\\ start[%d] <= %d ", *iter, begin);
#endif
				expl.push(getNegLeqLit(start[*iter], begin));
			}
            // Get the negated literal for [[dur[*iter] >= min_dur(*iter)]]
            if (min_dur0(*iter) < min_dur(*iter)) 
                expl.push(getNegGeqLit(dur[*iter], min_dur(*iter)));
            // Get the negated literal for [[usage[*iter] >= min_usage(*iter)]]
            const CUMU_INT usage_diff = min_usage(*iter) - min_usage0(*iter);
            if (usage_diff > 0) { 
                if (usage_diff <= lift_usage)
                    lift_usage -= usage_diff;
                else
                    expl.push(getNegGeqLit(usage[*iter], min_usage(*iter)));
            }
		}
	}
}

void
CumulativeProp::submit_conflict_explanation(vec<Lit> & expl) {
	Clause * reason = NULL;
	if (so.lazy) {
		reason = Reason_new(expl.size());
		int i = 0;
		for (; i < expl.size(); i++) { (*reason)[i] = expl[i]; }
	}
	sat.confl = reason;
}

Clause *
CumulativeProp::get_reason_for_update(vec<Lit> & expl) {
	Clause* reason = Reason_new(expl.size() + 1);
	for (int i = 1; i <= expl.size(); i++) {
		(*reason)[i] = expl[i-1];
	}
	return reason;
}


	// XXX Which version of the cumulative constraint should be used?
	// Lifting the limit parameter to an integer variable
	//
void cumulative(vec<IntVar*>& s, vec<int>& d, vec<int>& r, int limit) {
    std::list<string> opt;
    cumulative(s, d, r, limit, opt);
}

void cumulative(vec<IntVar*>& s, vec<int>& d, vec<int>& r, int limit, std::list<string> opt) {
	rassert(s.size() == d.size() && s.size() == r.size());
	// ASSUMPTION
	// - s, d, and r contain the same number of elements
	
    // Option switch
    if (so.cumu_global) {
        vec<IntVar*> s_new, d_new, r_new;
		IntVar * vlimit = newIntVar(limit, limit);
        int r_sum = 0;
	    
        for (int i = 0; i < s.size(); i++) {
	    	if (r[i] > 0 && d[i] > 0) {
	    		s_new.push(s[i]);
	    		d_new.push(newIntVar(d[i], d[i]));
	    		r_new.push(newIntVar(r[i], r[i]));
	    		r_sum += r[i];
	    	}
        }
		
        if (r_sum <= limit) return;

        // Global cumulative constraint
        new CumulativeProp(s_new, d_new, r_new, vlimit, opt);
    } else {
	    vec<IntVar*> s_new;
	    vec<int> d_new, r_new;
	    int r_sum = 0;
	    for (int i = 0; i < s.size(); i++) {
	    	if (r[i] > 0 && d[i] > 0) {
	    		s_new.push(s[i]);
	    		d_new.push(d[i]);
	    		r_new.push(r[i]);
	    		r_sum += r[i];
	    	}
        }
	    
        if (r_sum <= limit) return;

		// Time-indexed decomposition
        timed_cumulative(s_new, d_new, r_new, limit);
	}
}

void cumulative2(vec<IntVar*>& s, vec<IntVar*>& d, vec<IntVar*>& r, IntVar* limit) {
    std:list<string> opt;
    cumulative2(s, d, r, limit, opt);
}

void cumulative2(vec<IntVar*>& s, vec<IntVar*>& d, vec<IntVar*>& r, IntVar* limit, std::list<string> opt) {
	rassert(s.size() == d.size() && s.size() == r.size());
	// ASSUMPTION
	// - s, d, and r contain the same number of elements
    
    vec<IntVar*> s_new, d_new, r_new;
    int r_sum = 0;
	
    for (int i = 0; i < s.size(); i++) {
		if (r[i]->getMax() > 0 && d[i]->getMax() > 0) {
			s_new.push(s[i]);
			d_new.push(d[i]);
			r_new.push(r[i]);
			r_sum += r[i]->getMax();
		}
    }
	
    if (r_sum <= limit->getMin()) return;

    // Global cumulative constraint
    new CumulativeProp(s_new, d_new, r_new, limit, opt);
}

/********************************************
 * Functions related to the TTEF propagator
 *******************************************/

	// Initialisation of various parameters
	//
void
CumulativeProp::ttef_initialise_parameters() {
	int energy = 0;
	int p_idx = tt_profile_size - 1;

		// Initialisation of the task id's arrays
		//
	for (int ii = 0; ii <= last_unfixed; ii++) {
		task_id_est[ii] = task_id[ii];
		task_id_lct[ii] = task_id[ii];
	}
	if (ttef_filt) {
		for (int ii = 0; ii <= last_unfixed; ii++) {
			new_est[task_id[ii]] = est(task_id[ii]);
			new_lct[task_id[ii]] = lct(task_id[ii]);
		}
	}
		// Sorting of the task id's arrays
		//
	sort(task_id_est, task_id_est + last_unfixed + 1, sort_est_asc);
	sort(task_id_lct, task_id_lct + last_unfixed + 1, sort_lct_asc);
		// Calculation of 'tt_after_est'
		//
	for (int ii = last_unfixed; ii >= 0; ii--) {
		int i = task_id_est[ii];
		if (p_idx < 0 || tt_profile[p_idx].end <= est(i)) {
			tt_after_est[ii] = energy;
		} else if (tt_profile[p_idx].begin <= est(i)) {
			tt_after_est[ii] = energy + tt_profile[p_idx].level * (tt_profile[p_idx].end - est(i));
		} else {
			assert(tt_profile[p_idx].begin > est(i));
			energy += tt_profile[p_idx].level * (tt_profile[p_idx].end - tt_profile[p_idx].begin);
			p_idx--;
			ii++;
		} 
	}  
		// Calculation of 'tt_after_lct'
		//
    p_idx = tt_profile_size - 1;
	energy = 0;
	for (int ii = last_unfixed; ii >= 0; ii--) {
		unsigned i = task_id_lct[ii];
		if (p_idx < 0 || tt_profile[p_idx].end <= lct(i)) {
			tt_after_lct[ii] = energy;
		} else if (tt_profile[p_idx].begin <= lct(i)) {
			tt_after_lct[ii] = energy + tt_profile[p_idx].level * (tt_profile[p_idx].end - lct(i));
		} else {
			assert(tt_profile[p_idx].begin > lct(i));
			energy += tt_profile[p_idx].level * (tt_profile[p_idx].end - tt_profile[p_idx].begin);
			p_idx--;
			ii++;
		}
	}
}

	// TTEF Consistency Check
	//	Assumptions:
	//	- task_id_est sorted in non-decreasing order of est's
	//	- task_id_lct sorted in non-decreasing order of lct's
bool
CumulativeProp::ttef_consistency_check(
	int shift_in(const int, const int, const int, const int, const int, const int, const int)
) {
	assert(last_unfixed > 0);
	int begin, end;		// Begin and end of the time interval [begin, end)
	int est_idx_last = last_unfixed;
	int i, j, en_req, en_avail;
	int en_req_free;
	int min_en_avail = -1, lct_idx_last = last_unfixed, i_last = task_id_lct[lct_idx_last];
	bool consistent = true;
	
	end = lct(task_id_lct[last_unfixed]) + 1;

		// Outer Loop: iterating over lct in non-increasing order
		//
	for (int ii = last_unfixed; ii >= 0; ii--) {
		i = task_id_lct[ii];
		if (end == lct(i) || min_energy(i) == 0) continue;
			
			// Check whether the current latest completion time have to be considered
		int free = max_limit() * (lct(i_last) - lct(i)) - (tt_after_lct[ii] - tt_after_lct[lct_idx_last]);
		if (min_en_avail >= free) continue;
		lct_idx_last = ii;
		i_last = i;
		min_en_avail = max_limit() * (lct(task_id_lct[last_unfixed]) - est(task_id_est[0]));
		
		end = lct(i);
		while (est(task_id_est[est_idx_last]) >= end) est_idx_last--; 
		en_req_free = 0;

			// Inner Loop: iterating over est in non-increasing order
			//
		for (int jj = est_idx_last; jj >= 0; jj--) {
			j = task_id_est[jj];
            if (min_energy(j) == 0) continue;
			assert(est(j) < end);
			begin = est(j);
			if (lct(j) <= end) {
				// Task lies in the considered time interval	
				en_req_free += free_energy(j);
			} else {
				// Task might partially lie in the considered time interval
				int dur_fixed = max(0, ect(j) - lst(j));
				int dur_shift = shift_in(begin, end, est(j), ect(j), lst(j), lct(j), dur_fixed);
				en_req_free += min_usage(j) * dur_shift;
			}
			en_req = en_req_free + tt_after_est[jj] - tt_after_lct[ii];
			en_avail = max_limit() * (end - begin) - en_req;

			min_en_avail = min(min_en_avail, en_avail);

				// Check for resource overload
				//
			if (en_avail < 0) {
				consistent = false;
				ii = -1;
				break;
			}
		}
	}

	if (!consistent) {
		vec<Lit> expl;
        // Increment the inconsistency counter
        nb_ttef_incons++;
		if (so.lazy) {
			list<TaskDur> tasks_tw;
			list<TaskDur> tasks_cp;
			int en_req1 = 0;
			// Retrieve tasks involved
			en_req1 = ttef_retrieve_tasks(shift_in, begin, end, -1, tasks_tw, tasks_cp);
			assert(en_req1 >= en_req);
			// Calculate the lifting
			int en_lift = en_req1 - 1 - max_limit() * (end - begin);
			assert(en_lift >= 0);
			// Explaining the overload
			ttef_analyse_limit_and_tasks(begin, end, tasks_tw, tasks_cp, en_lift, expl);
		}
		assert(expl.size() > 0);
		// Submitting of the conflict explanation
		submit_conflict_explanation(expl);
	}
	return consistent;
}

	// TTEF bounds propagation
	//
bool
CumulativeProp::ttef_bounds_propagation(
	int shift_in1(const int, const int, const int, const int, const int, const int, const int),
	int shift_in2(const int, const int, const int, const int, const int, const int, const int)
) {
	std::queue<TTEFUpdate> update1;
	std::queue<TTEFUpdate> update2;
	// TODO LB bound on the limit
	// LB bounds on the start times
	if (!ttef_bounds_propagation_lb(shift_in1, update1)) {
		// Inconsistency
		return false;
	}
	// TODO UB bounds on the start times
	if (!ttef_bounds_propagation_ub(shift_in2, update2)) {
		// Inconsistency
		return false;
	}
	// TODO Updating the bounds
	//printf("zzz %d\n", (int) update1.size());
	if (!ttef_update_bounds(shift_in1, update1)) {
		return false;
	}
	if (!ttef_update_bounds(shift_in2, update2)) {
		return false;
	}
	return true;
}

bool
CumulativeProp::ttef_bounds_propagation_lb(
	int shift_in(const int, const int, const int, const int, const int, const int, const int),
	std::queue<TTEFUpdate> & update_queue
) {
	assert(last_unfixed > 0);
	int begin, end;		// Begin and end of the time interval [begin, end)
	int est_idx_last = last_unfixed;
	int i, j, en_req, en_avail;
	int en_req_free;
	int update_en_req_start, update_idx;
	//int min_en_avail = -1, lct_idx_last = last_unfixed, i_last = task_id_lct[lct_idx_last];
	int min_en_avail = -1, min_begin = -1;
	bool consistent = true;
	
	end = lct(task_id_lct[last_unfixed]) + 1;

		// Outer Loop: iterating over lct in non-increasing order
		//
	for (int ii = last_unfixed; ii >= 0; ii--) {
		i = task_id_lct[ii];
		if (end == lct(i) || min_energy(i) == 0) continue;
			
			// Check whether the current latest completion time have to be considered
		//int free = max_limit() * (lct(i_last) - lct(i)) - (tt_after_lct[ii] - tt_after_lct[lct_idx_last]);
		//if (min_en_avail >= free) continue;
		//lct_idx_last = ii;
		//i_last = i;
		min_en_avail = max_limit() * (lct(task_id_lct[last_unfixed]) - est(task_id_est[0]));
		min_begin = -1;
		
		end = lct(i);
		while (est(task_id_est[est_idx_last]) >= end) est_idx_last--;
			// Initialisations for the inner loop
		en_req_free = 0;
		update_idx = -1;
		update_en_req_start = -1;

			// Inner Loop: iterating over est in non-increasing order
			//
		for (int jj = est_idx_last; jj >= 0; jj--) {
			j = task_id_est[jj];
			assert(est(j) < end);
            if (min_energy(j) == 0) continue;
			begin = est(j);

				// Checking for TTEEF propagation on upper bound
				//
			int min_en_in = min_usage(j) * max(0, min(end, ect(j)) - max(min_begin, lst(j)));
			if (min_begin >= 0 && min_en_avail + min_en_in < min_usage(j) * (min(end, lct(j)) - max(min_begin, lst(j)))) {
				// Calculate new upper bound
                // XXX Is min_usage correct?
				int dur_avail = (min_en_avail + min_en_in) / min_usage(j);
				int lct_new = min_begin + dur_avail;
				// Check whether a new upper bound was found
				if (lct_new < new_lct[j]) {
					// Push possible update into the queue
					update_queue.push(TTEFUpdate(j, lct_new, min_begin, end, false));
					new_lct[j] = lct_new;
					//int blah = max_limit() * (end - min_begin) - (min_en_avail + min_en_in);
					//printf("%d: lct_new %d; dur_avail %d; en_req %d; [%d, %d)\n", j, lct_new, dur_avail, blah, min_begin, end);
					//printf("XXXXXX\n");
				}
			}
			
			if (lct(j) <= end) {
				// Task lies in the considered time interval	
				en_req_free += free_energy(j);
			} else {
				// Task might partially lie in the considered time interval
				
					// Calculation of the energy part inside the time interavl
				int dur_fixed = max(0, ect(j) - lst(j));
				int dur_shift = shift_in(begin, end, est(j), ect(j), lst(j), lct(j), dur_fixed);
				en_req_free += min_usage(j) * dur_shift;
					// Calculation of the required energy for starting at est(j)
				int en_req_start = min(free_energy(j), min_usage(j) * (end - est(j))) - min_usage(j) * dur_shift;
				if (en_req_start > update_en_req_start) {
					update_en_req_start = en_req_start;
					update_idx = jj;
				}
			}
			en_req = en_req_free + tt_after_est[jj] - tt_after_lct[ii];
			en_avail = max_limit() * (end - begin) - en_req;

			if (min_en_avail > en_avail) {
				min_en_avail = en_avail;
				min_begin = begin;
			}

				// Check for resource overload
				//
			if (en_avail < 0) {
				consistent = false;
				ii = -1;
				break;
			}

				// Check for a start time update
				//
			if (en_avail < update_en_req_start) {
					// Reset 'j' to the task to be updated
				j = task_id_est[update_idx];
					// Calculation of the possible new lower bound wrt. 
					// the current time interval
				int dur_mand  = max(0, min(end, ect(j)) - lst(j));
				int dur_shift = shift_in(begin, end, est(j), ect(j), lst(j), lct(j), dur_mand);
				int en_in     = min_usage(j) * (dur_mand + dur_shift);
				int en_avail_new = en_avail + en_in;
                // XXX Is min_usage correct?
				int dur_avail = en_avail_new / min_usage(j);
				int start_new = end - dur_avail;
					// TODO Check whether a new lower bound was found
					// - nfnl-rule TODO
				if (start_new > new_est[j]) {
					// Push possible update into the queue
					update_queue.push(TTEFUpdate(j, start_new, begin, end, true));
					new_est[j] = start_new;
					//printf("XXXXXX\n");
				}
			}
		}
	}

	if (!consistent) {
		vec<Lit> expl;
        // Increment the inconsistency counter
        nb_ttef_incons++;
		if (so.lazy) {
			list<TaskDur> tasks_tw;
			list<TaskDur> tasks_cp;
			int en_req1 = 0;
			// Retrieve tasks involved
			en_req1 = ttef_retrieve_tasks(shift_in, begin, end, -1, tasks_tw, tasks_cp);
			assert(en_req1 >= en_req);
			// Calculate the lifting
			int en_lift = en_req1 - 1 - max_limit() * (end - begin);
			assert(en_lift >= 0);
			// Explaining the overload
			ttef_analyse_limit_and_tasks(begin, end, tasks_tw, tasks_cp, en_lift, expl);
			assert(expl.size() > 0);
		}
		// Submitting of the conflict explanation
		submit_conflict_explanation(expl);
	}
	return consistent;
}

bool
CumulativeProp::ttef_bounds_propagation_ub(
	int shift_in(const int, const int, const int, const int, const int, const int, const int),
	std::queue<TTEFUpdate> & update_queue
) {
	assert(last_unfixed > 0);
	int begin, end;		// Begin and end of the time interval [begin, end)
	int lct_idx_last = 0;
	int i, j, en_req, en_avail;
	int en_req_free;
	int update_en_req_end, update_idx;
	//int min_en_avail = -1, lct_idx_last = last_unfixed, i_last = task_id_lct[lct_idx_last];
	int min_en_avail = -1, min_end = -1;
	bool consistent = true;
	
	begin = est(task_id_est[0]) - 1;

		// Outer Loop: iterating over est in non-decreasing order
		//
	for (int ii = 0; ii <= last_unfixed; ii++) {
		i = task_id_est[ii];
		if (begin == est(i) || min_energy(i) == 0) continue;
		
			// Intialisation for the minimal avaible energy of a time interval starting
			// at begin
			// TODO dominance rule for skipping time intervals
		min_en_avail = max_limit() * (lct(task_id_lct[last_unfixed]) - est(task_id_est[0]));
		min_end = -1;

		begin = est(i);
		while (lct(task_id_lct[lct_idx_last]) <= begin) lct_idx_last++;
			// Initialisations for the inner loop
		en_req_free = 0;
		update_idx = -1;
		update_en_req_end = -1;

			// Inner Loop: iterating over lct in non-decreasing order
			//
		for (int jj = lct_idx_last; jj <= last_unfixed; jj++) {
			j = task_id_lct[jj];
			assert(lct(j) > begin);
            if (min_energy(j) == 0) continue;
			end = lct(j);

				// Checking for TTEEF propagation on lower bounds
				//
			int min_en_in = min_usage(j) * max(0, min(min_end, ect(j)) - max(begin, lst(j)));
			if (min_end >= 0 && min_en_avail + min_en_in < min_usage(j) * (min(min_end, ect(j)) - max(begin, est(j)))) {
				// Calculate new upper bound
                // XXX Is min_usage correct?
				int dur_avail = (min_en_avail + min_en_in) / min_usage(j);
				int est_new = min_end - dur_avail;
				// Check whether a new lower bound was found
				if (est_new > new_est[j]) {
					// Push possible update into the queue
					update_queue.push(TTEFUpdate(j, est_new, begin, min_end, true));
					new_est[j] = est_new;
					//int blah = max_limit() * (end - min_begin) - (min_en_avail + min_en_in);
					//printf("%d: lct_new %d; dur_avail %d; en_req %d; [%d, %d)\n", j, lct_new, dur_avail, blah, min_begin, end);
					//printf("XXXXXX\n");
				}
			}

			if (begin <= est(j)) {
				// Task lies in the considered time interval [begin, end)
				en_req_free += free_energy(j);
			} else {
				// Task might partially lie in the considered time interval
				
					// Calculation of the energy part inside the time interval
				int dur_fixed = max(0, ect(j) - lst(j));
				int dur_shift = shift_in(begin, end, est(j), ect(j), lst(j), lct(j), dur_fixed);
				en_req_free += min_usage(j) * dur_shift;
					// Calculation of the required energy for finishing at 'lct(j)'
				int en_req_end = min(free_energy(j), min_usage(j) * (lct(j) - begin)) - min_usage(j) * dur_shift;
				if (en_req_end > update_en_req_end) {
					update_en_req_end = en_req_end;
					update_idx = jj;
				}
			}
			en_req = en_req_free + tt_after_est[ii] - tt_after_lct[jj];
			en_avail = max_limit() * (end - begin) - en_req;

			if (min_en_avail > en_avail) {
				min_en_avail = en_avail;
				min_end = end;
			}

				// Check for resource overload
				//
			if (en_avail < 0) {
				consistent = false;
				ii = last_unfixed + 1;
				break;
			}

				// Check for a start time update
				//
			if (en_avail < update_en_req_end) {
					// Reset 'j' to the task to be updated
				j = task_id_lct[update_idx];
					// Calculation of the possible upper bound wrt.
					// the current time interval
				int dur_mand  = max(0, ect(j) - max(begin, lst(j)));
				int dur_shift = shift_in(begin, end, est(j), ect(j), lst(j), lct(j), dur_mand);
				int en_in     = min_usage(j) * (dur_mand + dur_shift);
				int en_avail_new = en_avail + en_in;
                // XXX Is min_usage correct?
				int dur_avail = en_avail_new / min_usage(j);
				int end_new   = begin + dur_avail;
					// TODO Check whether a new uppder bound was found
					// - nfnl-rule TODO
				if (end_new < new_lct[j]) {
					// Push possible update into queue
					update_queue.push(TTEFUpdate(j, end_new, begin, end, false));
					new_lct[j] = end_new;
				}
			}
		}
	}

	if (!consistent) {
		vec<Lit> expl;
        // Increment the inconsistency counter
        nb_ttef_incons++;
		if (so.lazy) {
			list<TaskDur> tasks_tw;
			list<TaskDur> tasks_cp;
			int en_req1 = 0;
			// Retrieve tasks involved
			en_req1 = ttef_retrieve_tasks(shift_in, begin, end, -1, tasks_tw, tasks_cp);
			assert(en_req1 >= en_req);
			// Calculate the lifting
			int en_lift = en_req1 - 1 - max_limit() * (end - begin);
			assert(en_lift >= 0);
			// Explaining the overload
			ttef_analyse_limit_and_tasks(begin, end, tasks_tw, tasks_cp, en_lift, expl);
			assert(expl.size() > 0);
		}
		// Submitting of the conflict explanation
		submit_conflict_explanation(expl);
	}
	return consistent;
}

bool
CumulativeProp::ttef_update_bounds(
	int shift_in(const int, const int, const int, const int, const int, const int, const int), 
	std::queue<TTEFUpdate> & queue_update
) {
	while (!queue_update.empty()) {
		int task  = queue_update.front().task;
		int bound = queue_update.front().bound_new;
		int begin = queue_update.front().tw_begin;
		int end   = queue_update.front().tw_end;
		Clause * reason = NULL;
		if (queue_update.front().is_lb_update) {
			// Lower bound update
			if (new_est[task] == bound) {
				if (so.lazy) {
					vec<Lit> expl;
					list<TaskDur> tasks_tw;
					list<TaskDur> tasks_cp;
					// Retrieving tasks involved
					int en_req = ttef_retrieve_tasks(shift_in, begin, end, task, tasks_tw, tasks_cp);

						// Lifting for the lower bound of 'task'
						//
					int en_avail = max_limit() * (end - begin) - en_req;
                        // XXX Is min_usage correct?
					int dur_avail = en_avail / min_usage(task);
					assert(end - dur_avail >= bound);
                        // XXX Is min_usage correct?
					assert(en_avail < min_usage(task) * (min(end, ect(task)) - max(begin, est(task))));
					bound = end - dur_avail;
					int expl_lb;

					switch (ttef_expl_deg) {
					case ED_NORMAL:
					case ED_LIFT:
                            // XXX Is min_dur correct?
						expl_lb = max(min_start0(task), begin + dur_avail + 1 - min_dur(task)); 
						break;
					case ED_NAIVE:
					default:
						expl_lb = est(task);
					}
						// Lifting from the remainder
					int en_lift = min_usage(task) - 1 - (en_avail % min_usage(task));
						// Lifting from 'expl_lb'
					en_lift += min_usage(task) * (expl_lb + min_dur(task) - (begin + dur_avail + 1));
					assert(expl_lb + min_dur(task) - (begin + dur_avail + 1) >= 0);
					assert(en_lift >= 0);

						// Explaining the update
						//
					if (expl_lb > min_start0(task)) {
						// start[task] >= expl_lb
						expl.push(getNegGeqLit(start[task], expl_lb));
					}
                    // Get the negated literal for [[dur[task] >= min_dur(task)]]
                    if (min_dur0(task) < min_dur(task)) 
                        expl.push(getNegGeqLit(dur[task], min_dur(task)));
                    // Get the negated literal for [[usage[task] >= min_usage(task)]]
                    if (min_usage0(task) < min_usage(task)) 
                        expl.push(getNegGeqLit(usage[task], min_usage(task)));
					ttef_analyse_limit_and_tasks(begin, end, tasks_tw, tasks_cp, en_lift, expl);
					reason = get_reason_for_update(expl);
				}
                // Increment the filtering counter
                nb_ttef_filt++;
				// Update the lower bound
				if (!start[task]->setMin(bound, reason)) {
					// Conflict occurred
					return false;
				}
				// Set bound_update to true
				bound_update = true;
			}
		} else {
			// Upper bound update
			if (new_lct[task] == bound) {
				if (so.lazy) {
					vec<Lit> expl;
					list<TaskDur> tasks_tw;
					list<TaskDur> tasks_cp;
					// Retrieving tasks involved
					int en_req = ttef_retrieve_tasks(shift_in, begin, end, task, tasks_tw, tasks_cp);

						// Lifting for the upper bound of 'task'
						//
					int en_avail = max_limit() * (end - begin) - en_req;
                        // XXX Is min_usage correct?
					int dur_avail = en_avail / min_usage(task);
					//printf("%d: bound %d; dur_avail %d; en_req %d; [%d, %d)\n", task, bound, dur_avail, en_req, begin, end);
					assert(begin + dur_avail <= bound);
//					assert(en_avail < usage[task] * (min(end, lct(task)) - max(begin, lst(task))));
					bound = begin + dur_avail;
					int expl_ub;

					switch (ttef_expl_deg) {
					case ED_NORMAL:
					case ED_LIFT:
						expl_ub = min(max_start0(task), end - dur_avail - 1);
						break;
					case ED_NAIVE:
					default:
						expl_ub = lst(task);
					}
						// Lifting from the remainder
                        // XXX Is min_usage correct
					int en_lift = min_usage(task) - 1 - (en_avail % min_usage(task));
						// Lifting from 'expl_ub'
					en_lift += min_usage(task) * (end - dur_avail - 1 - expl_ub);
					assert(end - dur_avail - 1 - expl_ub >= 0);
					assert(en_lift >= 0);

						// Explaining the update
						//
					if (expl_ub < max_start0(task)) {
						// start[task] <= expl_ub
						expl.push(getNegLeqLit(start[task], expl_ub));
					}
                    // Get the negated literal for [[dur[task] >= min_dur(task)]]
                    if (min_dur0(task) < min_dur(task)) 
                        expl.push(getNegGeqLit(dur[task], min_dur(task)));
                    // Get the negated literal for [[usage[task] >= min_usage(task)]]
                    if (min_usage0(task) < min_usage(task)) 
                        expl.push(getNegGeqLit(usage[task], min_usage(task)));
					ttef_analyse_limit_and_tasks(begin, end, tasks_tw, tasks_cp, en_lift, expl);
					reason = get_reason_for_update(expl);

				}
                // Increment the filtering counter
                nb_ttef_filt++;
				// Update the lower bound
                // XXX Is min_dur correct?
				if (!start[task]->setMax(bound - min_dur(task), reason)) {
					// Conflict occurred
					return false;
				}
				// Set bound_update to true
				bound_update = true;
			}
		}
		queue_update.pop();
	}

	return true;
}

int
CumulativeProp::ttef_retrieve_tasks(
	int shift_in(const int, const int, const int, const int, const int, const int, const int), 
	int begin, int end, int fb_id, list<TaskDur> & tasks_tw, list<TaskDur> & tasks_cp) 
{
	int en_req = 0;
	//printf("* [%d, %d): #tasks %d; fixed %d\n", begin, end, task_id.size(), (int) last_unfixed);
	// Getting fixed tasks
	for (int ii = 0; ii < task_id.size(); ii++) {
		int i = task_id[ii];
		if (i == fb_id || min_energy(i) == 0) continue;
		//printf("\t%d: est %d;  ect %d; lst %d; lct %d (dur: %d; rr: %d; en: %d)\n", i, est(i), ect(i), lst(i), lct(i),
		//	min_dur(i), min_usage(i), min_energy(i));
		if (begin <= est(i) && lct(i) <= end) {
			// Task lies in the time interval [begin, end)
			en_req += min_energy(i);
			tasks_tw.push_back(TaskDur(i, min_dur(i)));
			//printf("\tFull %d: %d in [%d, %d)\n", i, min_energy(i), begin, end);
			//printf("\t\t%d: est %d;  ect %d; lst %d; lct %d (dur: %d; rr: %d; en: %d)\n", i, est(i), ect(i), lst(i), lct(i),
			//	min_dur(i), min_usage(i), min_energy(i));
		} else if (lst(i) < ect(i) && is_intersecting(begin, end, lst(i), ect(i))) {
			// Compulsory part partially or fully lies in [begin, end)
			int dur_comp  = min(end, ect(i)) - max(begin, lst(i));
			int dur_shift = shift_in(begin, end, est(i), ect(i), lst(i), lct(i), dur_comp);
			int dur_in = dur_comp + dur_shift;
			en_req += min_usage(i) * dur_in;
			tasks_cp.push_back(TaskDur(i, dur_in));
			//printf("\tComp %d: %d in [%d, %d)\n", i, min_usage(i) * dur_in, begin, end);
			//printf("\t\t%d: est %d;  ect %d; lst %d; lct %d (dur: %d; rr: %d; en: %d)\n", i, est(i), ect(i), lst(i), lct(i),
			//	min_dur(i), min_usage(i), min_energy(i));
		} else if (0 < shift_in(begin, end, est(i), ect(i), lst(i), lct(i), 0)) {
			// Task partially lies in [begin, end)
			int dur_in = shift_in(begin, end, est(i), ect(i), lst(i), lct(i), 0);
			en_req += min_usage(i) * dur_in;
			tasks_tw.push_back(TaskDur(i, dur_in));
			//printf("Shift %d: %d in [%d, %d)\n", i, min_usage(i) * dur_in, begin, end);
		}
	}
	return en_req;
}

void
CumulativeProp::ttef_analyse_limit_and_tasks(const int begin, const int end, list<TaskDur> & tasks_tw,
	list<TaskDur> & tasks_cp, int & en_lift, vec<Lit> & expl) 
{
	// Getting	explanation for tasks in the time window
	ttef_analyse_tasks(begin, end, tasks_tw, en_lift, expl);
	// Getting explanation for tasks with compulsory parts
	ttef_analyse_tasks(begin, end, tasks_cp, en_lift, expl);
	// Getting explanation for the resource capacity
	int diff_limit = max_limit0() - max_limit();
	if (diff_limit > 0) {
		// Calculate possible lifting
		int lift_limit = min(en_lift / (end - begin), diff_limit);
		en_lift -= lift_limit * (end - begin);
		assert(en_lift >= 0);
		if (lift_limit < diff_limit) {
			// limit[%d] <= max_limit() + lift_limit
			expl.push(getNegLeqLit(limit, max_limit() + lift_limit));
		}
	}
}

void
CumulativeProp::ttef_analyse_tasks(const int begin, const int end, list<TaskDur> & tasks, int & en_lift, vec<Lit> & expl) {
	while (!tasks.empty()) {
		int i = tasks.front().task;
		int dur_in = tasks.front().dur_in;
		int expl_lb, expl_ub;
		int est0 = min_start0(i);
		int lst0 = max_start0(i);
		// Calculate possible lifting
		switch (ttef_expl_deg) {
		case ED_NORMAL:
                // XXX Is min_dur correct
			expl_lb = begin + dur_in - min_dur(i); expl_ub = end - dur_in;
			break;
		case ED_LIFT: {
			int dur_max_out0 = max(0, max(lst0 + min_dur(i) - end, begin - est0));
			int dur_max_out = min(dur_max_out0, dur_in);
                // XXX Is min_usage correct?
			int dur_lift = min(en_lift / min_usage(i), dur_max_out);
			//printf("\t%d: dur_in %d, dur_lift %d; max_out0 %d; max_out %d; %d\n", i, dur_in, dur_lift, dur_max_out0, dur_max_out, en_lift /dur[i]);
			//printf("\t\t est0 %d, lst0 %d\n", est0, lst0);
			en_lift -= min_usage(i) * dur_lift;
			assert(en_lift >= 0);
			if (dur_lift < dur_in) {
                    // XXX Is min_dur correct?
				expl_lb = begin + dur_in - dur_lift - min_dur(i);
				expl_ub = end - dur_in + dur_lift;
			} else {
				expl_lb = est0;
				expl_ub = lst0;
			}}
			break;
		case ED_NAIVE:
		default:
			expl_lb = est(i); expl_ub = lst(i);
		}
		//printf("%d: dur_in %d/%d; en_in %d; est0 %d; lst0 %d\t", i, dur_in, dur[i], dur_in * min_usage(i), est0, lst0);
		if (est0 < expl_lb) {
			//printf("s[%d] >= %d; ", i, expl_lb);
			expl.push(getNegGeqLit(start[i], expl_lb));
		}
		if (expl_ub < lst0) {
			//printf("s[%d] <= %d; ", i, expl_ub);
			expl.push(getNegLeqLit(start[i], expl_ub));
		}
        // Get the negated literal for [[dur[i] >= min_dur(i)]]
        if (min_dur0(i) < min_dur(i)) 
            expl.push(getNegGeqLit(dur[i], min_dur(i)));
        // Get the negated literal for [[usage[i] >= min_usage(i)]]
        if (min_usage0(i) < min_usage(i)) 
            expl.push(getNegGeqLit(usage[i], min_usage(i)));
		//printf("\n");
		tasks.pop_front();
	}
}

inline bool
CumulativeProp::is_intersecting(const int begin1, const int end1, const int begin2, const int end2) {
	return ((begin1 <= begin2 && begin2 < end1) || (begin2 <= begin1 && begin1 < end2));
}

/*** EOF ***/

