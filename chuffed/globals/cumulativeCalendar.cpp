#include <chuffed/core/propagator.h>

#include <iostream>
#include <list>
#include <queue>
#include <set>

using namespace std;

#define CUMUVERB 0

// Data types for the Chuffed solver
#define CUMU_ARR_INTVAR vec<IntVar*>
#define CUMU_MATRIX_INT vec<vec<int> >
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

#define CUMU_MEMCHECK(ptr)                                \
	do {                                                    \
		if ((ptr) == NULL) CHUFFED_ERROR("Out of memory!\n"); \
	} while (0)

class CumulativeCalProp : public Propagator {
	enum ExplDeg { ED_NAIVE, ED_NORMAL, ED_LIFT };
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
		TTEFUpdate(int _t, int _n, int _b, int _e, int _l)
				: task(_t), bound_new(_n), tw_begin(_b), tw_end(_e), is_lb_update(_l != 0) {}
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
		ProfilePart(CUMU_INT b, CUMU_INT e, CUMU_INT l, CUMU_INT t) : begin(b), end(e), level(l) {
			tasks.insert(t);
		};
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
	string name;  // Name of the cumulative constraint for printing statistics

	// Constant Data
	CUMU_ARR_INTVAR start;      // Start time variables of the tasks
	CUMU_ARR_INTVAR dur;        // Durations of the tasks
	CUMU_ARR_INTVAR usage;      // Resource usage of the tasks
	CUMU_INTVAR limit;          // Resource capacity of the resource
	CUMU_MATRIX_INT calendar2;  // Different calendars of the project
	CUMU_ARR_INT taskCalendar;  // Number of calendar that task depends on
	CUMU_INT rho;               //=1 if resource stays engaged, =0 otherwise
	CUMU_INT resCalendar;       // TTEF_cal: Number of calendar that resource depends on
	int** calendar;
	int** workingPeriods;

	const int minTime;  // Minimal time in the calendar
	const int maxTime;  // Maximal time in the calendar

	// Options
	const CUMU_BOOL idem;  // Whether the cumulative propagator should be idempotent
	const CUMU_BOOL tt_check;
	CUMU_BOOL tt_filt;     // Timetabling bounds filtering of the start times
	CUMU_BOOL ttef_check;  // Timetabling-edge-finding consistency check
	CUMU_BOOL ttef_filt;   // Timetabling-edge-finding filtering of the start times
	const CUMU_BOOL
			tteef_filt;  // Opportunistic timetabling-extended-edge-finding filtering of the start times
	long ttef_prop_factor;

	ExplDeg ttef_expl_deg;

	// Counters
	long nb_tt_incons;    // Number of timetabling inconsistencies
	long nb_tt_filt;      // Number of timetabling propagations
	long nb_ttef_incons;  // Number of timetabling-edge-finding inconsistencies
	long nb_ttef_filt;    // Number of timetabling-edge-finding propagations
	long nb_prop_calls;
	long nb_ttefc_calls;
	long nb_ttefc_steps;
	long nb_ttef_lb_calls;
	long nb_ttef_ub_calls;

	// Parameters
	CUMU_BOOL bound_update;

	// Structures
	CUMU_ARR_INT
	task_id;  // Unfixed tasks on the left-hand side and fixed tasks on the right-hand size
	int* task_id_est;
	int* task_id_lct;
	int* tt_after_est;
	int* tt_after_lct;
	int* new_est;
	int* new_lct;
	int tt_profile_size;
	struct ProfilePart* tt_profile;

	int* est_2;
	int* lst_2;
	int* ect_2;
	int* lct_2;
	int* min_energy2;
	Tint* min_energy2_global;
	int* free_energy2;

	// Inline functions
	struct SortEstAsc {
		CumulativeCalProp* p;
		bool operator()(int i, int j) const { return p->est_2[i] < p->est_2[j]; }
		SortEstAsc(CumulativeCalProp* _p) : p(_p) {}
	} sort_est_asc;

	struct SortLctAsc {
		CumulativeCalProp* p;
		bool operator()(int i, int j) const { return p->lct_2[i] < p->lct_2[j]; }
		SortLctAsc(CumulativeCalProp* _p) : p(_p) {}
	} sort_lct_asc;

	// Constructor
	CumulativeCalProp(CUMU_ARR_INTVAR& _start, CUMU_ARR_INTVAR& _dur, CUMU_ARR_INTVAR& _usage,
										CUMU_INTVAR _limit, CUMU_MATRIX_INT& _cal, CUMU_ARR_INT& _taskCal,
										CUMU_INT _rho, CUMU_INT _resCalendar, list<string> opt)
			: start(_start),
				dur(_dur),
				usage(_usage),
				limit(_limit),
				calendar2(_cal),
				taskCalendar(_taskCal),
				rho(_rho),
				resCalendar(_resCalendar),
				minTime(0),
				maxTime(calendar2[0].size() - 1),
				idem(false),
				tt_check(true),
				tt_filt(true),
				ttef_check(true),
				ttef_filt(true),
				tteef_filt(false),
				ttef_prop_factor(100),
				nb_tt_incons(0),
				nb_tt_filt(0),
				nb_ttef_incons(0),
				nb_ttef_filt(0),
				nb_prop_calls(0),
				nb_ttefc_calls(0),
				nb_ttefc_steps(0),
				nb_ttef_lb_calls(0),
				nb_ttef_ub_calls(0),
				bound_update(false),
				sort_est_asc(this),
				sort_lct_asc(this) {
		// Some checks
		rassert(!tteef_filt || ttef_filt);

		// Overriding option defaults
		for (auto& it : opt) {
			if (it == "tt_filt_on") {
				tt_filt = true;
			} else if (it == "tt_filt_off") {
				tt_filt = false;
			}
			if (it == "ttef_check_on") {
				ttef_check = true;
			} else if (it == "ttef_check_off") {
				ttef_check = false;
			}
			if (it == "ttef_filt_on") {
				ttef_filt = true;
			} else if (it == "ttef_filt_off") {
				ttef_filt = false;
			} else if (it.find("__name__") == 0) {
				name = it.substr(8);
			}
		}

		// Creating a copy of the calendars
		calendar = (int**)malloc(calendar2.size() * sizeof(int*));
		for (int i = 0; i < calendar2.size(); i++) {
			calendar[i] = (int*)malloc(calendar2[0].size() * sizeof(int));
		}

		for (int i = 0; i < calendar2.size(); i++) {
			for (int j = 0; j < calendar2[0].size(); j++) {
				calendar[i][j] = calendar2[i][j];
			}
		}

		// Memory allocation for the working periods
		workingPeriods = (int**)malloc(calendar2.size() * sizeof(int*));
		CUMU_MEMCHECK(workingPeriods);
		for (int i = 0; i < calendar2.size(); i++) {
			workingPeriods[i] = (int*)malloc(calendar2[0].size() * sizeof(int));
			CUMU_MEMCHECK(workingPeriods[i]);
		}

		// Initialisation of the working periods
		for (int i = 0; i < calendar2.size(); i++) {
			workingPeriods[i][calendar2[0].size() - 1] = calendar[i][calendar2[0].size() - 1];
			for (int j = calendar2[0].size() - 2; j >= 0; j--) {
				workingPeriods[i][j] = workingPeriods[i][j + 1] + calendar[i][j];
			}
		}

		// Explanation options
		// ttef_expl_deg = ED_NAIVE;
		// ttef_expl_deg = ED_NORMAL;	// TODO Not adjusted to calendars yet
		ttef_expl_deg = ED_LIFT;

		// Allocation of the memory
		tt_profile = new ProfilePart[calendar2[0].size()];  //[2 * start.size()];
		tt_profile_size = 0;

		// Memory allocation of the core structures
		est_2 = (int*)malloc(start.size() * sizeof(int));
		lst_2 = (int*)malloc(start.size() * sizeof(int));
		ect_2 = (int*)malloc(start.size() * sizeof(int));
		lct_2 = (int*)malloc(start.size() * sizeof(int));

		// Memory check
		CUMU_MEMCHECK(est_2);
		CUMU_MEMCHECK(lst_2);
		CUMU_MEMCHECK(ect_2);
		CUMU_MEMCHECK(lct_2);

		// Allocating memory required by the TTEF inconsistency check or
		// filtering algorithm
		if (ttef_check || ttef_filt) {
			// Memory allocation
			task_id_est = (int*)malloc(start.size() * sizeof(int));
			task_id_lct = (int*)malloc(start.size() * sizeof(int));
			tt_after_est = (int*)malloc(start.size() * sizeof(int));
			tt_after_lct = (int*)malloc(start.size() * sizeof(int));
			min_energy2 = (int*)malloc(start.size() * sizeof(int));
			min_energy2_global = (Tint*)malloc(start.size() * sizeof(Tint));
			free_energy2 = (int*)malloc(start.size() * sizeof(int));

			// Memory check
			CUMU_MEMCHECK(task_id_est);
			CUMU_MEMCHECK(task_id_lct);
			CUMU_MEMCHECK(tt_after_est);
			CUMU_MEMCHECK(tt_after_lct);
			CUMU_MEMCHECK(min_energy2);
			CUMU_MEMCHECK(min_energy2_global);
			CUMU_MEMCHECK(free_energy2);

			// Allocating memory only required by the TTEF filtering
			// algorithms
			if (ttef_filt) {
				// Memory allocation
				new_est = (int*)malloc(start.size() * sizeof(int));
				new_lct = (int*)malloc(start.size() * sizeof(int));

				// Memory check
				CUMU_MEMCHECK(new_est);
				CUMU_MEMCHECK(new_lct);
			} else {
				new_est = nullptr;
				new_lct = nullptr;
			}

			// Initialisation of some arrays
			for (int i = 0; i < start.size(); i++) {
				min_energy2_global[i] = min_dur(i);
			}
		} else {
			task_id_est = nullptr;
			task_id_lct = nullptr;
			tt_after_est = nullptr;
			tt_after_lct = nullptr;
			min_energy2 = nullptr;
			min_energy2_global = nullptr;
			free_energy2 = nullptr;
		}

		// Priority of the propagator
		priority = 3;

#if CUMUVERB > 1
		fprintf(stderr, "\tCumulative with n = %d\n", start.size());
#endif
		// Attach to var events
		for (int i = 0; i < start.size(); i++) {
#if CUMUVERB > 1
			fprintf(stderr, "\t%d: %p\n", i, start[i]);
#endif
			start[i]->attach(this, i, EVENT_LU);
			if (min_dur(i) < max_dur(i)) {
				dur[i]->attach(this, i, EVENT_LF);
			}
			if (min_usage(i) < max_usage(i)) {
				usage[i]->attach(this, i, EVENT_LF);
			}
		}
		limit->attach(this, start.size(), EVENT_UF);

		for (int i = 0; i < start.size(); i++) {
			task_id.push(i);
		}
		last_unfixed = start.size() - 1;
	}

	// Statistics
	void printStats() override {
		fprintf(stderr, "%% Cumulative propagator with calendars statistics");
		if (!name.empty()) {
			cerr << " for " << name;
		}
		fprintf(stderr, ":\n");
		fprintf(stderr, "%%\t#TT incons.: %ld\n", nb_tt_incons);
		if (tt_filt) {
			fprintf(stderr, "%%\t#TT prop.: %ld\n", nb_tt_filt);
		}
		if (ttef_check || ttef_filt) {
			fprintf(stderr, "%%\t#TTEF incons.: %ld\n", nb_ttef_incons);
		}
		if (ttef_check && !ttef_filt) {
			fprintf(stderr, "%%\t#TTEF calls: %ld\n", nb_ttefc_calls);
			fprintf(stderr, "%%\t#TTEF cons. steps: %ld\n", nb_ttefc_steps);
		}
		if (ttef_filt) {
			fprintf(stderr, "%%\t#TTEF prop.: %ld\n", nb_ttef_filt);
			fprintf(stderr, "%%\t#TTEF LB calls: %ld\n", nb_ttef_lb_calls);
			fprintf(stderr, "%%\t#TTEF UB calls: %ld\n", nb_ttef_ub_calls);
		}
	}

	/**
	 * Retrieval of parameters
	 **/

	int getEndTimeForStartTime(const int i, const int start, const int duration) {
		const int cal_idx = taskCalendar[i] - 1;
		int end = start + duration;
		if (end <= maxTime) {
			int workDays;
			do {
				workDays = workingPeriods[cal_idx][start] - workingPeriods[cal_idx][end];
				end += duration - workDays;
			} while (workDays < duration && end <= maxTime);
			assert(workDays == duration || end > maxTime);
		}
		if (end > maxTime) {
			end =
					maxTime + duration - (workingPeriods[cal_idx][start] - workingPeriods[cal_idx][maxTime]);
		}
		return end;
	}

	int getStartTimeForEndTime(const int i, const int end, const int duration) {
		const int cal_idx = taskCalendar[i] - 1;
		int start = end - duration;
		if (start >= minTime) {
			int workDays;
			do {
				workDays = workingPeriods[cal_idx][start] - workingPeriods[cal_idx][end];
				start -= duration - workDays;
			} while (workDays < duration && start >= minTime);
			assert(workDays == duration || start < minTime);
		}
		if (start < minTime) {
			start =
					minTime - duration + (workingPeriods[cal_idx][minTime] - workingPeriods[cal_idx][end]);
		}
		return start;
	}

	void retrieveCoreParameters(int i) {
		// Earliest start time
		est_2[i] = CUMU_PT_GETMIN(start[i]);
		// Latest start time
		lst_2[i] = CUMU_PT_GETMAX(start[i]);
		// Earliest completion time
		const int duration = CUMU_PT_GETMIN(dur[i]);
		ect_2[i] = getEndTimeForStartTime(i, est_2[i], duration);
		// Latest completion time
		lct_2[i] = getEndTimeForStartTime(i, lst_2[i], duration);
	}

	int retrieveMinEnergy(const int i) {
		int minEn = 0;
		if (rho == 0) {
			// Resource is released
			return minEn = min_usage(i) * min_dur(i);
		}
		assert(rho == 1);
		// Resource stays engaged
		const int duration = min_dur(i);
		const int cal_idx = taskCalendar[i] - 1;
		const int ls = lst_2[i];
		// Calculate distance when task starts as earliest as possible
		int end = est_2[i] + duration;
		int workDays;
		int distance;
		do {
			workDays = workingPeriods[cal_idx][est_2[i]] - workingPeriods[cal_idx][end];
			end += duration - workDays;
		} while (workDays < duration);
		assert(workDays == duration);
		distance = end - est_2[i];
		// Calculate minimal distance
		for (int time = est_2[i] + 1; time <= ls && distance > min_energy2_global[i]; time++) {
			if (calendar[cal_idx][time - 1] == 1) {
				workDays--;
			}
			while (workDays < duration) {
				if (calendar[cal_idx][end] == 1) {
					workDays++;
				}
				end++;
			}
			assert(workDays == duration);
			distance = min(distance, end - time);
		}
		if (distance > min_energy2_global[i]) {
			min_energy2_global[i] = distance;
		}
		return min_usage(i) * distance;
	}

	int retrieveFreeEnergy(const int i) {
		if (rho == 1) {
			// Resource stays engaged
			return (min_energy2[i] - min_usage(i) * max(0, ect_2[i] - lst_2[i]));
		}  // Resource is released
		int workDays = workingPeriods[taskCalendar[i] - 1][lst_2[i]] -
									 workingPeriods[taskCalendar[i] - 1][ect_2[i]];
		return (min_energy2[i] - min_usage(i) * max(0, workDays));
	}

	void retrieveEnergyParameters(const int i) {
		// NOTE it is assumpted that the arrays est_2, lst_2, ect_2, and lct_2 are up to date!
		// Minimal required energy for executing the task
		min_energy2[i] = retrieveMinEnergy(i);
		// Free energy
		free_energy2[i] = retrieveFreeEnergy(i);
	}

	/**
	 * Inline function for parameters of tasks
	 **/
	// Earliest start time of task i
	inline CUMU_INT est(CUMU_INT i) { return CUMU_PT_GETMIN(start[i]); }
	// Latest start time of task i
	inline CUMU_INT lst(CUMU_INT i) { return CUMU_PT_GETMAX(start[i]); }
	// Earliest completion time of task i
	inline CUMU_INT ect(CUMU_INT i) {
		int t = CUMU_PT_GETMIN(start[i]);
		int j = 0;
		while (j < CUMU_PT_GETMIN(dur[i])) {
			if (calendar[taskCalendar[i] - 1][t] == 1) {
				j++;
			}
			t++;
		}
		return t;
	}
	// Latest completion time of task i
	inline CUMU_INT lct(CUMU_INT i) {
		int t = CUMU_PT_GETMAX(start[i]);
		int j = 0;
		while (j < CUMU_PT_GETMIN(dur[i])) {
			if (calendar[taskCalendar[i] - 1][t] == 1) {
				j++;
			}
			t++;
		}
		return t;
	}
	// Minimal resource usage of task i
	inline CUMU_INT min_usage(CUMU_INT i) { return CUMU_PT_GETMIN(usage[i]); }
	// Minimal energy of task i
	// TTEF_cal: We could consider min_execution_time here, but computation is expensive
	inline CUMU_INT min_energy(CUMU_INT i) {
		if (rho == 0) {  // TTEF_cal: resource is used exactly for p_i time units
			return min_usage(i) * min_dur(i);
		}  // TTEF_cal: resource stays engaged during breaks / could be used more than p_i time
			 // units
		int duration = min_dur(i);
		int t = est(i);
		int ls = lst(i);
		int distance = lct(i) - t;
		int j;
		int tau;
		int next;
		while (t <= ls) {
			tau = t;
			j = 0;
			next = ls + 1;
			while (j < duration) {
				if (calendar[taskCalendar[i] - 1][t] == 1) {
					j++;
				} else if (calendar[taskCalendar[i] - 1][t + 1] == 1) {
					next = min(next, t + 1);
				}
				t++;
			}
			distance = min(distance, t - tau);
			if (distance == duration) {
				return min_usage(i) * duration;
			}
			t = next;
		}
		return min_usage(i) * distance;
	}
	// Free Energy
	inline CUMU_INT free_energy(CUMU_INT i) {
		if (rho == 1) {
			return (min_energy(i) - min_usage(i) * max(0, ect(i) - lst(i)));
		}
		int breaks =
				ect(i) - lst(i) -
				(workingPeriods[taskCalendar[i] - 1][lst(i)] - workingPeriods[taskCalendar[i] - 1][ect(i)]);
		return (min_energy(i) - min_usage(i) * max(0, ect(i) - lst(i) - breaks));
	}

	/**
	 * Inline functions for receiving the minimum and maximum of integer
	 * variables
	 **/
	inline CUMU_INT min_start0(CUMU_INT i) { return CUMU_PT_GETMIN0(start[i]); }
	inline CUMU_INT max_start0(CUMU_INT i) { return CUMU_PT_GETMAX0(start[i]); }
	inline CUMU_INT min_dur(CUMU_INT i) { return CUMU_PT_GETMIN(dur[i]); }
	inline CUMU_INT max_dur(CUMU_INT i) { return CUMU_PT_GETMAX(dur[i]); }
	inline CUMU_INT min_dur0(CUMU_INT i) { return CUMU_PT_GETMIN0(dur[i]); }
	inline CUMU_INT max_usage(CUMU_INT i) { return CUMU_PT_GETMAX(usage[i]); }
	inline CUMU_INT min_usage0(CUMU_INT i) { return CUMU_PT_GETMIN0(usage[i]); }

	inline CUMU_INT min_limit() const { return CUMU_PT_GETMIN(limit); }
	inline CUMU_INT max_limit() const { return CUMU_PT_GETMAX(limit); }
	inline CUMU_INT max_limit0() const { return CUMU_PT_GETMAX0(limit); }

	// TTEF Propagator
	// TTEF_cal: errors occurred when using shift_in function etc.; realized it with an integer
	// shift_in
	//           if shift_in == 1 right shift is used; if shift_in == 2 left shift is used
	void ttef_initialise_parameters();
	bool ttef_consistency_check(int shift_in);
	bool ttef_bounds_propagation(int shift_in1, int shift_in2);
	bool ttef_bounds_propagation_lb(int shift_in, std::queue<TTEFUpdate>& update_queue);
	bool ttef_bounds_propagation_ub(int shift_in, std::queue<TTEFUpdate>& update_queue);
	void tteef_bounds_propagation_lb(int begin, int end, int en_avail, int j,
																	 std::queue<TTEFUpdate>& update_queue);
	void tteef_bounds_propagation_ub(int begin, int end, int en_avail, int j,
																	 std::queue<TTEFUpdate>& update_queue);
	int ttef_get_new_start_time(int begin, int end, int task, int min_wdays_in);
	int ttef_get_new_end_time(int begin, int end, int task, int min_wdays_in);
	bool ttef_update_bounds(int shift_in, std::queue<TTEFUpdate>& queue_update);
	void ttef_explanation_for_update_lb(int shift_in, int begin, int end, int task, int& bound,
																			vec<Lit>& expl);
	void ttef_explanation_for_update_ub(int shift_in, int begin, int end, int task, int& bound,
																			vec<Lit>& expl);

	int ttef_retrieve_tasks(int shift_in, int begin, int end, int fb_id, list<TaskDur>& tasks_tw,
													list<TaskDur>& tasks_cp);

	// TTEF Generation of explanations
	// TTEF_cal: consider breaks between begin and end
	void ttef_analyse_limit_and_tasks(int begin, int end, int breaks, list<TaskDur>& tasks_tw,
																		list<TaskDur>& tasks_cp, int& en_lift, vec<Lit>& expl);
	void ttef_analyse_tasks(int begin, int end, list<TaskDur>& tasks, int& en_lift, vec<Lit>& expl);
	int ttef_analyse_tasks_left_shift(int begin, int end, int dur_in, int task, int max_dur_lift,
																		int& last_dur);
	int ttef_analyse_tasks_right_shift(int begin, int end, int dur_in, int task, int max_dur_lift,
																		 int& last_dur);
	bool ttef_analyse_tasks_check_expl_lb(int begin, int end, int task, int dur_in, int expl_lb);
	bool ttef_analyse_tasks_check_expl_ub(int begin, int end, int task, int dur_in, int expl_ub);

	static inline bool is_intersecting(int begin1, int end1, int begin2, int end2);

	inline int get_free_dur_right_shift2(const int tw_begin, const int tw_end, const int task) {
		if (tw_begin > est_2[task] || tw_end <= lst_2[task] || tw_end <= ect_2[task]) {
			return 0;
		}
		const int free_lst = (lst_2[task] < ect_2[task] ? ect_2[task] : lst_2[task]);
		if (rho == 0) {
			// Resource is released
			const int cal_idx = taskCalendar[task] - 1;
			const int workingDays = workingPeriods[cal_idx][free_lst] - workingPeriods[cal_idx][tw_end];
			return workingDays;
		}  // Resource stays engaged
		return (tw_end - free_lst);
	}

	inline int get_free_dur_left_shift2(const int tw_begin, const int tw_end, const int task) {
		if (tw_end < lct_2[task] || tw_begin >= ect_2[task] || tw_begin >= lst_2[task]) {
			return 0;
		}
		const int free_ect = (lst_2[task] < ect_2[task] ? lst_2[task] : ect_2[task]);
		if (rho == 0) {
			// Resource is released
			const int* wPeriods = workingPeriods[taskCalendar[task] - 1];
			const int workingDays = wPeriods[tw_begin] - wPeriods[free_ect];
			return workingDays;
		}  // Resource stays engaged
		return (free_ect - tw_begin);
	}

	static inline int get_no_shift(const int tw_begin, const int tw_end, const int est, const int ect,
																 const int lst, const int lct, const int dur_fixed_in,
																 const int task) {
		return 0;
	}

	// Cumulative Propagator
	CUMU_BOOL
	propagate() override {
#if CUMUVERB > 1
		fprintf(stderr, "Entering cumulative propagation\n");
#endif
		assert(last_unfixed >= 0);
		// Retrieval of the task's core data and updating
		// the fixed-task array
		int new_unfixed = last_unfixed;
		int tw_begin = maxTime;
		int tw_end = minTime;
		for (int ii = new_unfixed; ii >= 0; ii--) {
			const int i = task_id[ii];
			// Retrieve core data (est, lst, ect, lct)
			if (min_dur(i) > 0 && min_usage(i) > 0) {
				retrieveCoreParameters(i);
			}
			// Compute the time window for consideration
			tw_begin = min(tw_begin, est_2[i]);
			tw_end = max(tw_end, lct_2[i]);
			// Check whether the task 'i' is fixed
			if ((CUMU_PT_ISFIXED(start[i]) && CUMU_PT_ISFIXED(dur[i]) && CUMU_PT_ISFIXED(usage[i])) ||
					max_dur(i) <= 0 || max_usage(i) <= 0) {
				// Swaping the id's
				task_id[ii] = task_id[new_unfixed];
				task_id[new_unfixed] = i;
				new_unfixed--;
				if (min_energy2 != nullptr && min_dur(i) > 0 && min_usage(i) > 0) {
					free_energy2[i] = 0;
					if (rho == 1) {
						// Resource stays engaged
						min_energy2[i] = min_usage(i) * (lct_2[i] - est_2[i]);
					} else {
						// Resource is released
						min_energy2[i] = min_usage(i) * min_dur(i);
					}
				}
			}
		}
		tw_begin = minTime;
		tw_end = maxTime;
		// Trailing the index of the last unfixed task
		last_unfixed = new_unfixed;
#if CUMUVERB > 1
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
				if (!time_table_propagation(task_id, tw_begin, tw_end)) {
					// Inconsistency was detected
#if CUMUVERB > 1
					fprintf(stderr, "Leaving cumulative propagation with failure\n");
#endif
					return false;
				}
			}
			// if (!bound_update)
			//	nb_prop_calls++;
			//  Time-table-edge-finding propagation
			if (!bound_update && last_unfixed > 0 &&
					(ttef_check || ttef_filt)) {  // && nb_prop_calls % 100 == 0) {
				nb_prop_calls++;
				if (ttef_prop_factor != 0 && nb_prop_calls % ttef_prop_factor != 0) {
					continue;
				}
#if CUMUVERB > 0
				fprintf(stderr, "Entering TTEF\n");
#endif
				// Retrieval of the data required for the TTEF propagation
				for (int ii = 0; ii <= last_unfixed; ii++) {
					const int i = task_id[ii];
					retrieveEnergyParameters(i);
				}
				// Initialisation of necessary structures
				// - Unfixed tasks sorted according earliest start time
				// - Unfixed tasks sorted according latest completion time
				// - Energy of the compulsory parts after the latest completion
				// 	 time of unfixed tasks
				// - Energy of the compulsory parts after the earliest start
				//   time of unfixed tasks
				ttef_initialise_parameters();

				// TTEF filtering algorithm
				if (ttef_filt) {
					if (!ttef_bounds_propagation(1, 2)) {
						// Inconsistency was detected
						return false;
					}
				} else {
#if CUMUVERB > 0
					fprintf(stderr, "Entering TTEF Consistency\n");
#endif
					if (!ttef_consistency_check(1)) {
						// Inconsistency was detected
						return false;
					}
#if CUMUVERB > 0
					fprintf(stderr, "Leaving TTEF Consistency\n");
#endif
				}
#if CUMUVERB > 0
				fprintf(stderr, "Leaving TTEF\n");
#endif
			}
		} while (idem && bound_update);
#if CUMUVERB > 0
		fprintf(stderr, "\tLeaving cumulative propagation loop\n");
		fprintf(stderr, "Leaving cumulative propagation without failure\n");
#endif
		return true;
	}

	// Comparison between two compulsory parts
	static bool compare_CompParts(CompPart cp1, CompPart cp2) {
		if (cp1.begin < cp2.begin) {
			return true;
		}
		if (cp1.begin > cp2.begin) {
			return false;
		}
		// ASSUMPTION
		// - cp1.begin == cp2.begin
		if (cp1.end < cp2.end) {
			return true;
		}
		if (cp1.end > cp2.end) {
			return false;
		}
		// ASSUMPTION
		// - cp1.end == cp2.end
		if (cp1.task < cp2.task) {
			return true;
		}
		return false;
	}

	// Creation of the resource profile for the time-table consistency check
	// and propagator
	CUMU_BOOL
	time_table_propagation(CUMU_ARR_INT& task, const int tw_begin, const int tw_end) {
		list<ProfileChangePt> changes;
		list<CUMU_INT> comp_task;
		// int size_profile = 0;
#if CUMUVERB > 10
		fprintf(stderr, "\tCompulsory Parts ...\n");
#endif
		get_compulsory_parts2(changes, comp_task, task, 0, task.size(), tw_begin, tw_end);
		// Proceed if there are compulsory parts
		if (!changes.empty()) {
#if CUMUVERB > 1
			fprintf(stderr, "\tSorting (size %d)...\n", (int)changes.size());
#endif
			// Sorting the start and end points of all the profile
			changes.sort(compare_ProfileChangePt);
#if CUMUVERB > 1
			fprintf(stderr, "\tSorting (size %d)...\n", (int)changes.size());
#endif
			// Counting the number of different profiles
			tt_profile_size = count_profile(changes);
#if CUMUVERB > 1
			fprintf(stderr, "\t#profile parts = %d\n", tt_profile_size);
#endif
#if CUMUVERB > 1
			fprintf(stderr, "\tProfile Parts ...\n");
#endif
			// Creating the different profile parts
			create_profile(changes);
			int i_max_usage = 0;
#if CUMUVERB > 1
			fprintf(stderr, "\tFilling of Profile Parts ...\n");
#endif
			// Filling the profile parts with tasks
			if (!fill_in_profile_parts(tt_profile, tt_profile_size, comp_task, i_max_usage)) {
				return false;
			}
#if CUMUVERB > 10
			fprintf(stderr, "\tFiltering Resource Limit ...\n");
#endif
			// Filtering of resource limit variable
			if (!filter_limit(tt_profile, i_max_usage)) {
				return false;
			}
			if (tt_filt) {
#if CUMUVERB > 10
				fprintf(stderr, "\tFiltering Start Times ...\n");
#endif
				// Time-table filtering
				if (!time_table_filtering(tt_profile, tt_profile_size, task, 0, last_unfixed,
																	tt_profile[i_max_usage].level)) {
					return false;
				}
			}
		}
#if CUMUVERB > 10
		fprintf(stderr, "\tEnd of time-table propagation ...\n");
#endif
		return true;
	}

	void get_compulsory_parts2(list<ProfileChangePt>& changes, list<CUMU_INT>& comp_task,
														 CUMU_ARR_INT& task, CUMU_INT i_start, CUMU_INT i_end, int tw_begin,
														 int tw_end);

	// Sets for each profile part its begin and end time in chronological order
	// Runtime complexity: O(n)
	//
	void create_profile(list<ProfileChangePt>& changes) const {
		auto iter = changes.begin();
		int cur_profile = 0;
		int cur_time = iter->time;
		ProfileChange cur_change = iter->change;
		int no_starts = 1;
		for (; iter != changes.end(); iter++) {
			if (iter->time > cur_time && no_starts > 1) {
#if CUMUVERB > 20
				fprintf(stderr, "Set times for profile part %d = [%d, %d)\n", cur_profile, cur_time,
								iter->time);
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

	inline void set_times_for_profile(int i, CUMU_INT begin, CUMU_INT end) const {
		tt_profile[i].begin = begin;
		tt_profile[i].end = end;
		tt_profile[i].level = 0;
		tt_profile[i].tasks.clear();
	}

	// Filling the profile parts with compulsory parts and checking for a resource
	// overload
	CUMU_BOOL
	fill_in_profile_parts(ProfilePart* profile, int size, list<CUMU_INT> comp_task,
												int& i_max_usage) {
		list<CUMU_INT>::iterator iter;
		int i = 0;
		CUMU_INT lst_i;
		CUMU_INT ect_i;

#if CUMUVERB > 2
		fprintf(stderr, "\t\tstart filling profiles (size %d)\n", size);
#endif
		for (iter = comp_task.begin(); iter != comp_task.end(); iter++) {
#if CUMUVERB > 2
			fprintf(stderr, "\t\tcomp part = %d\n", *iter);
#endif
			lst_i = lst_2[*iter];
			ect_i = ect_2[*iter];
#if CUMUVERB > 2
			fprintf(stderr, "\t\tFinding first profile part ; est: %d ; lst: %d ; ect: %d ; dur: %d\n",
							est_2[*iter], lst_i, ect_i, min_dur(*iter));
#endif
			// Find first profile
			i = find_first_profile(profile, 0, size - 1, lst_i);
#if CUMUVERB > 2
			fprintf(stderr, "\t\tAdding comp parts of level %d\n", min_usage(*iter));
#endif
			// Add compulsory part to the profile
			while (i < size && profile[i].begin < ect_i) {
				if (calendar[taskCalendar[*iter] - 1][profile[i].begin] == 1 || rho == 1) {
#if CUMUVERB > 2
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
						fprintf(stderr, "\t\t\tResource overload (%d > %d) in profile part %d\n",
										profile[i].level, max_limit(), i);
#endif
						// Increment the inconsistency counter
						nb_tt_incons++;

						// The resource is overloaded in this part
						vec<Lit> expl;
						if (so.lazy) {
							CUMU_INT lift_usage = profile[i].level - max_limit() - 1;
							CUMU_INT begin1;
							CUMU_INT end1;
							// TODO Different choices to pick the interval
							// Pointwise explanation
							begin1 = profile[i].begin + ((profile[i].end - profile[i].begin) / 2);
							end1 = begin1 + 1;
							// Generation of the explanation
							analyse_limit_and_tasks(expl, profile[i].tasks, lift_usage, begin1, end1);
						}
						// Submitting of the conflict explanation
						submit_conflict_explanation(expl);
#if CUMUVERB > 20
						fprintf(stderr, "\texpl size: %d\n", expl.size());
						fprintf(stderr, "\t\tend filling (conflict)\n");
#endif
						return false;
					}
				}
				i++;
			}
		}
#if CUMUVERB > 2
		fprintf(stderr, "\t\tend filling (successful)\n");
#endif
		return true;
	}

	// Finds the profile part that begins at the time unit "lst"
	// Complexity: O(log(high - low + 1))
	//
	static int find_first_profile(ProfilePart* profile, int low, int high, CUMU_INT lst) {
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
	static int count_profile(list<ProfileChangePt>& changes) {
		auto iter = changes.begin();
		int cur_time = iter->time;
		int next_time;
		ProfileChange cur_change = iter->change;
		int no_starts = (iter->change == PROFINC ? 1 : 0);
		int no_profile = no_starts;
		iter++;

#if CUMUVERB > 2
		fprintf(stderr, "\t\t\ttime = %d; change = %d; no_starts = %d; no_profile = %d;\n", cur_time,
						cur_change, no_starts, no_profile);
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
#if CUMUVERB > 2
			fprintf(stderr, "\t\t\ttime = %d; change = %d; no_starts = %d; no_profile = %d;\n", cur_time,
							cur_change, no_starts, no_profile);
#endif
		}
		return no_profile;
	}

	static bool compare_ProfileChangePt(ProfileChangePt& pt1, ProfileChangePt& pt2) {
		if (pt1.time == pt2.time && pt1.change == PROFDEC && pt2.change == PROFINC) {
			return true;
		}
		return pt1.time < pt2.time;
	}

	// Time-table filtering on the lower bound of the resource limit variable
	// Complexity:
	CUMU_BOOL
	filter_limit(ProfilePart* profile, int& i_max_usage);

	// Time-table filtering on the start time variables
	// Complexity:
	CUMU_BOOL
	time_table_filtering(ProfilePart profile[], int size, CUMU_ARR_INT& task, int start, int end,
											 CUMU_INT max_usage);
	CUMU_BOOL
	time_table_filtering_lb(ProfilePart profile[], int low, int high, int task);
	CUMU_BOOL
	time_table_filtering_ub(ProfilePart profile[], int low, int high, int task);

	static int find_first_profile_for_lb(ProfilePart profile[], int low, int high, CUMU_INT t);
	static int find_first_profile_for_ub(ProfilePart profile[], int low, int high, CUMU_INT t);

	// Analysing the conflict and generation of the explanations
	// NOTE: Fixed durations and resource usages are assumed!!!
	//
	// Explanation is created for the time interval [begin, end), i.e., exluding end.
	//
	void analyse_limit_and_tasks(vec<Lit>& expl, set<CUMU_INT>& tasks, CUMU_INT lift_usage,
															 CUMU_INT begin, CUMU_INT end);
	void analyse_tasks(vec<Lit>& expl, set<CUMU_INT>& tasks, CUMU_INT lift_usage, CUMU_INT begin,
										 CUMU_INT end);
	static void submit_conflict_explanation(vec<Lit>& expl);
	static Clause* get_reason_for_update(vec<Lit>& expl);

	// TODO Disentailment check
	// CUMU_INT
	// checkSatisfied() {
	//	// XXX Until no cumulative propagator is implemented the constraint
	//	// is always ?satisfied?
	//	return 1;
	//}

	// Wrapper to get the negated literal -[[v <= val]] = [[v >= val + 1]]
	static inline Lit getNegLeqLit(CUMU_INTVAR v, CUMU_INT val) {
		// return v->getLit(val + 1, LR_GE);
		return (INT_VAR_LL == v->getType() ? v->getMaxLit() : v->getLit(val + 1, LR_GE));
	}
	// Wrapper to get the negated literal -[[v >= val]] = [[ v <= val - 1]]
	static inline Lit getNegGeqLit(CUMU_INTVAR v, CUMU_INT val) {
		// return v->getLit(val - 1, LR_LE);
		return (INT_VAR_LL == v->getType() ? v->getMinLit() : v->getLit(val - 1, LR_LE));
	}
};

/****
 * Functions related to the Time-Table Consistency Check and Propagation
 ****/

void CumulativeCalProp::get_compulsory_parts2(list<ProfileChangePt>& changes,
																							list<CUMU_INT>& comp_task, CUMU_ARR_INT& task,
																							CUMU_INT i_start, CUMU_INT i_end, const int tw_begin,
																							const int tw_end) {
#if CUMUVERB > 2
	fprintf(stderr, "\tstart get_compulsory_part from %d to %d\n", i_start, i_end);
#endif
	for (int ii = i_start; ii < i_end; ii++) {
		const int i = task[ii];
#if CUMUVERB > 2
		fprintf(stderr, "\t\tii = %d; task[ii] = %d; est %d; dur %d\n", ii, i, est_2[i], min_dur(i));
#endif
		// Check whether the task creates a compulsory part and if it falls into
		// the considered time window
		if (min_dur(i) > 0 && min_usage(i) > 0 && lst_2[i] < ect_2[i] && tw_begin < lct_2[i] &&
				est_2[i] < tw_end) {
#if CUMUVERB > 2
			fprintf(stderr, "\t\ttask[ii] = %d, comp part [%d, %d)\n", i, lst_2[i], ect_2[i]);
#endif
			// Add task to the list
			comp_task.push_back(i);
			// Add time points to change lists
			int t;
			changes.emplace_back(lst_2[i], PROFINC);
			changes.emplace_back(ect_2[i], PROFDEC);
			if (rho == 0) {
				// Resource is released
				// Calculating the breaks of the task 'i'
				for (t = lst_2[i] + 1; t < ect_2[i]; t++) {
					const int tCal = taskCalendar[i] - 1;
					if (calendar[tCal][t] == 1 && calendar[tCal][t - 1] == 0) {
						changes.emplace_back(t, PROFINC);
					}
					if (calendar[tCal][t] == 0 && calendar[tCal][t - 1] == 1) {
						changes.emplace_back(t, PROFDEC);
					}
				}
			}
		}
	}
#if CUMUVERB > 2
	fprintf(stderr, "\tend get_compulsory_part\n");
#endif
}

/***************************************************************************************
 * Function for time-table filtering on the lower bound of the resource limit variable *
 ***************************************************************************************/

CUMU_BOOL
CumulativeCalProp::filter_limit(ProfilePart* profile, int& i) {
	if (min_limit() < profile[i].level) {
		Clause* reason = nullptr;
		nb_tt_filt++;
		if (so.lazy) {
			// Lower bound can be updated
			// XXX Determining what time period is the best
			int expl_begin = profile[i].begin + ((profile[i].end - profile[i].begin - 1) / 2);
			int expl_end = expl_begin + 1;
			vec<Lit> expl;
			// Get the negated literals for the tasks in the profile
			analyse_tasks(expl, profile[i].tasks, 0, expl_begin, expl_end);
			// Transform literals to a clause
			reason = get_reason_for_update(expl);
		}
		if (!limit->setMin(profile[i].level, reason)) {
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
CumulativeCalProp::time_table_filtering(ProfilePart profile[], int size, CUMU_ARR_INT& task,
																				int i_start, int i_end, CUMU_INT max_usage) {
	for (int ii = i_start; ii <= i_end; ii++) {
		const int i = task[ii];
		// Skipping tasks with zero duration or usage
		if (min_dur(i) <= 0 || min_usage(i) <= 0) {
			continue;
		}
#if CUMUVERB > 2
		fprintf(stderr, "TT Filtering of task %d\n", i);
#endif
		// Check if the sum of max_usage and the task's usage are greater then the upper bound
		// on the resource limit
		if (min_usage(i) + max_usage > max_limit()) {
			int index;
#if CUMUVERB > 2
			fprintf(stderr, "Finding the first index for LB ...\n");
#endif
			// Find initial profile part for lower bound propagation
			//
			index = find_first_profile_for_lb(profile, 0, size - 1, est_2[i]);
#if CUMUVERB > 2
			fprintf(stderr, "Lower bound starting from index %d\n", index);
#endif
			// Update the lower bound if possible
			if (!time_table_filtering_lb(profile, index, size - 1, i)) {
				return false;
			}
#if CUMUVERB > 2
			fprintf(stderr, "Finding the first index for UB ...\n");
#endif
			// Find initial profile part for upper bound propagation
			index = find_first_profile_for_ub(profile, 0, size - 1, lct_2[task[i]]);
#if CUMUVERB > 2
			fprintf(stderr, "Upper bound starting from index %d\n", index);
#endif
			// Update the upper bound if possible
			if (!time_table_filtering_ub(profile, 0, index, i)) {
				return false;
			}
		}
	}
	return true;
}

// Time-Table Filtering on the Lower Bound of Start Times Variables
//
CUMU_BOOL
CumulativeCalProp::time_table_filtering_lb(ProfilePart profile[], int low, int high, int task) {
	int i;
	for (i = low; i <= high; i++) {
		if (ect_2[task] <= profile[i].begin) {
			// No lower bound update possible
			break;
		}
		// ASSUMPTION
		// - ect_2[task] > profile[i].begin
		if (est_2[task] < profile[i].end && profile[i].level + min_usage(task) > max_limit()) {
			// Possibly a lower bound update if "task" as no compulsory part in the profile
			if (lst_2[task] < ect_2[task] && lst_2[task] <= profile[i].begin &&
					profile[i].end <= ect_2[task]) {
				// No lower bound update possible for this profile part, because
				// "task" has a compulsory part in it
				continue;
			}
			const int cal_idx = taskCalendar[task] - 1;
			const int* wPeriods = workingPeriods[cal_idx];
			const int end = min(ect_2[task], profile[i].end);
			if (rho == 0 && wPeriods[profile[i].begin] == wPeriods[end]) {
				continue;
			}
#if CUMUVERB > 1
			fprintf(stderr, "\n----\n");
			fprintf(stderr, "setMin of task %d in profile part [%d, %d)\n", task, profile[i].begin,
							profile[i].end);
			fprintf(stderr, "task %d: lst = %d; ect = %d; dur = %d;\n", task, lst_2[task], ect_2[task],
							min_dur(task));
#endif
			int expl_end = profile[i].end;
			Clause* reason = nullptr;
			if (so.lazy) {
				// XXX Assumption for the remaining if-statement
				//   No compulsory part of task in profile[i]!
				int lift_usage = profile[i].level + min_usage(task) - max_limit() - 1;
				// TODO Choices of different explanation
				// Pointwise explanation
				expl_end = end;
				int expl_begin = expl_end - 1;

				vec<Lit> expl;
				const int wdays = min_dur(task) - (calendar[cal_idx][expl_end - 1] == 1 ? 0 : 1);
				int k = getStartTimeForEndTime(task, end, wdays);
				// Get the negated literal for [[start[task] >= ex_end - min_dur(task)]]

#if CUMUVERB > 1
				fprintf(stderr, "start[%d] => %d ", task, k);
#endif
				// expl.push(getNegGeqLit(start[task], expl_end - min_dur(task)));
				expl.push(getNegGeqLit(start[task], k));
				// Get the negated literal for [[dur[task] >= min_dur(task)]]
				if (min_dur0(task) < min_dur(task)) {
					expl.push(getNegGeqLit(dur[task], min_dur(task)));
				}
				// Get the negated literal for [[usage[task] >= min_usage(task)]]
				if (min_usage0(task) < min_usage(task)) {
					expl.push(getNegGeqLit(usage[task], min_usage(task)));
				}
				// Get the negated literals for the tasks in the profile and the resource limit
				analyse_limit_and_tasks(expl, profile[i].tasks, lift_usage, expl_begin, expl_end);
#if CUMUVERB > 1
				fprintf(stderr, " -> start[%d] => %d\n", task, expl_end);
#endif
				// Transform literals to a clause
				reason = get_reason_for_update(expl);
			}
			nb_tt_filt++;
			// Impose the new lower bound on start[task]
			if (!start[task]->setMin(expl_end, reason)) {
				// Conflict occurred
				return false;
			}
			// Update task's parameters
			retrieveCoreParameters(task);
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
CumulativeCalProp::time_table_filtering_ub(ProfilePart profile[], int low, int high, int task) {
	int i;
	for (i = high; i >= low; i--) {
		if (profile[i].end <= lst_2[task]) {
			// No upper bound update possible
			break;
		}
		// ASSUMPTION for the remaining for-loop
		// - profile[i].end > lst_2[task]
		if (profile[i].begin < lct_2[task] && profile[i].level + min_usage(task) > max_limit()) {
			// Possibly a upper bound update possible if "task" has no compulsory part
			// in this profile part
			if (lst_2[task] < ect_2[task] && lst_2[task] <= profile[i].begin &&
					profile[i].end <= ect_2[task]) {
				// No lower bound update possible for this profile part, because
				// "task" has a compulsory part in it
				continue;
			}
			// Check whether the task has a working period in the profile part
			// if the resource is released
			const int cal_idx = taskCalendar[task] - 1;
			const int begin = max(lst_2[task], profile[i].begin);
			if (rho == 0 && workingPeriods[cal_idx][begin] == workingPeriods[cal_idx][profile[i].end]) {
				continue;
			}

			int expl_begin = profile[i].begin;
			Clause* reason = nullptr;
			if (so.lazy) {
				// ASSUMPTION for the remaining if-statement
				// - No compulsory part of task in profile[i]
				int lift_usage = profile[i].level + min_usage(task) - max_limit() - 1;
				// TODO Choices of different explanations
				// Pointwise explanation
				expl_begin = begin;
				// expl_begin = max(profile[i].begin, lst_2[task]);
				int expl_end = expl_begin + 1;
				vec<Lit> expl;
				// Get the negated literal for [[start[task] <= expl_begin]]
				expl.push(getNegLeqLit(start[task], expl_begin));
				// Get the negated literal for [[dur[task] >= min_dur(task)]]
				if (min_dur0(task) < min_dur(task)) {
					expl.push(getNegGeqLit(dur[task], min_dur(task)));
				}
				// Get the negated literal for [[usage[task] >= min_usage(task)]]
				if (min_usage0(task) < min_usage(task)) {
					expl.push(getNegGeqLit(usage[task], min_usage(task)));
				}
				// Get the negated literals for the tasks in the profile and the resource limit
				analyse_limit_and_tasks(expl, profile[i].tasks, lift_usage, expl_begin, expl_end);
				// Transform literals to a clause
				reason = get_reason_for_update(expl);
			}
			int new_lst = expl_begin;
			int j = 0;
			while (j < min_dur(task)) {
				new_lst--;
				if (calendar[taskCalendar[task] - 1][new_lst] == 1) {
					j++;
				}
			}

			nb_tt_filt++;
			// Impose the new lower bound on start[task]
			// if (! start[task]->setMax(expl_begin - min_dur(task), reason)) {
			if (!start[task]->setMax(new_lst, reason)) {
				// Conflict occurred
				return false;
			}
			// Update task's core parameters
			retrieveCoreParameters(task);
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

int CumulativeCalProp::find_first_profile_for_lb(ProfilePart profile[], int low, int high,
																								 CUMU_INT t) {
	int median;
	if (profile[low].end > t || low == high) {
		return low;
	}
	if (profile[high].begin <= t) {
		return high;
	}
#if CUMUVERB > 2
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
#if CUMUVERB > 2
		fprintf(stderr, "profile[lo = %d] = [%d, %d); ", low, profile[low].begin, profile[low].end);
		fprintf(stderr, "profile[me = %d] = [%d, %d); ", median, profile[median].begin,
						profile[median].end);
		fprintf(stderr, "profile[hi = %d] = [%d, %d);\n", high, profile[high].begin, profile[high].end);
#endif
		if (t < profile[median].end) {
			high = median;
			// high = median - 1;
			low++;
		} else {
			low = median;
		}
	}
	return low;
}

int CumulativeCalProp::find_first_profile_for_ub(ProfilePart profile[], int low, int high,
																								 CUMU_INT t) {
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

void CumulativeCalProp::analyse_limit_and_tasks(vec<Lit>& expl, set<CUMU_INT>& tasks,
																								CUMU_INT lift_usage, CUMU_INT begin, CUMU_INT end) {
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

void CumulativeCalProp::analyse_tasks(vec<Lit>& expl, set<CUMU_INT>& tasks, CUMU_INT lift_usage,
																			CUMU_INT begin, CUMU_INT end) {
	set<CUMU_INT>::iterator iter;
	for (iter = tasks.begin(); iter != tasks.end(); iter++) {
		const int i = *iter;
#if CUMUVERB > 10
		fprintf(stderr, "\ns[%d] in [%d..%d]\n", i, start[i]->getMin(), start[i]->getMax());
#endif
		if (min_usage(i) <= lift_usage) {
			// Task is not relevant for the resource overload
			lift_usage -= min_usage(i);
		} else {
			const int duration = min_dur(i) - (calendar[taskCalendar[i] - 1][end - 1] != 0 ? 0 : 1);
			const int t = getStartTimeForEndTime(i, end, duration);

			// Lower bound of the start time variable matters
			if (t > min_start0(i)) {
				// Get explanation for [[start[i] >= end - min_dur(i)]]

#if CUMUVERB > 10
				fprintf(stderr, "/\\ start[%d] => %d ", i, t);
#endif
				expl.push(getNegGeqLit(start[i], t));
			}
			if (begin < max_start0(i)) {
				// Upper bound of the start time variable matters
				// Get explanation for [[start[i] <= begin]]
#if CUMUVERB > 10
				fprintf(stderr, "/\\ start[%d] <= %d ", i, begin);
#endif
				expl.push(getNegLeqLit(start[i], begin));
			}
			// Get the negated literal for [[dur[i] >= min_dur(i)]]
			if (min_dur0(i) < min_dur(i)) {
				expl.push(getNegGeqLit(dur[i], min_dur(i)));
			}
			// Get the negated literal for [[usage[i] >= min_usage(i)]]
			const int usage_diff = min_usage(i) - min_usage0(i);
			if (usage_diff > 0) {
				if (usage_diff <= lift_usage) {
					lift_usage -= usage_diff;
				} else {
					expl.push(getNegGeqLit(usage[i], min_usage(i)));
				}
			}
		}
	}
}

void CumulativeCalProp::submit_conflict_explanation(vec<Lit>& expl) {
	Clause* reason = nullptr;
	if (so.lazy) {
		reason = Reason_new(expl.size());
		int i = 0;
		for (; i < expl.size(); i++) {
			(*reason)[i] = expl[i];
		}
	}
	sat.confl = reason;
}

Clause* CumulativeCalProp::get_reason_for_update(vec<Lit>& expl) {
	Clause* reason = Reason_new(expl.size() + 1);
	for (int i = 1; i <= expl.size(); i++) {
		(*reason)[i] = expl[i - 1];
	}
	return reason;
}

void cumulative_cal(vec<IntVar*>& s, vec<IntVar*>& d, vec<IntVar*>& r, IntVar* limit,
										vec<vec<int> >& cal, vec<int>& taskCal, int rho_in, int resCal_in) {
	list<string> opt;
	cumulative_cal(s, d, r, limit, cal, taskCal, rho_in, resCal_in);
}

void cumulative_cal(vec<IntVar*>& s, vec<IntVar*>& d, vec<IntVar*>& r, IntVar* limit,
										vec<vec<int> >& cal, vec<int>& taskCal, int rho_in, int resCal_in,
										list<string> opt) {
	rassert(s.size() == d.size() && s.size() == r.size());
	// ASSUMPTION
	// - s, d, and r contain the same number of elements

	vec<IntVar*> s_new;
	vec<IntVar*> d_new;
	vec<IntVar*> r_new;
	vec<int> taskCal_new;
	int r_sum = 0;

	for (int i = 0; i < s.size(); i++) {
		if (r[i]->getMax() > 0 && d[i]->getMax() > 0) {
			s_new.push(s[i]);
			d_new.push(d[i]);
			r_new.push(r[i]);
			r_sum += r[i]->getMax();
			taskCal_new.push(taskCal[i]);
		}
	}

	if (r_sum <= limit->getMin()) {
		return;
	}

	// Global cumulative constraint
	new CumulativeCalProp(s_new, d_new, r_new, limit, cal, taskCal_new, rho_in, resCal_in, opt);
}

/********************************************
 * Functions related to the TTEF propagator
 *******************************************/

// Initialisation of various parameters
//
void CumulativeCalProp::ttef_initialise_parameters() {
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
			const int i = task_id[ii];
			new_est[i] = est_2[i];
			new_lct[i] = lct_2[i];
		}
	}
	// Sorting of the task id's arrays
	//
	sort(task_id_est, task_id_est + last_unfixed + 1, sort_est_asc);
	sort(task_id_lct, task_id_lct + last_unfixed + 1, sort_lct_asc);
	// Calculation of 'tt_after_est'
	//
	for (int ii = last_unfixed; ii >= 0; ii--) {
		const int i = task_id_est[ii];
		if (p_idx < 0 || tt_profile[p_idx].end <= est_2[i]) {
			tt_after_est[ii] = energy;
		} else if (tt_profile[p_idx].begin <= est_2[i]) {
			tt_after_est[ii] = energy + tt_profile[p_idx].level * (tt_profile[p_idx].end - est_2[i]);
		} else {
			assert(tt_profile[p_idx].begin > est_2[i]);
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
		if (p_idx < 0 || tt_profile[p_idx].end <= lct_2[i]) {
			tt_after_lct[ii] = energy;
		} else if (tt_profile[p_idx].begin <= lct_2[i]) {
			tt_after_lct[ii] = energy + tt_profile[p_idx].level * (tt_profile[p_idx].end - lct_2[i]);
		} else {
			assert(tt_profile[p_idx].begin > lct_2[i]);
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
bool CumulativeCalProp::ttef_consistency_check(int shift_in) {
	assert(last_unfixed > 0);
	assert(shift_in == 0 || shift_in == 1);
	nb_ttefc_calls++;

	// Some constants
	const int* rPeriods = workingPeriods[resCalendar - 1];
	const int maxLimit = max_limit();

	// Some variables
	int begin;
	int end;
	int workingDays;
	int dur_shift;
	int est_idx_last = last_unfixed;
	int i;
	int j;
	int en_req;
	int en_avail;
	int en_req_free;
	int min_en_avail = -1;
	int lct_idx_last = last_unfixed;
	int i_last = task_id_lct[lct_idx_last];
	bool consistent = true;

	int dom_jj_last = -1;
	int* sumFreeEnergy = new int[last_unfixed + 1];
	for (int ii = 0; ii <= last_unfixed; ii++) {
		const int i = task_id_est[ii];
		sumFreeEnergy[ii] = (ii > 0 ? sumFreeEnergy[ii - 1] : 0) + free_energy2[i];
	}

	end = lct_2[task_id_lct[last_unfixed]] + 1;

	// Outer Loop: iterating over lct in non-increasing order
	//
	for (int ii = last_unfixed; ii >= 0; ii--) {
		i = task_id_lct[ii];
		if (end == lct_2[i]) {
			continue;
		}

		assert(lct_2[i] < lct_2[i_last] || i == i_last);

		// Check whether the current latest completion time have to be considered
		// Dominance rule for skipping time intervals
		workingDays = lct_2[i_last] - lct_2[i];
		if (rho == 0) {
			// Resource is released
			workingDays = (rPeriods[lct_2[i]] - rPeriods[lct_2[i_last]]);
		}
		const int free = maxLimit * workingDays - (tt_after_lct[ii] - tt_after_lct[lct_idx_last]);
		if (min_en_avail >= free) {
			continue;
		}

		lct_idx_last = ii;
		i_last = i;
		min_en_avail = maxLimit * (lct_2[task_id_lct[last_unfixed]] - est_2[task_id_est[0]]);

		end = lct_2[i];
		while (est_2[task_id_est[est_idx_last]] >= end) {
			est_idx_last--;
		}
		en_req_free = 0;

		dom_jj_last = -1;
		// Inner Loop: iterating over est in non-increasing order
		//
		for (int jj = est_idx_last; jj >= 0; jj--) {
			nb_ttefc_steps++;
			j = task_id_est[jj];

			// Dominance rule for skipping time intervals
			if (dom_jj_last >= 0) {
				// Computing an over-approximation of the required energy in the time
				// interval [est_2[j], end)
				const int dom_begin = est_2[j];
				const int dom_en_comp = tt_after_est[0] - tt_after_est[jj + 1];
				const int dom_en_free = sumFreeEnergy[jj] + en_req;
				const int dom_wdays = (rho == 1 ? end - dom_begin : rPeriods[dom_begin] - rPeriods[end]);
				const int dom_en_avail = maxLimit * dom_wdays - dom_en_comp - dom_en_free;
				if (dom_en_avail >= min_en_avail) {
					break;
				}
			}

			assert(est_2[j] < end);
			begin = est_2[j];
			if (lct_2[j] <= end) {
				// Task lies in the considered time interval
				en_req_free += free_energy2[j];
			} else if (shift_in == 1) {
				// Task might partially lie in the considered time interval
				dur_shift = get_free_dur_right_shift2(begin, end, j);
				// Adjusting dur_shift if resource stays engaged
				if (rho == 1) {
					const int dur_fixed = max(0, ect_2[j] - lst_2[j]);
					dur_shift = min(min_energy2[j] / min_usage(j) - dur_fixed, dur_shift);
				}
				en_req_free += min_usage(j) * dur_shift;
			}
			en_req = en_req_free + tt_after_est[jj] - tt_after_lct[ii];
			// TTEF_cal: Consider resource calendar
			workingDays = end - begin;
			if (rho == 0) {
				// Resource is released
				workingDays = rPeriods[begin] - rPeriods[end];
			}
			en_avail = maxLimit * workingDays - en_req;

			if (min_en_avail > en_avail) {
				min_en_avail = en_avail;
				dom_jj_last = jj;
			}

			// Check for resource overload
			//
			if (en_avail < 0) {
				consistent = false;
				ii = -1;
				break;
			}
		}
	}

	delete[] sumFreeEnergy;

	if (!consistent) {
		vec<Lit> expl;
		// Increment the inconsistency counter
		nb_ttef_incons++;
		if (so.lazy) {
#if CUMUVERB > 0
			fprintf(stderr, "Entering TTEF Inconsistent\n");
#endif
			list<TaskDur> tasks_tw;
			list<TaskDur> tasks_cp;
			int en_req1 = 0;
			// Retrieve tasks involved
			en_req1 = ttef_retrieve_tasks(shift_in, begin, end, -1, tasks_tw, tasks_cp);
			assert(en_req1 >= en_req);
			// Calculate the lifting TTEF_cal: added breaks
			int en_lift = en_req1 - 1 - maxLimit * workingDays;
			int breaks = end - begin - workingDays;
			assert(en_lift >= 0);
			// Explaining the overload
#if CUMUVERB > 0
			fprintf(stderr, "Explaining TTEF Overload\n");
#endif
			ttef_analyse_limit_and_tasks(begin, end, breaks, tasks_tw, tasks_cp, en_lift, expl);
			assert(expl.size() > 0);
		}
#if CUMUVERB > 0
		fprintf(stderr, "TTEF Submitting Explanation\n");
#endif
		// Submitting of the conflict explanation
		submit_conflict_explanation(expl);
#if CUMUVERB > 0
		fprintf(stderr, "TTEF END Submitting Explanation: %d\n", consistent);
#endif
	}
	return consistent;
}

// TTEF bounds propagation
//
bool CumulativeCalProp::ttef_bounds_propagation(int shift_in1, int shift_in2) {
	std::queue<TTEFUpdate> update1;
	std::queue<TTEFUpdate> update2;
	// TODO LB bound on the limit
	// LB bounds on the start times
#if CUMUVERB > 0
	fprintf(stderr, "Entering TTEF Bounds Propagtion\n");
#endif
	if (!ttef_bounds_propagation_lb(shift_in1, update1)) {
		// Inconsistency
		return false;
	}
	// UB bounds on the start times
	if (!ttef_bounds_propagation_ub(shift_in2, update2)) {
		// Inconsistency
		return false;
	}
#if CUMUVERB > 0
	fprintf(stderr, "TTEF Bounds Propagtion\n");
#endif
	// Updating the bounds
	if (!ttef_update_bounds(shift_in1, update1)) {
		return false;
	}
	if (!ttef_update_bounds(shift_in2, update2)) {
		return false;
	}
#if CUMUVERB > 0
	fprintf(stderr, "Leaving TTEF Bounds Propagtion\n");
#endif
	return true;
}

bool CumulativeCalProp::ttef_bounds_propagation_lb(int shift_in,
																									 std::queue<TTEFUpdate>& update_queue) {
	assert(last_unfixed > 0);
	assert(shift_in == 0 || shift_in == 1);
	// Begin and end of the time interval [begin, end)

	// Some constants
	const int maxLimit = max_limit();
	const int* rPeriods = workingPeriods[resCalendar - 1];

	// Some variables
	int begin;
	int end;
	int dur_shift;
	int est_idx_last = last_unfixed;
	int i;
	int j;
	int en_req;
	int en_avail;
	int en_req_free;
	int update_en_req_start;
	int update_idx;
	int update_workDays_req_in;
	int min_en_avail = -1;
	int min_begin = minTime - 1;
	int workingDays = 0;
	bool consistent = true;

	int maxEnergy = 0;
	int lct_idx_last = -1;
	int* sumFreeEnergy = new int[last_unfixed + 1];
	for (int ii = 0; ii <= last_unfixed; ii++) {
		const int i = task_id_est[ii];
		maxEnergy = max(maxEnergy, min_usage(i) * (rho == 1 ? ect_2[i] - est_2[i] : min_dur(i)));
		sumFreeEnergy[ii] = (ii == 0 ? 0 : sumFreeEnergy[ii - 1]) + free_energy2[i];
	}

	end = lct_2[task_id_lct[last_unfixed]] + 1;

	// Outer Loop: iterating over lct in non-increasing order
	//
	for (int ii = last_unfixed; ii >= 0; ii--) {
		i = task_id_lct[ii];
		if (end == lct_2[i]) {
			continue;
		}

		// Dominance rule for skipping time intervals
		if (min_en_avail >= 0) {
			const int dom_wdays = (rho == 1 ? end - lct_2[i] : rPeriods[lct_2[i]] - rPeriods[end]);
			const int dom_en_comp = tt_after_lct[ii] - tt_after_lct[lct_idx_last];
			const int dom_en_avail = maxLimit * dom_wdays - dom_en_comp;
			if (min_en_avail - dom_en_avail >= maxEnergy) {
				continue;
			}
		}
		lct_idx_last = ii;
		// Check whether the current latest completion time have to be considered
		min_en_avail = maxLimit * (lct_2[task_id_lct[last_unfixed]] - est_2[task_id_est[0]]);
		min_begin = minTime - 1;

		end = lct_2[i];
		while (est_2[task_id_est[est_idx_last]] >= end) {
			est_idx_last--;
		}

		// Initialisations for the inner loop
		en_req_free = 0;
		en_req = 0;
		update_idx = -1;
		update_en_req_start = -1;
		update_workDays_req_in = -1;

		// Inner Loop: iterating over est in non-increasing order
		//
		for (int jj = est_idx_last; jj >= 0; jj--) {
			nb_ttef_lb_calls++;
			j = task_id_est[jj];

			assert(est_2[j] < end);

			// Check for TTEEF propagation in the time interval [min_begin, end)
			if (minTime <= min_begin && tteef_filt) {
				tteef_bounds_propagation_ub(min_begin, end, min_en_avail, j, update_queue);
			}

			// TTEF Dominance rule for skipping time intervals
			// NOTE this rule can cut off TTEEF propagation
			if (jj < est_idx_last) {
				// Computing an over-estimate of the energy in the time interval [est_2[j], end)
				const int dom_wdays = (rho == 1 ? end - est_2[j] : rPeriods[est_2[j]] - rPeriods[end]);
				const int dom_en_comp = tt_after_est[0] - tt_after_est[jj + 1];
				const int dom_en_free = sumFreeEnergy[jj] + en_req;
				const int dom_en_avail = maxLimit * dom_wdays - dom_en_comp - dom_en_free;
				if (dom_en_avail >= min_en_avail && dom_en_avail >= maxEnergy) {
					break;
				}
			}

			begin = est_2[j];

			// Computing the required free energy of task 'j' in the
			// time interval [begin, end)
			if (lct_2[j] <= end) {
				// Task 'j' lies in the considered time interval
				en_req_free += free_energy2[j];
			} else {
				// Task might partially lie in the considered time interval
				const int cal_idx = taskCalendar[j] - 1;
				const int* wPeriods = workingPeriods[cal_idx];
				const int ect_in = min(end, ect_2[j]);
				int workDays_req_in = 0;
				// Add the compulsory part of 'j' to the required energy in the time interval [begin, end)
				if (lst_2[j] < ect_2[j]) {
					const int begin_comp = min(end, lst_2[j]);
					workDays_req_in +=
							(rho == 1 ? ect_in - begin_comp : wPeriods[begin_comp] - wPeriods[ect_in]);
				}

				// Computing the required energy in the time interval [begin, end)
				// considering the right shift
				if (shift_in == 1) {
					dur_shift = get_free_dur_right_shift2(begin, end, j);
					// Adjusting dur_shift if resource stays engaged
					if (rho == 1) {
						const int dur_fixed = max(0, ect_2[j] - lst_2[j]);
						dur_shift = min(min_energy2[j] / min_usage(j) - dur_fixed, dur_shift);
					}
					workDays_req_in += dur_shift;
					en_req_free += min_usage(j) * dur_shift;
				}

				// Calculation of the additional required energy for starting at est_2[j]
				// in time window [begin, end)
				const int workDays_start =
						(rho == 1 ? ect_in - est_2[j] : wPeriods[est_2[j]] - wPeriods[ect_in]);
				const int en_req_start = min_usage(j) * (workDays_start - workDays_req_in);
				assert(workDays_start >= workDays_req_in);
				if (en_req_start > update_en_req_start) {
					update_en_req_start = en_req_start;
					update_workDays_req_in = workDays_req_in;
					update_idx = jj;
				}
			}

			// Adding the energy from the time table profile (compulsory parts)
			en_req = en_req_free + tt_after_est[jj] - tt_after_lct[ii];

			// Calculate the available energy in the time window [begin, end)
			workingDays = (rho == 1 ? end - begin : rPeriods[begin] - rPeriods[end]);
			en_avail = maxLimit * workingDays - en_req;

			// Update the time window [., end) with the minimal available energy
			// Note is required for the TTEEF propagation
			if (min_en_avail > en_avail) {
				min_en_avail = en_avail;
				min_begin = begin;
			}

			// Check for resource overload
			if (en_avail < 0) {
				consistent = false;
				ii = -1;
				break;
			}

			// Check for a lower bound update for the start time
			if (en_avail < update_en_req_start) {
				// Reset 'j' to the task to be updated
				j = task_id_est[update_idx];
				// Calculation of the possible new lower bound wrt.
				// the current time interval [begin, end)
				const int en_avail_new = en_avail + update_workDays_req_in * min_usage(j);
				const int wdays_avail = en_avail_new / min_usage(j);
				const int start_new = ttef_get_new_start_time(begin, end, j, wdays_avail);
				// Check whether a new lower bound was found
				// - nfnl-rule TODO
				if (start_new > new_est[j]) {
					// Push possible update into the queue
					update_queue.push(TTEFUpdate(j, start_new, begin, end, 1));
					new_est[j] = start_new;
				}
			}
		}
	}

	delete[] sumFreeEnergy;

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
			int breaks = end - begin - workingDays;
			int en_lift = en_req1 - 1 - maxLimit * (end - begin - breaks);
			assert(en_lift >= 0);
			// Explaining the overload
			ttef_analyse_limit_and_tasks(begin, end, breaks, tasks_tw, tasks_cp, en_lift, expl);
			assert(expl.size() > 0);
		}
		// Submitting of the conflict explanation
		submit_conflict_explanation(expl);
#if CUMUVERB > 0
		fprintf(stderr, "TTEF Inconsistency detected LB");
#endif
	}
	return consistent;
}

bool CumulativeCalProp::ttef_bounds_propagation_ub(int shift_in,
																									 std::queue<TTEFUpdate>& update_queue) {
	assert(last_unfixed > 0);
	assert(shift_in == 0 || shift_in == 2);

	// Some constants
	const int maxLimit = max_limit();
	const int* rPeriods = workingPeriods[resCalendar - 1];

	// Some variables
	// Begin and end of the time interval [begin, end)
	int begin;
	int end = -1;
	int dur_shift;
	int lct_idx_last = 0;
	int i;
	int j;
	int en_req;
	int en_avail;
	int en_req_free;
	int update_en_req_end;
	int update_idx;
	int update_workDays_req_in;
	int min_en_avail = -1;
	int min_end = minTime - 1;
	int workingDays = 0;
	bool consistent = true;

	int maxEnergy = 0;
	int est_idx_last = -1;
	int maxLength = 0;
	int* sumFreeEnergy = new int[last_unfixed + 2];
	sumFreeEnergy[last_unfixed + 1] = 0;
	for (int ii = last_unfixed; ii >= 0; ii--) {
		const int i = task_id_lct[ii];
		maxLength = (rho == 1 ? max(lct_2[i] - lst_2[i], ect_2[i] - est_2[i]) : min_dur(i));
		maxEnergy = max(maxEnergy, min_usage(i) * maxLength);
		sumFreeEnergy[ii] = sumFreeEnergy[ii + 1] + free_energy2[i];
	}

	begin = est_2[task_id_est[0]] - 1;

	// Outer Loop: iterating over est in non-decreasing order
	//
	for (int ii = 0; ii <= last_unfixed; ii++) {
		i = task_id_est[ii];
		if (begin == est_2[i]) {
			continue;
		}

		// Dominance rule for skipping time intervals
		if (min_en_avail >= 0) {
			const int dom_wdays = (rho == 1 ? est_2[i] - begin : rPeriods[begin] - rPeriods[est_2[i]]);
			const int dom_en_comp = tt_after_est[est_idx_last] - tt_after_est[ii];
			const int dom_en_avail = maxLimit * dom_wdays - dom_en_comp;
			if (min_en_avail - dom_en_avail >= maxEnergy) {
				continue;
			}
		}
		est_idx_last = ii;

		// Intialisation for the minimal avaible energy of a time interval starting
		// at begin
		min_en_avail = maxLimit * (lct_2[task_id_lct[last_unfixed]] - est_2[task_id_est[0]]);
		min_end = minTime - 1;

		begin = est_2[i];
		while (lct_2[task_id_lct[lct_idx_last]] <= begin) {
			lct_idx_last++;
		}

		// Initialisations for the inner loop
		en_req = 0;
		en_req_free = 0;
		en_avail = -1;
		update_idx = -1;
		update_en_req_end = -1;
		update_workDays_req_in = -1;

		// Inner Loop: iterating over lct in non-decreasing order
		//
		for (int jj = lct_idx_last; jj <= last_unfixed; jj++) {
			nb_ttef_ub_calls++;
			j = task_id_lct[jj];

			assert(lct_2[j] > begin);

			// Check for TTEEF propagation in the time interval [begin, min_end)
			if (minTime <= min_end && tteef_filt) {
				tteef_bounds_propagation_lb(begin, min_end, min_en_avail, j, update_queue);
			}

			// TTEF Dominance rule for skipping time intervals
			// NOTE this rule can cut off TTEEF propagation
			if (jj > lct_idx_last) {
				// Computing an over-estimate of the energy in the time interval [begin, lct_2[j])
				const int dom_wdays = (rho == 1 ? lct_2[j] - begin : rPeriods[begin] - rPeriods[lct_2[j]]);
				const int dom_en_comp = tt_after_lct[jj - 1];
				const int dom_en_free = sumFreeEnergy[jj] + en_req;
				const int dom_en_avail = maxLimit * dom_wdays - dom_en_comp - dom_en_free;
				if (dom_en_avail >= min_en_avail && dom_en_avail >= maxEnergy) {
					break;
				}
			}

			// Update end
			end = lct_2[j];

			// Computing the required free energy of task 'j' in the
			// time interval [begin, end)
			if (begin <= est_2[j]) {
				// Task lies in the considered time interval [begin, end)
				en_req_free += free_energy2[j];
			} else {
				// Task might partially lie in the considered time interval
				const int cal_idx = taskCalendar[j] - 1;
				const int* wPeriods = workingPeriods[cal_idx];
				const int lst_in = max(begin, lst_2[j]);
				int workDays_req_in = 0;
				// Add the compulsory part of 'j' to the required energy in the time interval [begin, end)
				if (lst_2[j] < ect_2[j]) {
					const int end_comp = max(begin, ect_2[j]);
					workDays_req_in += (rho == 1 ? end_comp - lst_in : wPeriods[lst_in] - wPeriods[end_comp]);
				}

				// Computing the required energy in the time interval [begin, end)
				// considering the lef shift
				if (shift_in == 2) {
					dur_shift = get_free_dur_left_shift2(begin, end, j);
					// Adjusting dur_shift if resource stays engaged
					if (rho == 1) {
						const int dur_fixed = max(0, ect_2[j] - lst_2[j]);
						dur_shift = min(min_energy2[j] / min_usage(j) - dur_fixed, dur_shift);
					}
					workDays_req_in += dur_shift;
					en_req_free += min_usage(j) * dur_shift;
				}

				// Calculation of the additional required energy for ending at lct_2[j]
				// in time window [begin, end)
				const int workDays_end =
						(rho == 1 ? lct_2[j] - lst_in : wPeriods[lst_in] - wPeriods[lct_2[j]]);
				const int en_req_end = min_usage(j) * (workDays_end - workDays_req_in);
				assert(workDays_end >= workDays_req_in);
				if (en_req_end > update_en_req_end) {
					update_en_req_end = en_req_end;
					update_workDays_req_in = workDays_req_in;
					update_idx = jj;
				}
			}

			// Adding the energy from the time table profile (compulsory parts)
			en_req = en_req_free + tt_after_est[ii] - tt_after_lct[jj];

			// Calculate the available energy in the time interval [begin, end)
			workingDays = (rho == 1 ? end - begin : rPeriods[begin] - rPeriods[end]);
			en_avail = maxLimit * workingDays - en_req;

			// Update the time window [begin, .) with the minimal available energy
			// Note is required for the TTEEF propagation
			if (min_en_avail > en_avail) {
				min_en_avail = en_avail;
				min_end = end;
			}

			// Check for resource overload
			if (en_avail < 0) {
				consistent = false;
				ii = last_unfixed + 1;
				break;
			}

			// Check for an upper bound update for the start time
			if (en_avail < update_en_req_end) {
				// Reset 'j' to the task to be updated
				j = task_id_lct[update_idx];
				// Calculation of the possible upper bound wrt.
				// the current time interval [begin , end)
				const int en_avail_new = en_avail + update_workDays_req_in * min_usage(j);
				const int wdays_avail = en_avail_new / min_usage(j);
				const int end_new = ttef_get_new_end_time(begin, end, j, wdays_avail);
				// Check whether a new upper bound was found
				// - nfnl-rule TODO
				if (end_new < new_lct[j]) {
					// Push possible update into queue
					update_queue.push(TTEFUpdate(j, end_new, begin, end, 0));
					new_lct[j] = end_new;
				}
			}
		}
	}

	delete[] sumFreeEnergy;

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
			int breaks = end - begin - workingDays;
			int en_lift = en_req1 - 1 - maxLimit * (end - begin - breaks);
			assert(en_lift >= 0);
			// Explaining the overload
			ttef_analyse_limit_and_tasks(begin, end, breaks, tasks_tw, tasks_cp, en_lift, expl);
			assert(expl.size() > 0);
		}
		// Submitting of the conflict explanation
		submit_conflict_explanation(expl);
#if CUMUVERB > 0
		fprintf(stderr, "TTEF Inconsistency detected UB");
#endif
	}
	return consistent;
}

// Checking for TTEEF propagation on lower bound in the
// time window [begin, end)
void CumulativeCalProp::tteef_bounds_propagation_lb(const int begin, const int end,
																										const int en_avail, const int j,
																										std::queue<TTEFUpdate>& update_queue) {
	if (begin <= est_2[j] || ect_2[j] <= begin) {
		return;
	}

	// Some useful constants
	const int* wPeriods = workingPeriods[taskCalendar[j] - 1];
	const int est_in = max(begin, est_2[j]);
	const int ect_in = min(end, ect_2[j]);
	assert(est_in <= ect_in);

	// Computing the compulsory part in the time interval [begin, end)
	int wdays_in = 0;
	if (lst_2[j] < ect_2[j]) {
		const int end_comp_in = max(begin, ect_in);
		wdays_in += (rho == 1 ? end_comp_in - est_in : wPeriods[est_in] - wPeriods[end_comp_in]);
	}

	// Computing the working days in the time interval [begin, end) when
	// task 'j' is executed to its earliest start time
	const int wdays_start_in = (rho == 1 ? ect_in - est_in : wPeriods[est_in] - wPeriods[ect_in]);
	assert(wdays_start_in >= wdays_in);

	// Checking for lower bound propagation
	if (en_avail < min_usage(j) * (wdays_start_in - wdays_in)) {
		// Calculate new lower bound
		const int wdays_avail = (en_avail / min_usage(j)) + wdays_in;
		const int est_new = ttef_get_new_start_time(begin, end, j, wdays_avail);
		// Check whether a new lower bound was found
		if (est_new > new_est[j]) {
			// Push possible update into the queue
			update_queue.push(TTEFUpdate(j, est_new, begin, end, 1));
			new_est[j] = est_new;
		}
	}
}

// Checking for TTEEF propagation on upper bound in the
// time window [begin, end)
void CumulativeCalProp::tteef_bounds_propagation_ub(const int begin, const int end,
																										const int en_avail, const int j,
																										std::queue<TTEFUpdate>& update_queue) {
	if (lst_2[j] >= end || lct_2[j] <= begin || est_2[j] >= begin) {
		return;
	}

	// Some useful constants
	const int* wPeriods = workingPeriods[taskCalendar[j] - 1];
	const int lst_in = max(begin, lst_2[j]);
	const int lct_in = min(end, lct_2[j]);

	// Computing the compulsory part in time interval [begin, end)
	int wdays_in = 0;
	if (lst_2[j] < ect_2[j]) {
		const int end_comp_in = max(begin, lct_in);
		wdays_in += (rho == 1 ? end_comp_in - lst_in : wPeriods[lst_in] - wPeriods[end_comp_in]);
	}

	// Computing the working days in the time interval [begin, end) when
	// task 'j' is executed to its latest start time
	const int wdays_end_in = (rho == 1 ? lct_in - lst_in : wPeriods[lst_in] - wPeriods[lct_in]);
	assert(wdays_end_in >= wdays_in);

	// Checking for upper bound propagation
	if (en_avail < min_usage(j) * (wdays_end_in - wdays_in)) {
		// Calculate new upper bound
		const int wdays_avail = (en_avail / min_usage(j)) + wdays_in;
		const int lct_new = ttef_get_new_end_time(begin, end, j, wdays_avail);
		// Check whether a new upper bound was found
		if (lct_new < new_lct[j]) {
			// Push possible update into the queue
			update_queue.push(TTEFUpdate(j, lct_new, begin, end, 0));
			new_lct[j] = lct_new;
		}
	}
}

int CumulativeCalProp::ttef_get_new_start_time(const int begin, const int end, const int task,
																							 const int min_wdays_in) {
	assert(min_wdays_in >= 0);
	if (min_wdays_in == 0) {
		const int* cal = calendar[taskCalendar[task] - 1];
		int est = end;
		while (est <= maxTime && cal[est] == 0) {
			est++;
		}
		return est;
	}
	if (rho == 0) {
		// Resource is released
		return getStartTimeForEndTime(task, end, min_wdays_in);
	}
	// Resource stays engaged
	const int* cal = calendar[taskCalendar[task] - 1];
	const int begin_in = max(begin, est_2[task]);
	const int end_in = min(end, ect_2[task]);
	assert(begin_in < end_in);
	int wdays_in = end_in - begin_in;
	assert(wdays_in > min_wdays_in);
	// const int max_est = min(max_start0(task), end - min_wdays_in);
	const int max_est = max_start0(task);
	int last_est = est_2[task];
	int last_wdays_in = wdays_in;
	int est = est_2[task] + 1;
	int ect = ect_2[task] + 1;

	for (; est <= max_est; est++, ect++) {
		// Updating the working days
		assert(cal[est - 1] == 1);
		if (begin <= last_est) {
			wdays_in--;
		}
		// Computing the new start time and updating the working days
		while (cal[est] == 0 && est <= max_est) {
			if (begin <= est) {
				wdays_in--;
			}
			est++;
		}
		if (est > max_est) {
			return last_est;
		}
		// Computing the new end time and updating the working days
		assert(cal[ect - 2] == 1);
		while (cal[ect - 1] == 0) {
			if (ect <= end) {
				wdays_in++;
			}
			ect++;
		}
		// Updating the working days
		if (ect <= end) {
			wdays_in++;
		}
		// Checking working days
		if (wdays_in == min_wdays_in || (last_wdays_in > min_wdays_in && wdays_in < min_wdays_in)) {
			return est;
		}
		if (wdays_in < min_wdays_in) {
			return last_est;
		}
		// Updating last valid earliest start time
		last_est = est;
		last_wdays_in = wdays_in;
	}

	return last_est;
}

int CumulativeCalProp::ttef_get_new_end_time(const int begin, const int end, const int task,
																						 const int min_wdays_in) {
	assert(min_wdays_in >= 0);
	if (min_wdays_in == 0) {
		const int* cal = calendar[taskCalendar[task] - 1];
		int lct = begin;
		while (minTime < lct && cal[lct - 1] == 0) {
			lct--;
		}
		return lct;
	}
	if (rho == 0) {
		// Resource is released
		return getEndTimeForStartTime(task, begin, min_wdays_in);
	}
	// Resource stays engaged
	const int* cal = calendar[taskCalendar[task] - 1];
	const int begin_in = max(begin, lst_2[task]);
	const int end_in = min(end, lct_2[task]);
	assert(begin_in < end_in);
	int wdays_in = end_in - begin_in;
	assert(wdays_in > min_wdays_in);
	const int lst0 = min_start0(task);
	int last_lct = lct_2[task];
	int last_wdays_in = wdays_in;
	int lst = lst_2[task] - 1;
	int lct = lct_2[task] - 1;

	for (; lst <= lst0; lst--, lct--) {
		assert(cal[lst + 1] == 1);
		// Computing the new start time and updating the working days
		while (cal[lst] == 0 && lst0 <= lst) {
			if (begin <= lst) {
				wdays_in++;
			}
			lst++;
		}
		if (lst < lst0) {
			return last_lct;
		}
		// Updating the working days
		if (begin <= lst) {
			wdays_in++;
		}
		// Updating the working days
		if (lct < end) {
			wdays_in--;
		}
		// Computing the new end time and updating the working days
		assert(cal[lct] == 1);
		while (cal[lct - 1] == 0) {
			if (lct <= end) {
				wdays_in--;
			}
			lct--;
		}
		// Checking the working days
		if (wdays_in == min_wdays_in || (last_wdays_in > min_wdays_in && wdays_in < min_wdays_in)) {
			return lct;
		}
		if (wdays_in < min_wdays_in) {
			return last_lct;
		}
		// Updating the last valid latest completion time
		last_lct = lct;
		last_wdays_in = wdays_in;
	}
	return last_lct;
}

void CumulativeCalProp::ttef_explanation_for_update_lb(int shift_in, const int begin, const int end,
																											 const int task, int& bound, vec<Lit>& expl) {
	// Some constants
	const int maxLimit = max_limit();
	const int* rPeriods = workingPeriods[resCalendar - 1];
	const int* wPeriods = workingPeriods[taskCalendar[task] - 1];

	// Some variables
	list<TaskDur> tasks_tw;
	list<TaskDur> tasks_cp;

	// Retrieving tasks involved in the time interval [begin, end) excluding task 'task'
	const int en_req = ttef_retrieve_tasks(shift_in, begin, end, task, tasks_tw, tasks_cp);

	// Calculating the available energy in the time interval [begin, end)
	const int wdays = (rho == 1 ? end - begin : rPeriods[begin] - rPeriods[end]);
	const int en_avail = maxLimit * wdays - en_req;
	const int breaks = end - begin - wdays;

	// Calculating the working days available for the task 'task' in the considered time interval
	const int wdays_avail = en_avail / min_usage(task);
	const int min_wdays_in = wdays_avail + 1;

	// Determining the new lower bound on the start time
	const int new_lb = ttef_get_new_start_time(begin, end, task, wdays_avail);

	// Some consistency checks
	assert(new_lb >= bound);
	assert(rho == 0 ||
				 en_avail < min_usage(task) * (min(end, ect_2[task]) - max(begin, est_2[task])));
	assert(rho == 1 || en_avail < min_usage(task) * (wPeriods[max(begin, est_2[task])] -
																									 wPeriods[min(end, ect_2[task])]));

	// Calculating the explanation lower bound on the start time
	int expl_wdays_in;
	int expl_lb;
	switch (ttef_expl_deg) {
		case ED_NORMAL:
		case ED_LIFT:
			expl_lb = ttef_analyse_tasks_left_shift(begin, end, min_wdays_in, task, 0, expl_wdays_in);
		case ED_NAIVE:
		default:
			expl_lb = est_2[task];
			const int expl_begin = max(begin, expl_lb);
			const int expl_end = min(end, ect_2[task]);
			expl_wdays_in =
					(rho == 1 ? expl_end - expl_begin : wPeriods[expl_begin] - wPeriods[expl_end]);
	}

	// Calculating the lifting energy for the remainder
	int en_lift = min_usage(task) - 1 - (en_avail % min_usage(task));

	// More consistency checks
	assert(expl_lb <= est_2[task]);
	assert(expl_wdays_in >= wdays_avail + 1);
	assert(en_lift >= 0);

	// Explaining the update for task 'task'
	if (expl_lb > min_start0(task)) {
		// start[task] >= expl_lb
		expl.push(getNegGeqLit(start[task], expl_lb));
	}
	// Get the negated literal for [[dur[task] >= min_dur(task)]]
	if (min_dur0(task) < min_dur(task)) {
		expl.push(getNegGeqLit(dur[task], min_dur(task)));
	}
	// Get the negated literal for [[usage[task] >= min_usage(task)]]
	if (min_usage0(task) < min_usage(task)) {
		expl.push(getNegGeqLit(usage[task], min_usage(task)));
	}

	// Retrieve explanation for the remaining tasks
	ttef_analyse_limit_and_tasks(begin, end, breaks, tasks_tw, tasks_cp, en_lift, expl);

	// Assigning new lower bound
	bound = new_lb;
}

void CumulativeCalProp::ttef_explanation_for_update_ub(int shift_in, const int begin, const int end,
																											 const int task, int& bound, vec<Lit>& expl) {
	// Some constants
	const int maxLimit = max_limit();
	const int* rPeriods = workingPeriods[resCalendar - 1];
	const int* wPeriods = workingPeriods[taskCalendar[task] - 1];

	// Some variables
	list<TaskDur> tasks_tw;
	list<TaskDur> tasks_cp;

	// Retrieving tasks involved in the time interval [begin, end) excluding task 'task'
	const int en_req = ttef_retrieve_tasks(shift_in, begin, end, task, tasks_tw, tasks_cp);

	// Calculating the available energy in the time interval [begin, end)
	const int wdays = (rho == 1 ? end - begin : rPeriods[begin] - rPeriods[end]);
	const int en_avail = maxLimit * wdays - en_req;
	const int breaks = end - begin - wdays;

	// Calculating the working days available for the task 'task' in the considered time interval
	const int wdays_avail = en_avail / min_usage(task);
	const int min_wdays_in = wdays_avail + 1;

	// Determining the new upper bound on the latest completion time
	const int new_lct = ttef_get_new_end_time(begin, end, task, wdays_avail);

	// Some consistency checks
	assert(new_lct <= bound);
	assert(rho == 0 ||
				 en_avail < min_usage(task) * (min(end, lct_2[task]) - max(begin, lst_2[task])));
	assert(rho == 1 || en_avail < min_usage(task) * (wPeriods[max(begin, lst_2[task])] -
																									 wPeriods[min(end, lct_2[task])]));

	// Calculating the explanation lower bound on the start time
	int expl_wdays_in;
	int expl_ub;
	switch (ttef_expl_deg) {
		case ED_NORMAL:
		case ED_LIFT:
			expl_ub = ttef_analyse_tasks_right_shift(begin, end, min_wdays_in, task, 0, expl_wdays_in);
		case ED_NAIVE:
		default:
			expl_ub = lst_2[task];
			const int expl_begin = max(begin, expl_ub);
			const int expl_end = min(end, lct_2[task]);
			expl_wdays_in =
					(rho == 1 ? expl_end - expl_begin : wPeriods[expl_begin] - wPeriods[expl_end]);
	}

	// Calculating the lifting energy for the remainder
	int en_lift = min_usage(task) - 1 - (en_avail % min_usage(task));

	// More consistency checks
	assert(expl_ub >= lst_2[task]);
	assert(expl_wdays_in >= wdays_avail + 1);
	assert(en_lift >= 0);

	// Explaining the update for task 'task'
	if (expl_ub < max_start0(task)) {
		// start[task] <= expl_ub
		expl.push(getNegLeqLit(start[task], expl_ub));
	}
	// Get the negated literal for [[dur[task] >= min_dur(task)]]
	if (min_dur0(task) < min_dur(task)) {
		expl.push(getNegGeqLit(dur[task], min_dur(task)));
	}
	// Get the negated literal for [[usage[task] >= min_usage(task)]]
	if (min_usage0(task) < min_usage(task)) {
		expl.push(getNegGeqLit(usage[task], min_usage(task)));
	}

	// Retrieve explanation for the remaining tasks
	ttef_analyse_limit_and_tasks(begin, end, breaks, tasks_tw, tasks_cp, en_lift, expl);

	// Assigning new lower bound
	bound = new_lct;
}

bool CumulativeCalProp::ttef_update_bounds(int shift_in, std::queue<TTEFUpdate>& queue_update) {
	while (!queue_update.empty()) {
		const int task = queue_update.front().task;
		int bound = queue_update.front().bound_new;
		const int begin = queue_update.front().tw_begin;
		const int end = queue_update.front().tw_end;
		Clause* reason = nullptr;
		if (queue_update.front().is_lb_update) {
			// Lower bound update
			if (new_est[task] == bound) {
				if (so.lazy) {
					vec<Lit> expl;
					ttef_explanation_for_update_lb(shift_in, begin, end, task, bound, expl);
					reason = get_reason_for_update(expl);
				}
				nb_ttef_filt++;
				// Update the lower bound
				if (!start[task]->setMin(bound, reason)) {
					// Conflict occurred
					return false;
				}
				// Set bound_update to true
				bound_update = true;
#if CUMUVERB > 0
				fprintf(stderr, "Bounds Update LB\n");
#endif
			}
		} else {
			// Upper bound update
			if (new_lct[task] == bound) {
				if (so.lazy) {
					vec<Lit> expl;
					ttef_explanation_for_update_ub(shift_in, begin, end, task, bound, expl);
					reason = get_reason_for_update(expl);
				}
				// Update the lower bound
				const int new_ub = getStartTimeForEndTime(task, bound, min_dur(task));
#if CUMUVERB > 0
				fprintf(stderr, "Bounds Update UB: task = %d, old = %d, new = %d \n", task, lst_2[task],
								new_ub);
#endif
				nb_ttef_filt++;
				if (!start[task]->setMax(new_ub, reason)) {
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

int CumulativeCalProp::ttef_retrieve_tasks(const int shift_in, const int begin, const int end,
																					 const int fb_id, list<TaskDur>& tasks_tw,
																					 list<TaskDur>& tasks_cp) {
	int en_req = 0;
	int dur_comp;
	int dur_shift;
	int dur_in;
	// Getting fixed tasks
	for (int ii = 0; ii < task_id.size(); ii++) {
		const int i = task_id[ii];
		if (i == fb_id || lct_2[i] <= begin || end <= est_2[i]) {
			continue;
		}
		if (begin <= est_2[i] && lct_2[i] <= end) {
			// Task lies in the time interval [begin, end)
			en_req += min_energy2[i];
			const int usedDays = min_energy2[i] / min_usage(i);
			tasks_tw.emplace_back(i, usedDays);
			continue;
		}
		if (lst_2[i] < ect_2[i] && is_intersecting(begin, end, lst_2[i], ect_2[i])) {
			// Compulsory part partially or fully lies in [begin, end)
			const int begin_comp = max(begin, lst_2[i]);
			const int end_comp = min(end, ect_2[i]);
			dur_comp = end_comp - begin_comp;
			if (rho == 0) {
				const int cal_idx = taskCalendar[i] - 1;
				dur_comp = workingPeriods[cal_idx][begin_comp] - workingPeriods[cal_idx][end_comp];
			}
			dur_shift = 0;
			if (shift_in == 1) {
				dur_shift = get_free_dur_right_shift2(begin, end, i);
				assert(begin <= est_2[i] || dur_shift == 0);
				// Adjusting dur_shift if the resource stays engaged
				if (rho == 1) {
					const int dur_fixed = max(0, ect_2[i] - lst_2[i]);
					dur_shift = min(min_energy2[i] / min_usage(i) - dur_fixed, dur_shift);
				}
			} else {
				assert(shift_in == 2);
				dur_shift = get_free_dur_left_shift2(begin, end, i);
				// Adjusting dur_shift if the resource stays engaged
				if (rho == 1) {
					const int dur_fixed = max(0, ect_2[i] - lst_2[i]);
					dur_shift = min(min_energy2[i] / min_usage(i) - dur_fixed, dur_shift);
				}
			}
			dur_in = dur_comp + dur_shift;
			en_req += min_usage(i) * dur_in;
			tasks_cp.emplace_back(i, dur_in);
			continue;
		}
		// Task 'i' should not have a compulsory part overlapping the time window [begin, end)
		dur_in = 0;
		if (shift_in == 1) {
			dur_in = get_free_dur_right_shift2(begin, end, i);
			assert(begin <= est_2[i] || dur_in == 0);
			// Adjusting dur_shift if the resource stays engaged
			if (rho == 1) {
				const int dur_fixed = max(0, ect_2[i] - lst_2[i]);
				dur_in = min(min_energy2[i] / min_usage(i) - dur_fixed, dur_in);
			}
		} else {
			assert(shift_in == 2);
			dur_in = get_free_dur_left_shift2(begin, end, i);
			assert(lct_2[i] <= end || dur_in == 0);
			// Adjusting dur_shift if the resource stays engaged
			if (rho == 1) {
				const int dur_fixed = max(0, ect_2[i] - lst_2[i]);
				dur_in = min(min_energy2[i] / min_usage(i) - dur_fixed, dur_in);
			}
		}
		if (0 < dur_in) {
			// Task partially lies in [begin, end)
			en_req += min_usage(i) * dur_in;
			tasks_tw.emplace_back(i, dur_in);
		}
	}
	return en_req;
}

void CumulativeCalProp::ttef_analyse_limit_and_tasks(const int begin, const int end,
																										 const int breaks, list<TaskDur>& tasks_tw,
																										 list<TaskDur>& tasks_cp, int& en_lift,
																										 vec<Lit>& expl) {
	// Getting	explanation for tasks in the time window
	ttef_analyse_tasks(begin, end, tasks_tw, en_lift, expl);
	// Getting explanation for tasks with compulsory parts
	ttef_analyse_tasks(begin, end, tasks_cp, en_lift, expl);
	// Getting explanation for the resource capacity
	int diff_limit = max_limit0() - max_limit();
	if (diff_limit > 0) {
		// Calculate possible lifting
		int lift_limit = min(en_lift / (end - begin - breaks), diff_limit);
		en_lift -= lift_limit * (end - begin - breaks);
		assert(en_lift >= 0);
		if (lift_limit < diff_limit) {
			// limit[%d] <= max_limit() + lift_limit
			expl.push(getNegLeqLit(limit, max_limit() + lift_limit));
		}
	}
}

int CumulativeCalProp::ttef_analyse_tasks_right_shift(const int begin, const int end,
																											const int dur_in, const int task,
																											const int max_dur_lift, int& last_dur) {
	// Some assumptions
	assert(est_2[task] < end && begin < lct_2[task]);

	// Defining some constants
	const int lst0 = max_start0(task);
	if (dur_in <= max_dur_lift) {
		last_dur = 0;
		return lst0;
	}
	// Defining more constants
	const int cal_idx = taskCalendar[task] - 1;
	const int* wPeriods = workingPeriods[cal_idx];
	const int* tCal = calendar[cal_idx];
	const int min_dur_in = dur_in - max_dur_lift;
	const int begin_in = max(begin, min(lst_2[task], end));
	const int end_in = min(lct_2[task], end);
	// Defining some variables
	int workDays = (rho == 1 ? end_in - begin_in : wPeriods[begin_in] - wPeriods[end_in]);
	int last_lst = lst_2[task];
	last_dur = workDays;
	int lst = lst_2[task] + 1;
	int lct = lct_2[task] + 1;

	assert(workDays >= dur_in);

	// Determining the latest possible start time and the number of workDays in the time window
	// [begin, end)
	for (; lst <= lst0; lst++, lct++) {
		if (last_lst >= begin) {
			workDays--;
		}
		// Determining the new start time
		assert(tCal[lst - 1] == 1);
		while (tCal[lst] == 0 && lst <= lst0) {
			if (rho == 1 && lst >= begin) {
				workDays--;
			}
			lst++;
		}
		if (lst > lst0) {
			return last_lst;
		}
		// Determining the new end time
		assert(tCal[lct - 2] == 1);
		while (tCal[lct - 1] == 0) {
			if (rho == 1 && lct <= end) {
				workDays++;
			}
			lct++;
		}
		if (lct <= end) {
			workDays++;
		}
		// Check the number of working days in the time window [begin, end)
		if (workDays < min_dur_in) {
			return last_lst;
		}
		// Saving valid shift
		last_lst = lst;
		last_dur = workDays;

		// Some cross checks
		assert(min_dur(task) == wPeriods[last_lst] - wPeriods[lct]);
		assert(rho == 0 || workDays == min(end, lct) - max(begin, last_lst));
		assert(rho == 1 || workDays == wPeriods[max(begin, last_lst)] - wPeriods[min(end, lct)]);
		assert(ttef_analyse_tasks_check_expl_ub(begin, end, task, min_dur_in, last_lst));
	}
	return last_lst;
}

int CumulativeCalProp::ttef_analyse_tasks_left_shift(const int begin, const int end,
																										 const int dur_in, const int task,
																										 const int max_dur_lift, int& last_dur) {
	// Determining the earliest start time so that a certain number of work days are within the time
	// window [begin, end)
	assert(est_2[task] < end && begin < lct_2[task]);
	const int est0 = min_start0(task);
	if (dur_in <= max_dur_lift) {
		last_dur = 0;
		return est0;
	}
	// Some useful constants
	const int cal_idx = taskCalendar[task] - 1;
	const int* wPeriods = workingPeriods[cal_idx];
	const int* tCal = calendar[cal_idx];
	const int min_dur_in = dur_in - max_dur_lift;
	const int end_in = min(ect_2[task], end);
	const int begin_in = max(est_2[task], begin);
	int wdays = (rho == 1 ? end_in - begin_in : wPeriods[begin_in] - wPeriods[end_in]);
	int last_est = est_2[task];
	last_dur = wdays;
	int ect = ect_2[task] - 1;
	int est = est_2[task] - 1;
	for (; est >= est0; est--, ect--) {
		assert(tCal[last_est] == 1);
		// Determining the new start time and updating the number of working days
		while (tCal[est] == 0 && est >= est0) {
			if (rho == 1 && est >= begin) {
				wdays++;
			}
			est--;
		}
		if (est < est0) {
			return last_est;
		}
		if (est >= begin) {
			wdays++;
		}
		// Determining the new end time and updating the number of working days
		assert(tCal[ect] == 1);
		if (ect < end) {
			wdays--;
		}
		while (tCal[ect - 1] == 0) {
			if (rho == 1 && ect <= end) {
				wdays--;
			}
			ect--;
		}
		// Check the number of working days in the time window [begin, end)
		if (wdays < min_dur_in) {
			return last_est;
		}
		// Saving last valid shift
		last_est = est;
		last_dur = wdays;
		// Some consistency checks
		assert(min_dur(task) == wPeriods[last_est] - wPeriods[ect]);
		assert(rho == 1 || wdays == wPeriods[max(last_est, begin)] - wPeriods[min(ect, end)]);
		assert(rho == 0 || wdays == min(ect, end) - max(last_est, begin));
		assert(ttef_analyse_tasks_check_expl_lb(begin, end, task, min_dur_in, last_est));
	}
	return last_est;
}

bool CumulativeCalProp::ttef_analyse_tasks_check_expl_lb(const int begin, const int end,
																												 const int task, const int dur_in,
																												 const int expl_lb) {
	const int cal_idx = taskCalendar[task] - 1;
	const int ect = getEndTimeForStartTime(task, expl_lb, min_dur(task));
	const int begin_expl = max(begin, expl_lb);
	const int end_expl = max(begin, min(end, ect));
	const int dur_expl_in =
			(rho == 1 ? end_expl - begin_expl
								: workingPeriods[cal_idx][begin_expl] - workingPeriods[cal_idx][end_expl]);
	if (dur_in > dur_expl_in) {
#if CUMUVERB > 2
		printf("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n");
		printf("EXPL LB\n");
		printf(" tw [%d, %d); expl_lb %d\n", begin, end, expl_lb);
		printf(" task %d: start [%d, %d]; end [%d, %d];\n", task, est_2[task], lst_2[task], ect_2[task],
					 lct_2[task]);
		printf(" start0 [%d, %d]\n", min_start0(task), max_start0(task));
		printf(" min_dur %d; dur_in %d;\n", min_dur(task), dur_in);
		printf(" min_energy2 %d; min_usage %d;\n", min_energy2[task], min_usage(task));
		printf(" tw_expl [%d, %d]; dur_expl_in %d, rho %d\n", begin_expl, end_expl, dur_expl_in, rho);
		for (int i = max(minTime, begin - 5); i < min(maxTime, end + 5); i++) {
			printf("%d ", calendar[cal_idx][i]);
		}
		printf("\n");
#endif
		return false;
	}
	return true;
}

bool CumulativeCalProp::ttef_analyse_tasks_check_expl_ub(const int begin, const int end,
																												 const int task, const int dur_in,
																												 const int expl_ub) {
	const int cal_idx = taskCalendar[task] - 1;
	const int lct = getEndTimeForStartTime(task, expl_ub, min_dur(task));
	const int end_expl = min(lct, end);
	const int lst = max(begin, min(end, expl_ub));
	const int dur_expl_in =
			(rho == 1 ? end_expl - lst
								: workingPeriods[cal_idx][lst] - workingPeriods[cal_idx][end_expl]);
	if (dur_in > dur_expl_in) {
#if CUMUVERB > 2
		printf("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n");
		printf("EXPL UB\n");
		printf(" tw [%d, %d); expl_ub %d\n", begin, end, expl_ub);
		printf(" task %d: start [%d, %d]; end [%d, %d];\n", task, est_2[task], lst_2[task], ect_2[task],
					 lct_2[task]);
		printf(" start0 [%d, %d]\n", min_start0(task), max_start0(task));
		printf(" min_dur %d; dur_in %d;\n", min_dur(task), dur_in);
		printf(" min_energy2 %d; min_usage %d;\n", min_energy2[task], min_usage(task));
		printf(" lst [%d, %d]; dur_expl_in %d, rho %d\n", lst, end_expl, dur_expl_in, rho);
		for (int i = max(minTime, begin - 5); i < min(maxTime, end + 5); i++) {
			printf("%d ", calendar[cal_idx][i]);
		}
		printf("\n");
#endif
		return false;
	}
	return true;
}

void CumulativeCalProp::ttef_analyse_tasks(const int begin, const int end, list<TaskDur>& tasks,
																					 int& en_lift, vec<Lit>& expl) {
	while (!tasks.empty()) {
		const int i = tasks.front().task;
		int dur_in = tasks.front().dur_in;
		int expl_lb;
		int expl_ub;
		int est0 = min_start0(i);
		int lst0 = max_start0(i);
		// TTEF_cal: running variable for loops t, storages for execution times sto1 and sto2
		int t;
		int sto1;
		int sto2;
		// Calculate possible lifting
		// TTEF_cal: several changes were necessary
		switch (ttef_expl_deg) {
			case ED_NORMAL:
				// XXX Is min_dur correct
				if (rho == 1) {
					// Resource stays engaged
					sto1 = workingPeriods[taskCalendar[i] - 1][begin] -
								 workingPeriods[taskCalendar[i] - 1][begin + dur_in];
					sto2 = min_dur(i) - sto1;
					sto1 = 0;
					t = begin;
					while (sto1 < sto2 && t > 0) {
						if (calendar[taskCalendar[i] - 1][t - 1] == 1) {
							sto1++;
						}
						t--;
					}
					expl_lb = min(est_2[i], t);
					expl_ub = lst_2[i];  // max(lst_2[i], end - dur_in);
				} else {
					// Resource is released
					sto1 = 0;
					sto2 = min_dur(i) - dur_in;
					t = begin;
					while (sto1 < sto2 && t > 0) {
						if (calendar[taskCalendar[i] - 1][t - 1] == 1) {
							sto1++;
						}
						t--;
					}
					expl_lb = min(est_2[i], t);
					sto1 = 0;
					sto2 = dur_in;
					t = end;
					while (sto1 < sto2 && t > 0) {
						if (calendar[taskCalendar[i] - 1][t - 1] == 1) {
							sto1++;
						}
						t--;
					}
					expl_ub = max(lst_2[i], t);
				}
				// expl_lb = begin + dur_in - min_dur(i); expl_ub = end - dur_in;
				break;
			//-----------------------------------------------------------
			case ED_LIFT: {
				int dur_in_lb = 0;
				int dur_in_ub = 0;
				// Computing maximal lift for the work days inside the time window [begin, end)
				const int max_lift = en_lift / min_usage(i);
				// Computing the lifted lower and upper bound on the start time
				expl_lb = ttef_analyse_tasks_left_shift(begin, end, dur_in, i, max_lift, dur_in_lb);
				expl_ub = ttef_analyse_tasks_right_shift(begin, end, dur_in, i, max_lift, dur_in_ub);
				// Some consistency checks
				assert(dur_in - dur_in_lb <= max_lift);
				assert(dur_in - dur_in_ub <= max_lift);
				assert(ttef_analyse_tasks_check_expl_lb(begin, end, i, min(dur_in_lb, dur_in_ub), expl_lb));
				assert(ttef_analyse_tasks_check_expl_ub(begin, end, i, min(dur_in_lb, dur_in_ub), expl_ub));
				// Computing the used lift
				const int dur_lift = dur_in - min(dur_in_lb, dur_in_ub);
				// Updating the remaining energy for lifting
				en_lift -= min_usage(i) * dur_lift;
			} break;
			//-----------------------------------------------------------
			case ED_NAIVE:
			default:
				expl_lb = est_2[i];
				expl_ub = lst_2[i];
		}
		// printf("%d: dur_in %d/%d; en_in %d; est0 %d; lst0 %d\t", i, dur_in, dur[i], dur_in *
		// min_usage(i), est0, lst0);
		if (est0 < expl_lb) {
			// printf("s[%d] >= %d; ", i, expl_lb);
			expl.push(getNegGeqLit(start[i], expl_lb));
		}
		if (expl_ub < lst0) {
			// printf("s[%d] <= %d; ", i, expl_ub);
			expl.push(getNegLeqLit(start[i], expl_ub));
		}
		// Get the negated literal for [[dur[i] >= min_dur(i)]]
		if (min_dur0(i) < min_dur(i)) {
			expl.push(getNegGeqLit(dur[i], min_dur(i)));
		}
		// Get the negated literal for [[usage[i] >= min_usage(i)]]
		if (min_usage0(i) < min_usage(i)) {
			expl.push(getNegGeqLit(usage[i], min_usage(i)));
		}
		// printf("\n");
		tasks.pop_front();
	}
}

inline bool CumulativeCalProp::is_intersecting(const int begin1, const int end1, const int begin2,
																							 const int end2) {
	return ((begin1 <= begin2 && begin2 < end1) || (begin2 <= begin1 && begin1 < end2));
}

/*** EOF ***/
