#include <ctime>
#include <cstring>
#include <chuffed/core/options.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/sat.h>
#include <chuffed/vars/int-var.h>
#include <chuffed/parallel/parallel.h>

Slave slave;

#ifdef PARALLEL

Slave::Slave() :
		thread_no(-1)
	, check_freq       (0.005)
	, report_freq      (1)
	, status           (RES_UNK)
	, next_check       (0)
	, report_message   (sizeof(Report)/sizeof(int),0)
{}

void Slave::solve() {

	thread_no = so.thread_no;

	srand(thread_no+1);

	checks = rand()%int(report_freq/check_freq);

	MPI_Buffer_attach(malloc(MPI_BUFFER_SIZE), MPI_BUFFER_SIZE);

	if (FULL_DEBUG) fprintf(stderr, "Solving\n");

	sendReport();
	while (receiveJob()) {
		real_time -= wallClockTime();
//		cpu_time -= cpuTime();
		status = engine.search();
		real_time += wallClockTime();
//		cpu_time += cpuTime();
		sendReport();
	}

	sendStats();
}

bool Slave::receiveJob() {
	double t;

	profile_start();

	if (FULL_DEBUG) fprintf(stderr, "%d: Waiting for job\n", thread_no);

	while (true) {
		MPI_Probe(0, MPI_ANY_TAG, MPI_COMM_WORLD, &s);
		if (s.MPI_TAG == FINISH_TAG) { profile_end("finish", 0); return false; }
		MPI_Get_count(&s, MPI_INT, &message_length);
		if (s.MPI_TAG == JOB_TAG) break;
		if (s.MPI_TAG == LEARNTS_TAG) { receiveLearnts(); continue; }
		assert(s.MPI_TAG != LEARNTS_TAG);
		MPI_Recv(&message_length, message_length, MPI_INT, 0, s.MPI_TAG, MPI_COMM_WORLD, &s); 
	}

	assert(message_length <= TEMP_SC_LEN);

	MPI_Recv((int*) sat.temp_sc, message_length, MPI_INT, 0, JOB_TAG, MPI_COMM_WORLD, &s);

	profile_end("receive job", message_length);

	if (FULL_DEBUG) fprintf(stderr, "%d: Received job\n", thread_no);

//	for (int i = 0; i < message_length; i++) fprintf(stderr, "%d ", message[i]); fprintf(stderr, "\n");

	sat.convertToClause(*sat.temp_sc);
	for (int i = 0; i < engine.assumptions.size(); i++) {
		sat.decVarUse(engine.assumptions[i]/2);
	}
	engine.assumptions.clear();
	for (int i = 0; i < sat.out_learnt.size(); i++) {
		engine.assumptions.push(toInt(sat.out_learnt[i]));
		sat.incVarUse(engine.assumptions.last()/2);
	}
	sat.btToLevel(0);
	status = RES_SEA;

//	fprintf(stderr, "%d: Assumptions received: ", thread_no);
//	for (int i = 0; i < assumptions.size(); i++) fprintf(stderr, "%d ", assumptions[i]);
//	fprintf(stderr, "\n");

	if (FULL_DEBUG) fprintf(stderr, "%d: Parsed job\n", thread_no);

	return true;
}

bool Slave::checkMessages() {
	if (engine.decisionLevel() <= engine.assumptions.size()) return false;

	double t = wallClockTime();

	if (t <= next_check) return false;

	real_time += t;
//	cpu_time += cpuTime();

	int received;

	while (true) {
		MPI_Iprobe(0, MPI_ANY_TAG, MPI_COMM_WORLD, &received, &s);
		if (!received) break;
		switch (s.MPI_TAG) {
			case INTERRUPT_TAG:
				MPI_Recv(NULL, 0, MPI_INT, 0, INTERRUPT_TAG, MPI_COMM_WORLD, &s);
				if (PAR_DEBUG) fprintf(stderr, "%d: Interrupted! %f\n", thread_no, wallClockTime());
				real_time -= wallClockTime();
//				cpu_time -= cpuTime();
				return true;
			case STEAL_TAG:
				splitJob();
				break;
			case LEARNTS_TAG:
				receiveLearnts();
				break;
			default:
				assert(false);
		}
	}

	if (++checks%int(report_freq/check_freq) == 0) {
		sendReport();
	}

	t = wallClockTime();
	next_check = t + check_freq;

	real_time -= t;
//	cpu_time -= cpuTime();

	return false;
}

void Slave::sendReport() {
	if (FULL_DEBUG) fprintf(stderr, "%d: Forming report\n", thread_no);

	Report& r = *((Report*) (int*) report_message);
	r.status = status;

	if (FULL_DEBUG) fprintf(stderr, "%d: Sending report to master\n", thread_no);

	profile_start();

	MPI_Bsend((int*) report_message, report_message.size(), MPI_INT, 0, REPORT_TAG, MPI_COMM_WORLD);

	profile_end("send result", report_message.size());

	if (FULL_DEBUG) fprintf(stderr, "%d: Sent report to master\n", thread_no);

	report_message.clear();
	report_message.growTo(sizeof(Report)/sizeof(int),0);

	sat.updateShareParam();

}


void Slave::splitJob() {
	vec<int> message;
	int num_splits;

	profile_start();

	MPI_Recv(&num_splits, 1, MPI_INT, 0, STEAL_TAG, MPI_COMM_WORLD, &s);

	int max_splits = engine.decisionLevel() - engine.assumptions.size() - 1;
	if (num_splits > max_splits) num_splits = max_splits;
	if (num_splits < 0) num_splits = 0;

	if (FULL_DEBUG) fprintf(stderr, "%d: Splitting %d jobs\n", thread_no, num_splits);

	for (int i = 0; i < num_splits; i++) {
		engine.assumptions.push(toInt(sat.decLit(engine.assumptions.size()+1)));
		sat.incVarUse(engine.assumptions.last()/2);
	}
	assert(num_splits == 0 || engine.decisionLevel() > engine.assumptions.size());

	vec<Lit> ps;
	for (int i = 0; i < engine.assumptions.size(); i++) ps.push(toLit(engine.assumptions[i]));
	Clause *c = Clause_new(ps);
	sat.convertToSClause(*c);
	free(c);
	message.push(num_splits);
	sat.temp_sc->pushInVec(message);

	MPI_Bsend((int*) message, message.size(), MPI_INT, 0, SPLIT_TAG, MPI_COMM_WORLD);

	profile_end("send split job", message.size());

	if (FULL_DEBUG) fprintf(stderr, "%d: Sent %d split job to master\n", thread_no, message[0]);
}

void Slave::receiveLearnts() {
	if (PAR_DEBUG) fprintf(stderr, "%d: Adding foreign clauses, current level = %d\n", thread_no, sat.decisionLevel());

	profile_start();

	MPI_Probe(0, LEARNTS_TAG, MPI_COMM_WORLD, &s);
	MPI_Get_count(&s, MPI_INT, &message_length);
	message = (int*) malloc(message_length*sizeof(int));
	MPI_Recv(message, message_length, MPI_INT, 0, LEARNTS_TAG, MPI_COMM_WORLD, &s);
	Report& r = *((Report*) message);

	profile_end("receive learnts", message_length);

	profile_start();

//	for (int i = 0; i < message_length; i++) fprintf(stderr, "%d ", message[i]); fprintf(stderr, "\n");

	SClause *sc = (SClause*) r.data;
	for (int i = 0; i < r.num_learnts; i++) {
		sat.convertToClause(*sc);
		if (sc->size == 1) {
			Lit x = sat.out_learnt[0];
			if (sat.value(x) != l_True || sat.level[var(x)] != 0) {
				sat.btToLevel(0);
				if (sat.value(x) == l_False) assert(false);
				sat.enqueue(x);
			}
		} else {
			sat.addLearnt();
		}
		sc = sc->getNext();
	}

	profile_end("processing learnts", message_length);

	if (PAR_DEBUG) fprintf(stderr, "%d: Added foreign clauses, new level = %d\n", thread_no, sat.decisionLevel());

	free(message);

}

void SAT::convertToSClause(Clause& c) {
	assert(c.size() <= TEMP_SC_LEN/2);
	temp_sc->size = c.size();
	temp_sc->extra = 0;
	temp_sc->source = so.thread_no;
	int j = 0;
	for (int i = 0; i < c.size(); i++) {
		int vid = c_info[var(c[i])].vid;
		if (vid != -1 && engine.vars[vid]->getType() == INT_VAR_LL) {
			temp_sc->data[j++] = 0x8000000 + vid;
			temp_sc->data[j++] = c_info[var(c[i])].v ^ sign(c[i]);
			temp_sc->extra++;
		} else {
			temp_sc->data[j++] = toInt(c[i]);
		}
	}
}

void SAT::convertToClause(SClause& sc) {
	out_learnt.clear();
	int *pt = sc.data;
	for (int i = 0; i < sc.size; i++) {
		if (0x8000000 & *pt) {
			IntVar *v = engine.vars[0x7ffffff & *pt];
			assert(v->getType() == INT_VAR_LL);
			Lit p = ((IntVarLL*) v)->createLit(pt[1]);
			out_learnt.push(p);
			pt += 2;
		} else {
			out_learnt.push(toLit(*pt));
			pt += 1;
		}
	}
}

void SAT::addLearnt() {
	vec<Lit> &c = out_learnt;
	bool enqueue_first = false;

	int j = 0;
	Lit t;
	while (value(c[j]) == l_False && ++j < c.size());
	if (j == c.size()) {
		int hlevel = level[var(c[0])]; j = 0;
		for (int k = 1; k < c.size(); k++) if (level[var(c[k])] > hlevel) {hlevel = level[var(c[k])]; j = k;}
		if (hlevel == 0) { engine.status = RES_GUN; return; }
		btToLevel(hlevel-1);
		assert(value(c[j]) == l_Undef);
	}
	t = c[0]; c[0] = c[j]; c[j] = t;
	assert(value(c[0]) != l_False);

	j = 1;

	while (value(c[j]) == l_False && ++j < c.size());
	if (j == c.size()) {
		int hlevel = level[var(c[1])]; j = 1;
		for (int k = 2; k < c.size(); k++) if (level[var(c[k])] > hlevel) {hlevel = level[var(c[k])]; j = k;}
		if (value(c[0]) != l_True || level[var(c[0])] > hlevel) {
			btToLevel(hlevel);
			if (decisionLevel() == hlevel) enqueue_first = true;
		}
	}
	t = c[1]; c[1] = c[j];	c[j] = t;

	assert(value(c[0]) == l_True || (value(c[0]) != l_False && value(c[1]) != l_False) || enqueue_first);

	Clause *r = Clause_new(c, true);
	r->activity()  = cla_inc;

	addClause(*r, so.one_watch);

//	if (r->size() <= 2) sat.rtrail.push(r);

	if (enqueue_first) enqueue(c[0], r);

}


void Slave::sendStats() {
	MPI_Reduce(&engine.conflicts, NULL, 1, MPI_LONG_LONG_INT, MPI_SUM, 0, MPI_COMM_WORLD);
	MPI_Reduce(&engine.propagations, NULL, 1, MPI_LONG_LONG_INT, MPI_SUM, 0, MPI_COMM_WORLD);
	MPI_Reduce(&engine.opt_time, NULL, 1, MPI_DOUBLE, MPI_MAX, 0, MPI_COMM_WORLD);

	if (PROFILING) fprintf(stderr, "%d: Real time spent searching = %f\n", thread_no, real_time);
	if (PROFILING) fprintf(stderr, "%d: CPU time spent searching = %f\n", thread_no, cpu_time);
}

//--------
// Minor methods

void Slave::shareClause(Clause& c) {
	sat.convertToSClause(c);
	sat.temp_sc->pushInVec(report_message);
	((Report*) (int*) report_message)->num_learnts++;
}

#endif
