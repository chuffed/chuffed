#include <ctime>
#include <cstring>
#include <chuffed/core/options.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/sat.h>
#include <chuffed/parallel/parallel.h>

Master master;

#ifdef PARALLEL

Master::Master() :
		num_threads(0)
	, thread_no(-1)
	, min_share_time   (1.0)
	, min_job_time     (0.025)
	, num_free_slaves  (0)
	, status           (RES_UNK)
	, shared           (0)
	, shared_len       (0)
	, real_time        (0)
	, cpu_time         (0)
{}


void Master::initMPI() {
	MPI_Init(NULL, NULL);
  MPI_Comm_size(MPI_COMM_WORLD, &so.num_threads);
  MPI_Comm_rank(MPI_COMM_WORLD, &so.thread_no);

	so.num_threads--;
	so.thread_no--;

//	printf("num_threads = %d, thread_no = %d\n", so.num_threads, so.thread_no);

	if (so.num_threads > MAX_SLAVES) ERROR("Maximum number of slaves (%d) exceeded!\n", MAX_SLAVES);
}

void Master::finalizeMPI() {
	MPI_Finalize();
}

void Master::solve() {	

//	fprintf(stderr, "Start master solve\n");

	num_threads = so.num_threads;
	job_start_time.growTo(num_threads, DONT_DISTURB);
	cur_job.growTo(num_threads, NULL);
	lhead.growTo(num_threads, 0);
	last_send_learnts.growTo(num_threads, 0);
	global_learnts.reserve(10000000);

	job_queue.push(new SClause());

	MPI_Buffer_attach(malloc(MPI_BUFFER_SIZE), MPI_BUFFER_SIZE);

//	fprintf(stderr, "Start master loop\n");
	// Search:
	while (status == RES_UNK && time(NULL) < so.time_out) {

		while (num_free_slaves > 0 && job_queue.size() > 0) sendJob();

		int received;
		MPI_Iprobe(MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &received, &s);
		if (received) {
			double t;
			profile_start();
			switch (s.MPI_TAG) {
				case REPORT_TAG:
					receiveReport();
					profile_end("receive report", 0);
					continue;
				case SPLIT_TAG:
					receiveJobs();
					profile_end("receive jobs", 0);
					continue;
				default:
					assert(false);
			}
		}

		if (job_queue.size() < 2*num_threads-2) { stealJobs(); continue; }

		usleep(500);
	}

	if (PAR_DEBUG) fprintf(stderr, "End of problem called\n");
	MPI_Request r;
	for (int i = 0; i < num_threads; i++) {
		MPI_Isend(NULL, 0, MPI_INT, i+1, INTERRUPT_TAG, MPI_COMM_WORLD, &r);
		MPI_Isend(NULL, 0, MPI_INT, i+1, FINISH_TAG, MPI_COMM_WORLD, &r);
	}

	while (num_free_slaves != num_threads) {
		MPI_Probe(MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &s);
		int thread_no = s.MPI_SOURCE-1;

		MPI_Get_count(&s, MPI_INT, &message_length);
		message = (int*) malloc(message_length*sizeof(int));
		MPI_Recv(message, message_length, MPI_INT, s.MPI_SOURCE, s.MPI_TAG, MPI_COMM_WORLD, &s);
		if (s.MPI_TAG == REPORT_TAG) {
			if (message[0] != RES_SEA) {
				assert(job_start_time[thread_no] != NOT_WORKING);
				num_free_slaves++;
				job_start_time[thread_no] = NOT_WORKING;
				if (PAR_DEBUG) fprintf(stderr, "%d is free, %f\n", thread_no, wallClockTime());
			}
		}

		free(message);
	}

	collectStats();
//	printStats();

}


void Master::receiveReport() {
	int thread_no = s.MPI_SOURCE-1;

	MPI_Get_count(&s, MPI_INT, &message_length);
	message = (int*) malloc(message_length*sizeof(int));
	MPI_Recv(message, message_length, MPI_INT, s.MPI_SOURCE, REPORT_TAG, MPI_COMM_WORLD, &s);
	Report& r = *((Report*) message);

//	for (int i = 0; i < message_length; i++) fprintf(stderr, "%d ", message[i]); fprintf(stderr, "\n");

	if (PAR_DEBUG) fprintf(stderr, "Received report %d from %d\n", r.status, thread_no);

	if (r.status == RES_SEA) {
		if (wallClockTime() - last_send_learnts[thread_no] > min_share_time) sendLearnts(thread_no);
	}

	if (r.status != RES_SEA) {
		assert(job_start_time[thread_no] != NOT_WORKING);
		num_free_slaves++;
		job_start_time[thread_no] = NOT_WORKING;
		if (PAR_DEBUG) fprintf(stderr, "%d is free, %f\n", thread_no, wallClockTime());
	}

	if (r.status == RES_GUN) status = RES_GUN;
	if (r.status == RES_SAT) status = RES_SAT;

	if (r.status == RES_LUN && updateProgress(cur_job[thread_no]->size)) {
		for (int i = 0; i < num_threads; i++) assert(job_start_time[i] == NOT_WORKING);
		assert(job_queue.size() == 0);
		fprintf(stderr, "Search finished!\n");
		status = RES_GUN;
	}

	if (num_free_slaves == num_threads && job_queue.size() == 0 && status != RES_GUN) {
		for (int i = 0; i < search_progress.size(); i++) fprintf(stderr, "%d ", search_progress[i]);
		assert(false);
	}

//	fprintf(stderr, "message length = %d: ", message_length);
//	for (int i = 1; i < message_length; i++) fprintf(stderr, "%d ", message[i]);

	if (status != RES_GUN) receiveLearnts(r, thread_no, message_length);

	free(message);

}

bool Master::updateProgress(int i) {
	search_progress.growTo(i+1,0);
	search_progress[i]++;
	for ( ; i > 0; i--) {
		if (search_progress[i]%2) return false;
		search_progress[i-1] += search_progress[i]/2;
		search_progress[i] = 0;
	}
	return (search_progress[0] == 1);
}

void Master::sendLearnts(int thread_no) {
	if (PAR_DEBUG) fprintf(stderr, "Sending learnts to %d\n", thread_no);

	vec<int> message(sizeof(Report)/sizeof(int),0);
	int num_learnts = 0;

	SClause *sc = (SClause*) &global_learnts[lhead[thread_no]];
	for ( ; (int*) sc != &global_learnts[global_learnts.size()]; sc = sc->getNext()) {
		if (sc->source == thread_no) continue;
		sc->pushInVec(message);
		num_learnts++;
	}
	lhead[thread_no] = global_learnts.size();

	Report& r = *((Report*) (int*) message);
	r.num_learnts = num_learnts;

	profile_start();

	MPI_Bsend((int*) message, message.size(), MPI_INT, thread_no+1, LEARNTS_TAG, MPI_COMM_WORLD);

	last_send_learnts[thread_no] = wallClockTime();

	profile_end("send learnts", message.size())
}

void Master::receiveLearnts(Report& r, int thread_no, int message_length) {
	if (FULL_DEBUG) fprintf(stderr, "Parsing learnts from %d\n", thread_no);

	SClause *sc = (SClause*) r.data;
	for (int i = 0; i < r.num_learnts; i++) {
		assert(sc->size > 0);
		if (sc->size == 1) {
			sat.convertToClause(*sc);
			Lit x = sat.out_learnt[0];
			if (sat.value(x) == l_False) { status = RES_GUN; return; }
			if (sat.value(x) == l_Undef) { sat.enqueue(x); }
		}
		shared++;
		shared_len += sc->size;
		sc->pushInVec(global_learnts);
		sc = sc->getNext();
	}

	if (global_learnts.size() > global_learnts.capacity()/2) {
		int first = global_learnts.size();
		for (int i = 0; i < num_threads; i++) if (lhead[i] < first) first = lhead[i];
		for (int i = 0; i < num_threads; i++) lhead[i] -= first;
		for (int i = first; i < global_learnts.size(); i++) global_learnts[i-first] = global_learnts[i];
		global_learnts.shrink(first);
//		fprintf(stderr, "Shrink global learnts by %d\n", first);
	}

	if (FULL_DEBUG) fprintf(stderr, "Received learnts from %d\n", thread_no);
}


void Master::sendJob() {
	if (PAR_DEBUG) fprintf(stderr, "Finding free slave\n");

	profile_start();

	int thread_no = rand()%(num_threads);
	while (job_start_time[thread_no] != NOT_WORKING) thread_no = (thread_no+1)%num_threads;

	num_free_slaves--;
	job_start_time[thread_no] = wallClockTime();
	if (PAR_DEBUG) fprintf(stderr, "Sending job to %d\n", thread_no);
	
	int job_num = selectJob(thread_no);
	if (cur_job[thread_no]) free(cur_job[thread_no]);
	cur_job[thread_no] = job_queue[job_num];
	job_queue[job_num] = job_queue.last();
	job_queue.pop();

	MPI_Request r;
	MPI_Isend((int*) cur_job[thread_no], cur_job[thread_no]->memSize(), MPI_INT, thread_no+1, JOB_TAG, MPI_COMM_WORLD, &r);
	MPI_Request_free(&r);

	if (PROFILING && job_queue.size() <= 4) fprintf(stderr, "Number of jobs left in queue: %d\n", job_queue.size());
}



int Master::selectJob(int thread_no) {
	assert(job_queue.size());
	int best_job = -1;

	int longest_match = -1;
	for (int i = 0; i < job_queue.size(); i++) {
		int j, k = (job_queue.size()*thread_no/num_threads + i) % job_queue.size();
		if (cur_job[thread_no] == NULL) { best_job = k; break; }
		for (j = 0; j < job_queue[k]->memSize()-1 && j < cur_job[thread_no]->memSize()-1; j++) {
			if (job_queue[k]->data[j] != cur_job[thread_no]->data[j]) break;
		}
		if (j > longest_match) {
			longest_match = j;
			best_job = k;
		}
	}

	assert(best_job != -1);
	return best_job;
}

void Master::stealJobs() {
	int num_splits = 4-2*job_queue.size()/(num_threads-1);
	assert(num_splits > 0);

//	fprintf(stderr, "Check for busy slave, free slaves = %d\n", num_free_slaves);

	profile_start();

	int slave = -1;
	double cur_time = wallClockTime();
	double oldest_job = cur_time;
	for (int i = 0; i < num_threads; i++) {
		if (job_start_time[i] < oldest_job) {
			slave = i;
			oldest_job = job_start_time[i];
		}
	}
	if (oldest_job < cur_time-min_job_time) {
		MPI_Bsend(&num_splits, 1, MPI_INT, slave+1, STEAL_TAG, MPI_COMM_WORLD);
		if (PAR_DEBUG) fprintf(stderr, "Steal request sent to %d to steal %d jobs\n", slave, num_splits);
		assert(job_start_time[slave] != NOT_WORKING);
		job_start_time[slave] = DONT_DISTURB;
	} 

	profile_end("steal job", 0);

//	fprintf(stderr, "Sent steal message to %d\n", slave);

}

void Master::receiveJobs() {
	int thread_no = s.MPI_SOURCE-1;

	MPI_Get_count(&s, MPI_INT, &message_length);
	message = (int*) malloc(message_length*sizeof(int));
	MPI_Recv(message, message_length, MPI_INT, s.MPI_SOURCE, SPLIT_TAG, MPI_COMM_WORLD, &s);

	if (PAR_DEBUG) fprintf(stderr, "Received %d jobs from %d\n", message[0], thread_no);
	assert(job_start_time[thread_no] != NOT_WORKING);
	job_start_time[thread_no] = wallClockTime();

	assert(message_length <= TEMP_SC_LEN);

	memcpy(sat.temp_sc, message + 1, (message_length-1) * sizeof(int));
	assert(cur_job[thread_no]->size + message[0] == sat.temp_sc->size);
	free(cur_job[thread_no]);
	cur_job[thread_no] = sat.temp_sc->copy();
	for (int i = 0; i < message[0]; i++) {
		sat.temp_sc->negateLast();
		job_queue.push(sat.temp_sc->copy());
		sat.temp_sc->pop();
	}

	free(message);

//	fprintf(stderr, "New curr job for %d is: ", thread_no);
//	for (int j = 0; j < cur_job[slave].size(); j++) fprintf(stderr, "%d ", cur_job[slave][j]); fprintf(stderr, "\n");

}


void Master::collectStats() {
	int64_t dummy = 0;
	MPI_Reduce(&dummy, &engine.conflicts, 1, MPI_LONG_LONG_INT, MPI_SUM, 0, MPI_COMM_WORLD);
	MPI_Reduce(&dummy, &engine.propagations, 1, MPI_LONG_LONG_INT, MPI_SUM, 0, MPI_COMM_WORLD);
	MPI_Reduce(&dummy, &engine.opt_time, 1, MPI_DOUBLE, MPI_MAX, 0, MPI_COMM_WORLD);
}

void Master::printStats() {
	fprintf(stderr, "%lld shared clauses\n", shared);
	fprintf(stderr, "%.1f avg shared len\n", (double) shared_len / shared);
}

/*
void Master::printStats() {

	double total_time = wallClockTime()-start_time;
	double comm_time = total_time * num_threads - real_time;
	char result_string[20] = "RES_UNK";
	
	if (status == SAT) sprintf(result_string, "SATISFIABLE");
	if (status == RES_GUN) sprintf(result_string, "UNSATISFIABLE"); 

	fprintf(stderr, "===============================================================================\n");
	fprintf(stderr, "conflicts             : %-12lld   (%.0f /sec)\n", conflicts, conflicts/total_time);
	fprintf(stderr, "decisions             : %-12lld   (%.0f /sec)\n", decisions, decisions/total_time);
	fprintf(stderr, "propagations          : %-12lld   (%.0f /sec)\n", propagations, propagations/total_time);
	fprintf(stderr, "shared clauses        : %-12lld   (%.0f /sec)\n", shared, shared/total_time);
	fprintf(stderr, "Slave CPU time        : %g s\n", cpu_time);
	fprintf(stderr, "Master CPU time       : %g s\n", cpuTime());
	fprintf(stderr, "Slave comm time       : %g s\n", comm_time);
	fprintf(stderr, "Total time            : %g s\n", total_time);
	printf("%lld,%lld,%lld,%lld,%g,%g,%g,%g,%s\n", conflicts, decisions, propagations shared, cpu_time, cpuTime(), comm_time, total_time, result_string);

}
*/

#endif

