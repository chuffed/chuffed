#include <chuffed/mip/mip.h>
#include <chuffed/mip/simplex.h>
#include <chuffed/support/misc.h>

#define REFACTOR_FREQ 100
#define AVOID_SMALL_PIVOT 0

// Maximize x_0
// Ax <= b
// x >= 0

Simplex simplex;

Simplex::Simplex()
		: L_cols_zeros(0),
			U_diag_units(0),
			recalc_time(0),
			simplexs(0),
			refactors(0),
			sort_col_ratio(ratio),
			sort_col_nz(AV_nz) {}

void Simplex::init() {
	m = mip->ineqs.size();
	n = mip->vars.size();

	A_size = 0;
	for (int i = 0; i < m; i++) {
		A_size += mip->ineqs[i].a.size();
	}

	if (so.verbosity >= 2) {
		fprintf(stderr, "Number of vars = %d\n", n);
		fprintf(stderr, "Number of cons = %d\n", m);
		fprintf(stderr, "Number of coeffs = %d\n", A_size);
	}

	// Allocate memory

	AH = new IndexVal*[m];
	AV = new IndexVal*[n + m];
	_AH = new IndexVal[A_size];
	_AV = new IndexVal[A_size + m];
	AH_nz = new int[m];
	AV_nz = new int[n + m];

	Y = new long double[m];
	BZ = new long double[m];
	obj = new long double[n + m];
	rhs = new long double[m];
	R1 = new2d<long double>(m, m);
	R2 = new2d<long double>(m, m);
	tm = new long double[m];
	BC = new int[m];

	norm2 = new float[m];
	reduced_costs = new double[n];

	L_cols.growTo(m);
	L_rows.growTo(m);
	U_cols.growTo(m);
	U_rows.growTo(m);

	U_diag = new long double[m];
	U_perm = new int[m];

	lu_factors = new LUFactor[REFACTOR_FREQ + 10];

	lb = new Tint[n + m];
	ub = new Tint[n + m];

	rtoc = new int[m];
	ctor = new int[n + m];
	shift = new int[n + m + 1];

	row = new long double[n + m];
	column = new long double[m];
	ratio = new long double[n + m];
	Z = &row[n];

	// Initialise obj

	obj[0] = 1;
	for (int i = 1; i < m + n; i++) obj[i] = 0;
	obj_bound = 0;

	// Initialise norm2

	for (int i = 0; i < m; i++) norm2[i] = 1;

	// Initialise BC

	for (int i = 0; i < m; i++) BC[i] = 0;

	// Initialise reduced costs

	for (int i = 0; i < n; i++) reduced_costs[i] = 0;

	// Initialise lb and ub

	for (int i = 0; i < n + m; i++) {
		lb[i] = 0;
		ub[i] = 0;
	}

	// Initialise basis and row data

	for (int i = 0; i < m; i++) rtoc[i] = n + i;
	for (int i = 0; i < n; i++) ctor[i] = -1;
	for (int i = 0; i < m; i++) ctor[n + i] = i;
	for (int i = 0; i < n + m; i++) shift[i] = 0;
	shift[n + m] = 2;

	// Initialise var bounds

	for (int i = 1; i < n; i++) {
		lb[i] = mip->vars[i]->getMin();
		ub[i] = mip->vars[i]->getMax();
	}

	// Initialise AH

	IndexVal* cur_A = _AH;
	vec<vec<IndexVal> > temp_A(n);
	for (int i = 0; i < m; i++) {
		AH[i] = cur_A;
		LinearIneq& li = mip->ineqs[i];
		for (int j = 0; j < li.x.size(); j++) {
			int c = mip->var_map.find(li.x[j])->second;
			assert(0 <= c && c < n);
			long double v = (li.lb_notR ? -li.a[j] : li.a[j]);
			if (c == 0 && engine.opt_type == OPT_MAX) v = -v;
			*cur_A++ = IndexVal(c, v);
			temp_A[c].push(IndexVal(i, v));
			//			fprintf(stderr, "%d:%.0Lf ", c, v);
		}
		//		fprintf(stderr, "%.0Lf %.0Lf\n", mip->ineqs[i].lb, mip->ineqs[i].ub);
		AH_nz[i] = cur_A - AH[i];
		lb[n + i] = (int)(li.lb_notR ? mip->ineqs[i].lb : -mip->ineqs[i].ub);
		ub[n + i] = (int)(li.lb_notR ? mip->ineqs[i].ub : -mip->ineqs[i].lb);
		//		for (int j = 0; j < n; j++) fprintf(stderr, "%.0Lf ", A[j][i]); fprintf(stderr, "\n");
	}

	// Initialise AV

	cur_A = _AV;
	for (int i = 0; i < n; i++) {
		AV[i] = cur_A;
		for (int j = 0; j < temp_A[i].size(); j++) {
			*cur_A++ = temp_A[i][j];
		}
		AV_nz[i] = cur_A - AV[i];
	}
	for (int i = 0; i < m; i++) {
		AV[n + i] = cur_A;
		*cur_A++ = IndexVal(i, 1);
		AV_nz[n + i] = 1;
	}

	for (int i = 0; i < n + m; i++) boundChange(i, lb[i]);

	refactorB();

	//	printB();

	pivotObjVar();
}

void Simplex::pivotObjVar() {
	pivot_col = 0;
	pivot_row = -1;

	// find a pivot row
	memset(column, 0, m * sizeof(long double));
	for (int i = 0; i < AV_nz[0]; i++) {
		column[AV[0][i].index()] = AV[0][i].val();
	}
	Bmultiply(column);

	for (int i = 0; i < m; i++) {
		checkZero13(column[i]);
		if (column[i] < 0) {
			pivot_row = i;
			break;
		}
	}
	assert(pivot_row != -1);

	regeneratePivotRow();

	pivot();

	//	printB();

	//	printTableau(true);
	//	exit(0);

	// do bound swaps
	for (int i = 1; i < n; i++) {
		if (obj[i] < 0) boundSwap(i);
	}

	//	printTableau(true);
	//	exit(0);

	//	checkObjective();

	//	checkBasis();
}

// increase var v's bound by d
void Simplex::boundChange(int v, int d) {
	for (int i = 0; i < AV_nz[v]; i++) {
		BC[AV[v][i].index()] -= d * (int)AV[v][i].val();
	}
}

void Simplex::boundSwap(int v) {
	boundChange(v, shift[v] ? -gap(v) : gap(v));
	shift[v] = 1 - shift[v];
}

int Simplex::simplex() {
	if (SIMPLEX_DEBUG) fprintf(stderr, "Simplex step:\n");
	if (SIMPLEX_DEBUG) printObjective();
	if (SIMPLEX_DEBUG) printTableau();

	//	fprintf(stderr, "Objective = %.6f\n", optimum());

	//	printTableau(true);

	//	checkObjective2();

	if (!findPivotRow()) return SIMPLEX_OPTIMAL;

	//	fprintf(stderr, "pivot row = %d\n", pivot_row);

	regeneratePivotRow();

	//	checkObjective2();

	//	if (!findPivotCol()) {
	if (!findPivotCol2()) {
		mip->unboundedFailure();
		return SIMPLEX_UNBOUNDED;
	}

	//	fprintf(stderr, "pivot col = %d\n", pivot_col);

	pivot();

	simplexs++;

	//	printB();

	//	printTableau(true);

	//	checkBasis();

	//	printObjective();

	//	if (SIMPLEX_DEBUG) printTableau();

	//	exit(0);

	// If bound is already good enough to cause failure, return
	if (EARLY_TERM && (int)ceil(optimum()) > mip->objVarBound()) return SIMPLEX_GOOD_ENOUGH;

	return SIMPLEX_IN_PROGRESS;
}

bool Simplex::findPivotRow() {
	// find row with largest violation of constraint

	float best = 0;
	int vio_type = 0;
	pivot_row = -1;

	calcRHS();

	// find exiting row
	for (int i = 0; i < m; i++) {
		int v = rtoc[i];
		if (v == 0) continue;
		float a, val = rhs[i] + (shift[v] ? ub[v] : lb[v]);
		//		fprintf(stderr, "cr %d: %.3Lf %d %d\n", i, val, (int) lb[v], (int) ub[v]);
		// check lower bound
		a = lb[v] - val;
		if (a > obj_limit) {
			if (STEEPEST_EDGE) a /= sqrt(norm2[i]);
			if (a > best) {
				best = a;
				vio_type = 0;
				pivot_row = i;
			}
		}
		// check upper bound
		a = val - ub[v];
		if (val > ub[v] + obj_limit) {
			if (STEEPEST_EDGE) a /= sqrt(norm2[i]);
			if (a > best) {
				best = a;
				vio_type = 1;
				pivot_row = i;
			}
		}
	}
	if (pivot_row == -1) return false;
	pr_violation = best;
	if (STEEPEST_EDGE) pr_violation *= sqrt(norm2[pivot_row]);

	// perform bound swap if necessary

	int v = rtoc[pivot_row];
	if (vio_type != shift[v]) boundSwap(v);

	if (SIMPLEX_DEBUG) fprintf(stderr, "Pivot row = %d\n", pivot_row);

	return true;
}

void Simplex::regeneratePivotRow() {
	memset(row, 0, n * sizeof(long double));
	R_nz.clear();

	calcBInvRow(Z, pivot_row);

	int v = rtoc[pivot_row];

	for (int i = 0; i < m; i++) {
		if (ctor[n + i] >= 0) continue;
		checkZero13(Z[i]);
		if (Z[i] == 0) continue;
		if (shift[v] == 1) Z[i] = -Z[i];
		R_nz.push(n + i);
		for (int j = 0; j < AH_nz[i]; j++) {
			row[AH[i][j].index()] += Z[i] * AH[i][j].val();
		}
	}

	if (v >= n) {
		row[v] = (shift[v] ? -1 : 1);
		R_nz.push(v);
		int i = v - n;
		for (int j = 0; j < AH_nz[i]; j++) {
			row[AH[i][j].index()] += Z[i] * AH[i][j].val();
		}
	}

	for (int i = 0; i < n; i++) {
		if (ctor[i] >= 0) continue;
		checkZero13(row[i]);
		if (row[i] != 0) R_nz.push(i);
	}

	if (v < n) {
		row[v] = (shift[v] ? -1 : 1);
		R_nz.push(v);
	}
}

bool Simplex::findPivotCol() {
	long double pivot_inc = 1e100;
	pivot_col = -1;

	for (int i = 0; i < R_nz.size(); i++) {
		int k = R_nz[i];
		if ((shift[k] == 0 && row[k] < -pivot_limit) || (shift[k] == 1 && row[k] > pivot_limit)) {
			long double a = -obj[k] / row[k];
			if (a < 0) fprintf(stderr, "%.18Lf %.18Lf\n", obj[k], row[k]);
			assert(a >= 0);
			if (a < pivot_inc) {
				pivot_inc = a;
				pivot_col = k;
			}
		}
	}

	if (SIMPLEX_DEBUG) fprintf(stderr, "Pivot col = %d\n", pivot_col);

	if (pivot_col == -1) return false;
	assert(ctor[pivot_col] == -1);
	return true;
}

// do multiple var flips
bool Simplex::findPivotCol2() {
	pivot_col = -1;

	long double leeway = pr_violation;

	vec<int> pivot_cands;

	for (int i = 0; i < R_nz.size(); i++) {
		int k = R_nz[i];
		if ((shift[k] == 0 && row[k] < 0) || (shift[k] == 1 && row[k] > 0)) {
			assert(ctor[k] == -1);
			pivot_cands.push(k);
			ratio[k] = -obj[k] / row[k];
		}
	}

	if (pivot_cands.size() == 0) return false;

	// sort based on ratio asc, then pivot size asc
	sort((int*)pivot_cands, (int*)pivot_cands + pivot_cands.size(), sort_col_ratio);

	long double best_psize = 0;

	for (int i = 0; i < pivot_cands.size(); i++) {
		int k = pivot_cands[i];
		long double r = (shift[k] ? row[k] : -row[k]);
		if (r > best_psize || (!AVOID_SMALL_PIVOT && r >= 0.001)) {
			best_psize = r;
			pivot_col = k;
		}
		leeway -= r * gap(k);
		if (leeway < 0) break;
	}

	if (SIMPLEX_DEBUG) fprintf(stderr, "Pivot col = %d\n", pivot_col);

	assert(pivot_col != -1);

	if (ctor[pivot_col] != -1) {
		fprintf(stderr, "%d %d %d %d %d %.18Lf %.18Lf\n", shift[pivot_col], pivot_row, rtoc[pivot_row],
						pivot_col, ctor[pivot_col], row[pivot_col], obj[pivot_col]);
	}

	assert(ctor[pivot_col] == -1);

	if (SIMPLEX_DEBUG && best_psize < pivot_limit)
		fprintf(stderr, "Very small pivot %d, %.18Lf\n", pivot_col, best_psize);

	// do bound swap for all vars with smaller ratio than pivot_col
	for (int i = 0; ratio[pivot_cands[i]] < ratio[pivot_col]; i++) {
		//		fprintf(stderr, "Bound swapping %d\n", pivot_cands[i]);
		boundSwap(pivot_cands[i]);
	}

	return true;
}

void Simplex::pivot() {
	assert(ctor[pivot_col] == -1);
	ctor[rtoc[pivot_row]] = -1;
	ctor[pivot_col] = pivot_row;
	rtoc[pivot_row] = pivot_col;

	// update objective row
	long double a = obj[pivot_col] / row[pivot_col];
	for (int i = 0; i < R_nz.size(); i++) {
		int k = R_nz[i];
		obj[k] -= a * row[k];
		checkZero13(obj[k]);
	}

	if (num_lu_factors < REFACTOR_FREQ)
		updateBasis();
	else
		refactorB();

	calcObjBound();

	//	if (simplexs) checkObjective2();
}
