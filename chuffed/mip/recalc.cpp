#include "chuffed/mip/simplex.h"
#include "chuffed/support/vec.h"

#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdio>
#include <cstring>

void LUFactor::multiply(long double* a) {
	for (int i = 0; i < vals.size(); i++) {
		a[r] += a[vals[i].index()] * vals[i].val();
	}
}

void LUFactor::Tmultiply(long double* a) {
	if (a[r] != 0) {
		for (int i = 0; i < vals.size(); i++) {
			a[vals[i].index()] += vals[i].val() * a[r];
		}
	}
}

void Simplex::Lmultiply(long double* a) {
	for (int i = L_cols_zeros; i < m; i++) {
		tm[i] = 0;
	}
	for (int i = L_cols_zeros; i < m; i++) {
		if (a[i] != 0) {
			for (int j = 0; j < L_cols[i].size(); j++) {
				tm[L_cols[i][j].index()] += a[i] * L_cols[i][j].val();
			}
		}
		a[i] += tm[i];
		checkZero13(a[i]);
	}
}

void Simplex::LTmultiply(long double* a) {
	for (int i = L_cols_zeros; i < m; i++) {
		tm[i] = 0;
	}
	for (int i = m - 1; i >= L_cols_zeros; i--) {
		if (a[i] != 0) {
			for (int j = 0; j < L_rows[i].size(); j++) {
				tm[L_rows[i][j].index()] += a[i] * L_rows[i][j].val();
			}
		}
		a[i] += tm[i];
		checkZero13(a[i]);
	}
}

void Simplex::Umultiply(long double* a) {
	for (int k = m - 1; k >= U_diag_units; k--) {
		const int i = U_perm[k];
		checkZero13(a[i]);
		if (a[i] == 0) {
			continue;
		}
		a[i] /= U_diag[i];
		for (int j = 0; j < U_cols[i].size(); j++) {
			a[U_cols[i][j].index()] -= a[i] * U_cols[i][j].val();
		}
	}
}

void Simplex::UTmultiply(long double* a) {
	for (int k = 0; k < m; k++) {
		const int i = U_perm[k];
		checkZero13(a[i]);
		if (a[i] == 0) {
			continue;
		}
		a[i] /= U_diag[i];
		for (int j = 0; j < U_rows[i].size(); j++) {
			a[U_rows[i][j].index()] -= a[i] * U_rows[i][j].val();
		}
	}
}

void Simplex::Bmultiply(long double* a) {
	Lmultiply(a);
	for (int i = 0; i < num_lu_factors; i++) {
		lu_factors[i].multiply(a);
	}
	Umultiply(a);
}

void Simplex::calcBInvRow(long double* a, int r) {
	memset(a, 0, m * sizeof(long double));
	a[r] = 1;
	UTmultiply(a);
	for (int i = num_lu_factors; (i--) != 0;) {
		lu_factors[i].Tmultiply(a);
	}
	LTmultiply(a);
}

void Simplex::calcRHS() {
	for (int i = 0; i < m; i++) {
		rhs[i] = BC[i];
	}
	Bmultiply(rhs);
}

void Simplex::calcObjective() {
	calcBInvRow(&obj[n], ctor[0]);
	for (int i = 0; i < m; i++) {
		obj[n + i] = -obj[n + i];
		checkZero13(obj[n + i]);
	}
	for (int i = 0; i < n; i++) {
		obj[i] = 0;
		for (int j = 0; j < AV_nz[i]; j++) {
			obj[i] += obj[n + AV[i][j].index()] * AV[i][j].val();
		}
		checkZero13(obj[i]);
	}
	obj[0] += 1;
	checkZero13(obj[0]);

	for (int i = 0; i < n + m; i++) {
		if ((shift[i] == 0 && obj[i] < 0) || (shift[i] == 1 && obj[i] > 0)) {
			boundSwap(i);
		}
	}
}

void Simplex::calcObjBound() {
	obj_bound = 0;
	for (int i = 0; i < m; i++) {
		obj_bound += obj[n + i] * BC[i];
	}
}

void Simplex::updateBasis() {
	// find new column
	memset(column, 0, m * sizeof(long double));
	for (int i = 0; i < AV_nz[pivot_col]; i++) {
		column[AV[pivot_col][i].index()] = AV[pivot_col][i].val();
	}
	Lmultiply(column);
	for (int i = 0; i < num_lu_factors; i++) {
		lu_factors[i].multiply(column);
	}

	if (STEEPEST_EDGE) {
		// calc Y
		for (int i = 0; i < m; i++) {
			Y[i] = column[i];
		}
		Umultiply(Y);

		// calculate BZ
		if (shift[rtoc[pivot_row]] == 0) {
			for (int i = 0; i < m; i++) {
				BZ[i] = Z[i];
			}
		} else {
			for (int i = 0; i < m; i++) {
				BZ[i] = -Z[i];
			}
		}
		Bmultiply(BZ);

		updateNorms();
	}

	const int r = pivot_row;  // column which is being replaced

	//	fprintf(stderr, "r = %d\n", r);

	// get rth row in dense form
	memset(tm, 0, m * sizeof(long double));
	for (int i = 0; i < U_rows[r].size(); i++) {
		tm[U_rows[r][i].index()] = U_rows[r][i].val();
	}

	LUFactor& f = lu_factors[num_lu_factors++];
	f.r = r;
	f.vals.clear();

	int inv_r = 0;
	while (U_perm[inv_r] != r) {
		inv_r++;
	}

	//	fprintf(stderr, "%d %d, ", inv_r, last_nz);

	// clear rth row
	for (int k = inv_r + 1; k < m; k++) {
		const int i = U_perm[k];
		checkZero13(tm[i]);
		if (tm[i] == 0) {
			continue;
		}
		const long double a = -tm[i] / U_diag[i];
		f.vals.push(IndexVal(i, a));
		for (int j = 0; j < U_rows[i].size(); j++) {
			tm[U_rows[i][j].index()] += a * U_rows[i][j].val();
		}
	}

	// transform new column
	f.multiply(column);

	if (f.vals.size() == 0) {
		num_lu_factors--;
	}

	// update U perm
	for (int i = inv_r; i < m - 1; i++) {
		U_perm[i] = U_perm[i + 1];
	}
	U_perm[m - 1] = r;

	if (inv_r < U_diag_units) {
		U_diag_units--;
	}

	//	fprintf(stderr, "column: ");
	//	for (int i = 0; i < m; i++) fprintf(stderr, "%.3Lf ", column[i]);
	//	fprintf(stderr, "\n");

	//	fprintf(stderr, "new column: ");
	//	for (int i = 0; i < m; i++) fprintf(stderr, "%.3Lf ", column[i]);
	//	fprintf(stderr, "\n");

	// update U_col for i != r

	for (int i = 0; i < U_rows[r].size(); i++) {
		vec<IndexVal>& col = U_cols[U_rows[r][i].index()];
		for (int j = 0; j < col.size(); j++) {
			//		for (int j = col.size(); j--; ) {
			if (col[j].index() == r) {
				col[j] = col.last();
				col.pop();
				break;
			}
		}
	}

	// update U_row

	U_rows[r].clear();

	//	int type[m];
	int* type = new int[m];

	for (int i = 0; i < m; i++) {
		checkZero13(column[i]);
		type[i] = ((column[i] != 0 && i != r) ? 1 : 0);
	}

	for (int i = 0; i < U_cols[r].size(); i++) {
		type[U_cols[r][i].index()] += 2;
	}
	U_cols[r].clear();

	for (int i = 0; i < m; i++) {
		if (column[i] != 0 && i != r) {
			U_cols[r].push(IndexVal(i, column[i]));
		}
	}

	for (int i = 0; i < m; i++) {
		if (type[i] == 0) {
			continue;
		}
		vec<IndexVal>& row = U_rows[i];
		if (type[i] == 1) {
			// add new element to U_rows[i]
			row.push(IndexVal(r, column[i]));
		}
		if (type[i] == 2) {
			// remove element from U_rows[i]
			for (int j = 0; j < row.size(); j++) {
				if (row[j].index() == r) {
					row[j] = row.last();
					row.pop();
					break;
				}
			}
		}
		if (type[i] == 3) {
			// change element in U_rows[i]
			for (int j = 0; j < row.size(); j++) {
				if (row[j].index() == r) {
					row[j].val() = column[i];
					break;
				}
			}
		}
	}

	U_diag[r] = column[r];
	assert(U_diag[r] != 0);
	if (SIMPLEX_DEBUG && -0.0001 < U_diag[r] && U_diag[r] < 0.0001) {
		fprintf(stderr, "Very small diag %d, %.18Lf\n", r, U_diag[r]);
	}
	delete[] type;
}

void Simplex::updateNorms() const {
	const long double Z_norm2 = BZ[pivot_row];

	assert(Y[pivot_row] != 0);
	for (int i = 0; i < m; i++) {
		if (i == pivot_row) {
			norm2[pivot_row] /= Y[pivot_row] * Y[pivot_row];
		} else {
			checkZero13(Y[i]);
			if (Y[i] == 0) {
				continue;
			}
			const long double y_ratio = Y[i] / Y[pivot_row];
			norm2[i] += -2 * y_ratio * BZ[i] + y_ratio * y_ratio * Z_norm2;
		}
		//		fprintf(stderr, "%d:%.3Lf ", i, norm2[i]);
		if (norm2[i] < 1) {
			norm2[i] = 1;
		}
		//		assert(norm2[i] > 0);
	}
	//	fprintf(stderr, "\n");
}

void Simplex::refactorB() {
	//	fprintf(stderr, "Refactor!!!\n");

	refactors++;

	//	int col_perm[m], col_perm2[m], row_perm[m], row_perm2[m];
	int* col_perm = new int[m];
	int* col_perm2 = new int[m];
	int* row_perm = new int[m];
	int* row_perm2 = new int[m];

	for (int i = 0; i < m; i++) {
		U_perm[i] = i;
		row_perm[i] = -1;
		norm2[i] = 1;
		U_rows[i].clear();
		U_cols[i].clear();
		L_rows[i].clear();
		L_cols[i].clear();
	}

	// find singleton columns

	int cs = 0;
	vec<int> non_col_sing;
	for (int i = 0; i < m; i++) {
		const int c = rtoc[i];
		if (AV_nz[c] == 1) {
			col_perm[i] = cs;
			const int k = AV[c][0].index();
			row_perm[k] = cs;
			row_perm2[cs] = cs;
			U_diag[cs] = AV[c][0].val();
			cs++;
		} else {
			non_col_sing.push(rtoc[i]);
		}
	}

	for (int i = 0; i < non_col_sing.size(); i++) {
		col_perm2[cs + i] = non_col_sing[i];
	}

	std::sort(col_perm2 + cs, col_perm2 + m, sort_col_nz);

	for (int i = cs; i < m; i++) {
		row_perm2[i] = -1;
		col_perm[ctor[col_perm2[i]]] = i;
	}

	// Do col perms
	//	int old_rtoc[m];
	int* old_rtoc = new int[m];
	for (int i = 0; i < m; i++) {
		old_rtoc[i] = rtoc[i];
	}
	for (int i = 0; i < m; i++) {
		rtoc[col_perm[i]] = old_rtoc[i];
		ctor[old_rtoc[i]] = col_perm[i];
	}

	// Initialise R1, R2 (for storing U and L)
	const int p = m - cs;
	for (int i = 1; i < p; i++) {
		R1[i] = R1[0] + static_cast<ptrdiff_t>(i * p);
		R2[i] = R2[0] + static_cast<ptrdiff_t>(i * p);
	}
	memset(R1[0], 0, sizeof(R1[0][0]) * p * p);
	memset(R2[0], 0, sizeof(R2[0][0]) * p * p);

	int rows_used = cs;
	for (int i = cs; i < m; i++) {
		const int c = col_perm2[i];
		for (int j = 0; j < AV_nz[c]; j++) {
			const int k = AV[c][j].index();
			int& r = row_perm[k];
			if (r == -1) {
				r = rows_used++;
			}
			if (r < cs) {
				U_rows[r].push(IndexVal(i, AV[c][j].val()));
				U_cols[i].push(IndexVal(r, AV[c][j].val()));
			} else {
				R1[r - cs][i - cs] = AV[c][j].val();
			}
		}
	}

	//	fprintf(stderr, "R:\n");
	//	for (int i = 0; i < m; i++) {
	//		fprintf(stderr, "row %d: ", i);
	//		for (int j = 0; j < m; j++) fprintf(stderr, "%d:%.3Lf ", j, R[i][j]);
	//		fprintf(stderr, "\n");
	//	}

	// calculate U and L
	for (int i = 0; i < p; i++) {
		int nr = -1;
		for (int j = 0; j < p; j++) {
			checkZero13(R1[j][i]);
			if (R1[j][i] != 0 && row_perm2[j + cs] == -1) {
				nr = j;
				break;
			}
		}
		assert(nr != -1);
		assert(R1[nr][i] != 0);
		row_perm2[nr + cs] = i + cs;
		U_diag[i + cs] = R1[nr][i];
		if (SIMPLEX_DEBUG && -0.0001 < U_diag[i + cs] && U_diag[i + cs] < 0.0001) {
			fprintf(stderr, "Very small diag %d, %.18Lf\n", i + cs, U_diag[i + cs]);
		}
		for (int j = i + 1; j < p; j++) {
			checkZero13(R1[nr][j]);
			if (R1[nr][j] != 0) {
				U_rows[i + cs].push(IndexVal(j + cs, R1[nr][j]));
				U_cols[j + cs].push(IndexVal(i + cs, R1[nr][j]));
			}
		}
		for (int j = 0; j < i; j++) {
			checkZero13(R2[nr][j]);
			if (R2[nr][j] != 0) {
				L_rows[i + cs].push(IndexVal(j + cs, R2[nr][j]));
				L_cols[j + cs].push(IndexVal(i + cs, R2[nr][j]));
			}
		}
		for (int j = 0; j < p; j++) {
			checkZero13(R1[j][i]);
			if (R1[j][i] == 0 || row_perm2[j + cs] >= 0) {
				continue;
			}
			const long double a = -R1[j][i] / R1[nr][i];
			for (int k = 0; k < U_rows[i + cs].size(); k++) {
				R1[j][U_rows[i + cs][k].index() - cs] += a * U_rows[i + cs][k].val();
			}
			for (int k = 0; k < L_rows[i + cs].size(); k++) {
				R2[j][L_rows[i + cs][k].index() - cs] += a * L_rows[i + cs][k].val();
			}
			R2[j][i] += a * 1;
		}
	}

	L_cols_zeros = cs;
	while (L_cols_zeros < m && L_cols[L_cols_zeros].size() == 0) {
		L_cols_zeros++;
	}

	U_diag_units = 0;
	while (U_diag_units < cs && U_diag[U_diag_units] == 1) {
		U_diag_units++;
	}

	//	fprintf(stderr, "R:\n");
	//	for (int i = 0; i < m; i++) {
	//		fprintf(stderr, "row %d: ", i);
	//		for (int j = 0; j < m; j++) fprintf(stderr, "%d:%.3Lf ", j, R[i][j]);
	//		fprintf(stderr, "\n");
	//	}

	for (int i = 0; i < m; i++) {
		row_perm[i] = row_perm2[row_perm[i]];
	}

	// Do row perms

	/* IndexVal *old_AH[m]; */
	/* int old_AH_nz[m]; */
	/* int old_BC[m]; */
	/* int old_lb[m]; */
	/* int old_ub[m]; */
	/* int old_shift[m]; */
	/* int old_ctor[m]; */

	auto** old_AH = new IndexVal*[m];
	int* old_AH_nz = new int[m];
	int* old_BC = new int[m];
	int* old_lb = new int[m];
	int* old_ub = new int[m];
	int* old_shift = new int[m];
	int* old_ctor = new int[m];
	// slack var i -> slack var row_perm[i]

	for (int i = 0; i < m; i++) {
		old_AH[i] = AH[i];
		old_AH_nz[i] = AH_nz[i];
		old_BC[i] = BC[i];
		old_lb[i] = lb[n + i];
		old_ub[i] = ub[n + i];
		old_shift[i] = shift[n + i];
		old_ctor[i] = ctor[n + i];
	}

	for (int i = 0; i < m; i++) {
		AH[row_perm[i]] = old_AH[i];
		AH_nz[row_perm[i]] = old_AH_nz[i];
		BC[row_perm[i]] = old_BC[i];
		lb[n + row_perm[i]].v = old_lb[i];
		ub[n + row_perm[i]].v = old_ub[i];
		shift[n + row_perm[i]] = old_shift[i];
		ctor[n + row_perm[i]] = old_ctor[i];
		if (old_ctor[i] >= 0) {
			rtoc[old_ctor[i]] = n + row_perm[i];
		}
	}

	for (int i = 0; i < A_size; i++) {
		AV_mem[i].index() = row_perm[AV_mem[i].index()];
	}

	num_lu_factors = 0;

	if (simplexs > 0) {
		calcObjective();
	}

	delete[] col_perm;
	delete[] col_perm2;
	delete[] row_perm;
	delete[] row_perm2;
	delete[] old_rtoc;
	delete[] old_AH;
	delete[] old_AH_nz;
	delete[] old_BC;
	delete[] old_lb;
	delete[] old_ub;
	delete[] old_shift;
	delete[] old_ctor;

	//	printB();
}

void Simplex::saveState(SimplexState& s) const {
	if (s.rtoc == nullptr) {
		s.rtoc = new int[m];
	}
	if (s.ctor == nullptr) {
		s.ctor = new int[n + m];
	}
	if (s.shift == nullptr) {
		s.shift = new int[n + m + 1];
	}

	for (int i = 0; i < m; i++) {
		s.rtoc[i] = rtoc[i];
	}
	for (int i = 0; i < n + m; i++) {
		s.ctor[i] = ctor[i];
	}
	for (int i = 0; i < n + m + 1; i++) {
		s.shift[i] = shift[i];
	}

	//	fprintf(stderr, "Saving state:\n");
	//	printTableau(true);
}

void Simplex::loadState(SimplexState& s) const {
	for (int i = 0; i < m; i++) {
		rtoc[i] = s.rtoc[i];
	}
	for (int i = 0; i < n + m; i++) {
		ctor[i] = s.ctor[i];
	}
	for (int i = 0; i < n + m + 1; i++) {
		shift[i] = s.shift[i];
	}

	//	fprintf(stderr, "loading state:\n");
	//	printTableau(true);
}

//-----
// Debug methods

void Simplex::printObjective() const {
	fprintf(stderr, "objective: ");
	for (int i = 0; i < n + m; i++) {
		fprintf(stderr, "%d:%.18Lf ", i, obj[i]);
	}
	fprintf(stderr, "\n");
	fprintf(stderr, "obj_bound = %.3Lf\n", obj_bound);
	fflush(stderr);
}

void Simplex::printTableau(bool full) {
	calcRHS();
	//	long double row[n+m];
	auto* row = new long double[n + m];
	fprintf(stderr, "Tableau:\n");
	for (int i = 0; i < n + m; i++) {
		fprintf(stderr, "%d:%d ", i, shift[i]);
	}
	fprintf(stderr, "\n");
	for (int i = 0; i < m; i++) {
		calcBInvRow(&row[n], i);
		for (int j = 0; j < n; j++) {
			row[j] = 0;
			for (int k = 0; k < AV_nz[j]; k++) {
				row[j] += row[n + AV[j][k].index()] * AV[j][k].val();
			}
		}
		fprintf(stderr, "%d: ", rtoc[i]);
		if (full) {
			for (int j = 0; j < n + m; j++) {
				fprintf(stderr, "%d:%.3Lf ", j, row[j]);
			}
		}
		fprintf(stderr, "rhs:%.18Lf", rhs[i]);
		fprintf(stderr, "\n");
		//		row[rtoc[i]] -= 1;
		//		for (int j = 0; j < m; j++) {
		//			if (!almostZero6(row[rtoc[j]])) fprintf(stderr, "%d:%d:%.2Lf ", i, j, row[rtoc[j]]);
		//			assert(almostZero6(row[rtoc[j]]));
		//		}
	}
	printObjective();
	fflush(stderr);

	//	long double T[n+m][m];
	auto** T = new long double*[n + m];
	for (int i = 0; i < n + m; i++) {
		T[i] = new long double[m];
	}
	for (int i = 0; i < n + m; i++) {
		for (int j = 0; j < m; j++) {
			T[i][j] = 0;
		}
		for (int j = 0; j < AV_nz[i]; j++) {
			T[i][AV[i][j].index()] = AV[i][j].val();
		}
		Bmultiply(T[i]);
	}

	for (int i = 0; i < m; i++) {
		fprintf(stderr, "%d: ", rtoc[i]);
		for (int j = 0; j < n + m; j++) {
			fprintf(stderr, "%d:%.3Lf ", j, T[j][i]);
		}
		fprintf(stderr, "\n");
	}

	delete[] row;
	for (int i = 0; i < n + m; i++) {
		delete T[i];
	}
	delete[] T;
}

void Simplex::printL() {
	fprintf(stderr, "L:\n");
	for (int i = 0; i < m; i++) {
		if (L_rows[i].size() != 0) {
			fprintf(stderr, "row %d: ", i);
		}
		for (int j = 0; j < L_rows[i].size(); j++) {
			fprintf(stderr, "%d:%.3Lf ", L_rows[i][j].index(), L_rows[i][j].val());
		}
		if (L_rows[i].size() != 0) {
			fprintf(stderr, "\n");
		}
	}
	for (int i = 0; i < m; i++) {
		if (L_cols[i].size() != 0) {
			fprintf(stderr, "col %d: ", i);
		}
		for (int j = 0; j < L_cols[i].size(); j++) {
			fprintf(stderr, "%d:%.3Lf ", L_cols[i][j].index(), L_cols[i][j].val());
		}
		if (L_cols[i].size() != 0) {
			fprintf(stderr, "\n");
		}
	}
}

void Simplex::printU() {
	fprintf(stderr, "U:\n");
	for (int i = 0; i < m; i++) {
		if (U_rows[i].size() != 0) {
			fprintf(stderr, "row %d: ", i);
		}
		for (int j = 0; j < U_rows[i].size(); j++) {
			fprintf(stderr, "%d:%.3Lf ", U_rows[i][j].index(), U_rows[i][j].val());
		}
		if (U_rows[i].size() != 0) {
			fprintf(stderr, "\n");
		}
	}
	for (int i = 0; i < m; i++) {
		if (U_cols[i].size() != 0) {
			fprintf(stderr, "col %d: ", i);
		}
		for (int j = 0; j < U_cols[i].size(); j++) {
			fprintf(stderr, "%d:%.3Lf ", U_cols[i][j].index(), U_cols[i][j].val());
		}
		if (U_cols[i].size() != 0) {
			fprintf(stderr, "\n");
		}
	}
	fprintf(stderr, "diag: ");
	for (int i = 0; i < m; i++) {
		fprintf(stderr, "%d:%.3Lf ", i, U_diag[i]);
	}
	fprintf(stderr, "\n");
}

void Simplex::printLUF() const {
	for (int i = 0; i < num_lu_factors; i++) {
		LUFactor& f = lu_factors[i];
		fprintf(stderr, "r = %d: ", f.r);
		for (int j = 0; j < f.vals.size(); j++) {
			fprintf(stderr, "%d:%.3Lf ", f.vals[j].index(), f.vals[j].val());
		}
		fprintf(stderr, "\n");
	}
}

void Simplex::printB() {
	printL();
	printLUF();
	printU();
	fprintf(stderr, "U_perm: ");
	for (int i = 0; i < m; i++) {
		fprintf(stderr, "%d ", U_perm[i]);
	}
	fprintf(stderr, "\n");
}

void Simplex::printRHS() const {
	fprintf(stderr, "RHS:\n");
	for (int i = 0; i < m; i++) {
		fprintf(stderr, "%.3Lf ", rhs[i]);
	}
	fprintf(stderr, "\n");
}

void Simplex::checkObjective() const {
	for (int i = 0; i < n + m; i++) {
		if (shift[i] == 0) {
			if (obj[i] < 0) {
				fprintf(stderr, "%d %d %.18Lf %lld\n", i, shift[i], obj[i], simplexs);
			}
			assert(obj[i] >= 0);
		} else {
			if (obj[i] > 0) {
				fprintf(stderr, "%d %d %.18Lf %lld\n", i, shift[i], obj[i], simplexs);
			}
			assert(obj[i] <= 0);
		}
	}
}

void Simplex::checkBasis() {
	//	printTableau(true);
	fprintf(stderr, "Check basis:\n");
	//	long double temp[m];
	auto* temp = new long double[m];
	for (int i = 0; i < m; i++) {
		calcBInvRow(temp, i);
		for (int j = 0; j < m; j++) {
			long double sum = 0;
			for (int k = 0; k < AV_nz[rtoc[j]]; k++) {
				sum += temp[AV[rtoc[j]][k].index()] * AV[rtoc[j]][k].val();
			}
			if (i == j) {
				sum -= 1;
			}
			if (!almostZero6(sum)) {
				fprintf(stderr, "%d:%d:%.2Lf ", i, j, sum);
			}
			assert(almostZero6(sum));
		}
		//		fprintf(stderr, "\n");
	}
	delete[] temp;
}

void Simplex::unboundedDebug() const {
	fprintf(stderr, "Unbounded:\n");
	printObjective();
	//		printTableau(true);
	fprintf(stderr, "Pivot row = %d\n", pivot_row);
	fprintf(stderr, "RHS = %.3Lf\n", rhs[pivot_row]);
	fprintf(stderr, "Row: ");
	for (int i = 0; i < n + m; i++) {
		if (row[i] == 0) {
			continue;
		}
		fprintf(stderr, "%d:", i);
		fprintf(stderr, "%.3Lf/%.3Lf, ", obj[i], row[i]);
	}
	for (int i = 0; i < n; i++) {
		fprintf(stderr, "%d:%d %d, ", i, (int)lb[i], (int)ub[i]);
	}
}
