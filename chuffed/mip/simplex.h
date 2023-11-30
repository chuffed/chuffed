#ifndef simplex_h
#define simplex_h

#include "chuffed/core/engine.h"

#define SIMPLEX_DEBUG 0
#define RECALC_DEBUG 0
#define EARLY_TERM 0
#define STEEPEST_EDGE 1

enum SimplexStatus { SIMPLEX_OPTIMAL, SIMPLEX_GOOD_ENOUGH, SIMPLEX_IN_PROGRESS, SIMPLEX_UNBOUNDED };

class SimplexState {
public:
	int* rtoc{nullptr};
	int* ctor{nullptr};
	int* shift{nullptr};
	SimplexState() = default;
};

class IndexVal {
public:
	union {
		long double v;
		int i[4];
	};
	IndexVal() {}
	IndexVal(int _i, long double _v) {
		v = _v;
		i[3] = _i;
	}
	long double& val() { return v; }
	int& index() { return i[3]; }
};

// class to store special form matrices spawned during LU update
// add diagonal entries are 1 and a single row r has non-zero entries
class LUFactor {
public:
	int r;               // row which has non-zero entries
	vec<IndexVal> vals;  // values in rth row
	LUFactor() = default;
	void multiply(long double* a);
	void Tmultiply(long double* a);
};

#define bound_weaken (1e-3)
#define obj_limit (1e-3)
#define pivot_limit (1e-3)

class Simplex {
	//	static const long double bound_weaken = 1e-3;          // bound given by simplex is weakened
	// by this much 	static const long double obj_limit    = 1e-3;          // minimum violation of
	// RHS before pivoting row 	static const long double pivot_limit  = 1e-3;          // minimum size
	// of pivot (otherwise, small ignore dual infeasibility)

public:
	int n;       // number of variables
	int m;       // number of constraints
	int A_size;  // number of coefficients

	IndexVal** AH;     // original constraints horizontally
	IndexVal** AV;     // original constraints vertically
	IndexVal* AH_mem;  // memory for AH
	IndexVal* AV_mem;  // memory for AV
	int* AH_nz;        // number of non-zeros in AH
	int* AV_nz;        // number of non-zeros in AV

	long double* Z;    // pivot row of B^-1
	long double* Y;    // pivot column
	long double* BZ;   // B^-1 . Z
	long double* obj;  // objective function
	long double* rhs;  // right hand side of constraints
	long double** R1;  // memory for refactorising B
	long double** R2;  // memory for refactorising B
	long double* tm;   // temp memory for various things
	int* BC;           // values of linear expressions at current bounds
	long double obj_bound;

	float* norm2;  // norm^2 of ith row of M
	double* reduced_costs;

	vec<vec<IndexVal> > L_cols;
	vec<vec<IndexVal> > L_rows;
	vec<vec<IndexVal> > U_cols;
	vec<vec<IndexVal> > U_rows;
	long double* U_diag;
	int* U_perm;          // U' -> U where U' is upper triangular
	int L_cols_zeros{0};  // number of empty columns from start
	int U_diag_units{0};  // number of unit U_diag from start

	LUFactor* lu_factors;
	int num_lu_factors;

	Tint* lb;
	Tint* ub;

	vec<int> R_nz;  // non-zero elements of pivot row

	int* rtoc;   // row to var
	int* ctor;   // var to row, -1 if non-basic
	int* shift;  // whether we're using upper or lower bound offset

	int pivot_col;
	int pivot_row;
	long double pr_violation;

	long double* row;
	long double* column;
	long double* ratio;

	SimplexState root;

	long double recalc_time{0};
	long long simplexs{0};
	long long refactors{0};

	struct SortColRatio {
		long double*& ratio;
		bool operator()(int i, int j) const { return (ratio[i] < ratio[j]); }
		SortColRatio(long double*& r) : ratio(r) {}
	} sort_col_ratio;

	struct SortColNz {
		int*& nz;
		bool operator()(int i, int j) const { return (nz[i] < nz[j]); }
		SortColNz(int*& _nz) : nz(_nz) {}
	} sort_col_nz;

	Simplex();

	// Simplex methods

	void init();
	void pivotObjVar();
	void boundChange(int v, int d) const;
	void boundSwap(int v) const;
	int simplex();
	bool findPivotRow();
	void regeneratePivotRow();
	bool findPivotCol();
	bool findPivotCol2();
	void pivot();

	// Recalculation methods

	void Lmultiply(long double* a);
	void LTmultiply(long double* a);
	void Umultiply(long double* a);
	void UTmultiply(long double* a);
	void Bmultiply(long double* a);
	void calcRHS();
	void calcObjective();
	void calcObjBound();
	void calcBInvRow(long double* a, int r);
	void updateBasis();
	void updateNorms() const;
	void refactorB();

	void saveState(SimplexState& s) const;
	void loadState(SimplexState& s) const;

	// Debug methods

	void printObjective() const;
	void printTableau(bool full = false);
	void printL();
	void printU();
	void printLUF() const;
	void printB();
	void printRHS() const;

	void checkObjective() const;
	void checkBasis();
	void unboundedDebug() const;

	// inline methods

	static void checkZero13(long double& a);
	static bool almostZero6(long double a);
	long double optimum() const;
	int gap(int i) const;
};

extern Simplex simplex;

inline void Simplex::checkZero13(long double& a) {
	//	if ((((int*) &a)[2] & 0x7fff) <= 16339)           // 16382 + log_2(precision)
	if (-1e-13 < a && a < 1e-13) {
		a = 0;
	}
}

inline bool Simplex::almostZero6(long double a) { return (-0.000001 < a && a < 0.000001); }

inline long double Simplex::optimum() const { return -obj_bound - bound_weaken; }
inline int Simplex::gap(int i) const { return ub[i] - lb[i]; }

#endif
