#ifndef ldsb_h
#define ldsb_h

#include "chuffed/support/misc.h"

#include <utility>

class Clause;
class IntVar;
class Lit;
class lbool;
class Symmetry;

class LDSB {
public:
	vec<Symmetry*> symmetries;
	vec<vec<std::pair<int, int> > >
			lookupTable;  // lookup by var_id, which symmetries it is in and what pos in that symmetry

	vec<Clause*> sym_learnts;  // List of symmetric learnt clauses
	vec<int> sl_origin;        // Source of new learnt clause

	duration ldsb_time;

	void init();
	void processDec(Lit p);
	bool processImpl(Clause* c);
	void addLearntClause(Clause& c, int sym_id);
};

void var_sym_ldsb(vec<IntVar*>& x);
void val_sym_ldsb(vec<IntVar*>& x, int l, int u);
void var_seq_sym_ldsb(int n, int m, vec<IntVar*>& x);
void val_seq_sym_ldsb(int n, int m, vec<IntVar*>& x, vec<int>& a);

extern LDSB ldsb;

#endif
