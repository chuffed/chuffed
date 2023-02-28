#ifndef __SORTERS_H__
#define __SORTERS_H__

#include <chuffed/core/propagator.h>

enum SorterKind { SRT_ODDEVEN, SRT_PAIRWISE, SRT_CARDNET, SRT_BDD };
enum SorterFlags { SRT_FULL = 0, SRT_HALF = 1 };

void sorter(int max, vec<Lit>& lits, vec<Lit>& vals, SorterKind kind = SRT_PAIRWISE,
						int flags = SRT_HALF);

struct FullCmp {
	static void cmp(Lit a, Lit b, Lit c, Lit d) {
		// (c <-> a \/ b)
		vec<Lit> cl;
		cl.push(~c);
		cl.push(a);
		cl.push(b);
		sat.addClause(cl);

		sat.addClause(c, ~a);
		sat.addClause(c, ~b);

		// (d <-> a /\ b)
		cl.clear();
		cl.push(d);
		cl.push(~a);
		cl.push(~b);
		sat.addClause(cl);

		sat.addClause(~d, a);
		sat.addClause(~d, b);
	}
};

struct HalfCmp {
	static void cmp(Lit a, Lit b, Lit c, Lit d) {
		// (c <-> a \/ b)
		sat.addClause(c, ~a);
		sat.addClause(c, ~b);

		vec<Lit> cl;
		cl.push(d);
		cl.push(~a);
		cl.push(~b);
		sat.addClause(cl);
	}
};

//==========================
// Pairwise sorting networks
//==========================
// input: as (list of things to be split)
// output: bs (list of higher values), cs (list of lower values)
template <class CMP>
static void PWSplit(vec<Lit>& as, vec<Lit>& bs, vec<Lit>& cs) {
	if (as.size() % 2 == 1) as.push(lit_False);
	assert(as.size() % 2 == 0);

	for (int ii = 0; ii < as.size(); ii += 2) {
		Lit b(Lit(sat.newVar(), 1));
		Lit c(Lit(sat.newVar(), 1));

		CMP::cmp(as[ii], as[ii + 1], b, c);

		bs.push(b);
		cs.push(c);
	}
}

// Same as PWSplit, but pairs 0 with (n/2), etc.
template <class CMP>
static void PWSplit_mid(vec<Lit>& as, vec<Lit>& bs, vec<Lit>& cs) {
	if (as.size() % 2 == 1) as.push(lit_False);
	assert(as.size() % 2 == 0);

	int mid = as.size() / 2;
	for (int ii = 0; ii < mid; ii++) {
		Lit b(Lit(sat.newVar(), 1));
		Lit c(Lit(sat.newVar(), 1));

		CMP::cmp(as[ii], as[mid + ii], b, c);

		bs.push(b);
		cs.push(c);
	}
}

// Merge two sorted lists s.t. \sum_{as} >= \sum_{bs}.
template <class CMP>
static void PWMerge(int max, vec<Lit>& as, vec<Lit>& bs, vec<Lit>& os) {
	assert(as.size() == bs.size());

	if (as.size() == 1) {
		os.push(as[0]);
		os.push(bs[0]);
	} else {
		if (as.size() % 2 == 1) {
			as.push(lit_False);
			bs.push(lit_False);
		}

		vec<Lit> aeven;
		vec<Lit> aodd;
		for (int ii = 0; ii < as.size(); ii += 2) {
			aeven.push(as[ii]);
			aodd.push(as[ii + 1]);
		}

		vec<Lit> beven;
		vec<Lit> bodd;
		for (int ii = 0; ii < bs.size(); ii += 2) {
			beven.push(bs[ii]);
			bodd.push(bs[ii + 1]);
		}
		vec<Lit> ds;
		PWMerge<CMP>(max, aeven, beven, ds);

		vec<Lit> es;
		PWMerge<CMP>(max, aodd, bodd, es);

		os.push(ds[0]);
		for (int ii = 0; ii < as.size() - 1; ii++) {
			Lit oa(Lit(sat.newVar(), 1));
			Lit ob(Lit(sat.newVar(), 1));
			CMP::cmp(es[ii], ds[ii + 1], oa, ob);

			os.push(oa);
			if (os.size() > max) return;

			os.push(ob);
			if (os.size() > max) return;
		}
		os.push(es.last());
	}
}

template <class CMP>
static void PWSort(int max, vec<Lit>& as, vec<Lit>& os) {
	if (as.size() == 0) return;
	if (as.size() == 1) {
		os.push(as[0]);
		return;
	}

	vec<Lit> bs;
	vec<Lit> cs;
	PWSplit<CMP>(as, bs, cs);

	vec<Lit> bsort;
	PWSort<CMP>(max, bs, bsort);

	vec<Lit> csort;
	PWSort<CMP>(max, cs, csort);

	PWMerge<CMP>(max, bsort, csort, os);
}

//=================
// Odd-even Sorters
//=================
// The Odd-even merger described in <Cardinality Networks: a Theoretical and Empirical Study>
// looks very similar to the PWMerge described in the Pairwise-sorter paper, but differs in the
// base case.
template <class CMP>
static void OEMerge(int max, vec<Lit>& as, vec<Lit>& bs, vec<Lit>& os) {
	assert(as.size() == bs.size());

	if (as.size() == 1) {
		Lit oa(Lit(sat.newVar(), 1));
		Lit ob(Lit(sat.newVar(), 1));
		CMP::cmp(as[0], bs[0], oa, ob);

		os.push(oa);
		os.push(ob);
	} else {
		if (as.size() % 2 != 0) {
			as.push(lit_False);
			bs.push(lit_False);
		}
		vec<Lit> aeven;
		vec<Lit> aodd;
		for (int ii = 0; ii < as.size(); ii += 2) {
			aeven.push(as[ii]);
			aodd.push(as[ii + 1]);
		}

		vec<Lit> beven;
		vec<Lit> bodd;
		for (int ii = 0; ii < bs.size(); ii += 2) {
			beven.push(bs[ii]);
			bodd.push(bs[ii + 1]);
		}
		vec<Lit> ds;
		OEMerge<CMP>(max, aeven, beven, ds);

		vec<Lit> es;
		OEMerge<CMP>(max, aodd, bodd, es);

		os.push(ds[0]);
		for (int ii = 0; ii < as.size() - 1; ii++) {
			Lit oa(Lit(sat.newVar(), 1));
			Lit ob(Lit(sat.newVar(), 1));
			CMP::cmp(es[ii], ds[ii + 1], oa, ob);

			os.push(oa);
			if (os.size() > max) return;

			os.push(ob);

			if (os.size() > max) return;
		}
		os.push(es.last());
	}
}

template <class CMP>
static void OESort(int max, vec<Lit>& as, vec<Lit>& os) {
	if (as.size() == 0) return;
	if (as.size() == 1) {
		os.push(as[0]);
		return;
	}

	if (as.size() % 2) as.push(lit_False);

	// as is of even length.
	vec<Lit> bs;
	vec<Lit> cs;
	for (int ii = 0; ii < as.size(); ii += 2) {
		bs.push(as[ii]);
		cs.push(as[ii + 1]);
	}

	vec<Lit> bsort;
	OESort<CMP>(max, bs, bsort);

	vec<Lit> csort;
	OESort<CMP>(max, cs, csort);

	OEMerge<CMP>(max, bsort, csort, os);
}

//==================
// BDD-based sorters
//==================
// Not yet implemented.

//=====================
// Cardinality networks
//=====================
template <class CMP>
static void CardNet(int max, vec<Lit>& as, vec<Lit>& os) {
	if (as.size() <= 2 * (max + 1)) {
		// Sort a single chunk of size <max>, plus (possibly) some leftover.
		OESort<CMP>(max, as, os);
	} else {
		vec<Lit> left;
		vec<Lit> right;

		vec<Lit> oleft;
		vec<Lit> oright;
		for (int ii = 0; ii < max + 1; ii++) {
			left.push(as[ii]);
		}
		for (int ii = max + 1; ii < as.size(); ii++) {
			right.push(as[ii]);
		}

		CardNet<CMP>(max, left, oleft);
		CardNet<CMP>(max, right, oright);
		if (oleft.size() != oright.size()) {
			printf("%d -- %d\n", oleft.size(), oright.size());
		}

		assert(oleft.size() == oright.size());

		// Merge the two sides
		OEMerge<CMP>(max, oleft, oright, os);
	}
}

// input: max (ub), lits (input literals)
// output: vals (fresh literals representing the sorter outputs)
inline void sorter(int max, vec<Lit>& lits, vec<Lit>& vals, SorterKind kind, int flags) {
	if (flags & SRT_HALF) {
		switch (kind) {
			case SRT_PAIRWISE:
				PWSort<HalfCmp>(max, lits, vals);
				break;

			case SRT_ODDEVEN:
				OESort<HalfCmp>(max, lits, vals);
				break;

			case SRT_CARDNET:
				CardNet<HalfCmp>(max, lits, vals);
				break;
			case SRT_BDD:
				NOT_SUPPORTED;
				break;
			default:
				NEVER;
				break;
		}
	} else {
		switch (kind) {
			case SRT_PAIRWISE:
				PWSort<FullCmp>(max, lits, vals);
				break;

			case SRT_ODDEVEN:
				OESort<FullCmp>(max, lits, vals);
				break;

			case SRT_CARDNET:
				CardNet<FullCmp>(max, lits, vals);
				break;
			case SRT_BDD:
				NOT_SUPPORTED;
				break;
			default:
				NEVER;
				break;
		}
	}
	return;
}

#endif
