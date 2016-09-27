#ifndef __MDDGLOBALS_H__
#define __MDDGLOBALS_H__
#include <chuffed/core/propagator.h>
#include <chuffed/mdd/MDD.h>
#include <chuffed/mdd/opts.h>

void mdd_table(vec<IntVar*>& x, vec<vec<int> >& t, const MDDOpts& mopts);

void mdd_regular(vec<IntVar*>& x, int q, int s, vec<vec<int> >& d, int q0, vec<int>& f, bool offset, const MDDOpts& mopts);
// GKG: FIXME
_MDD fd_regular(MDDTable& tab, int n, int nstates, vec< vec<int> >& transition, int q0, vec<int>& accepts, bool offset = true);
void wmdd_cost_regular(vec<IntVar*>& x, int q, int s, vec<vec<int> >& d, vec<vec<int> >& w,
    int q0, vec<int>& f, IntVar* cost, const MDDOpts& mopts);

void addMDD(vec<IntVar*>& xs, MDD r, const MDDOpts& mopts);
#endif
