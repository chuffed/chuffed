#ifndef assume_h
#define assume_h
#include <chuffed/support/misc.h>
#include <chuffed/core/sat-types.h>
#include <chuffed/core/sat.h>

// Helper for pushing a failure back to externally visible literals.
template<class P>
void pushback_reason(const P& is_extractable, Lit p, vec<Lit>& out_nogood) {
  assert(sat.value(p) == l_False);
  out_nogood.push(~p);

  // TODO: Take literal subsumption into account.
  // Even though we can't _export_ integer bounds, we can still
  // use the semantics to weaken the nogood.
  vec<Lit> removed;
  assert(!sat.reason[var(p)].isLazy()); 
  if(sat.trailpos[var(p)] < 0) {
    return; // p is false at the root.
  }
  
  Clause* cp = sat.getExpl(~p);
  if(!cp) {
    // Somebody has pushed inconsistent assumptions.
    // * This may happen if, in an optimization problem, the user
    // * provided an objective lower bound which is achieved.

    // If p and ~p are assumptions, we just return a
    // tautological clause.
    out_nogood.push(p);
    return;
  } else {
    // Otherwise, fill in the reason for ~p...
    for(int i = 1; i < cp->size(); i++) {
      Lit q((*cp)[i]);
      if(sat.trailpos[var(q)] < 0)
        continue;
      out_nogood.push(q);
      // Only look at the first bit of seen, because
      // we're using the second bit for assumption-ness.
      sat.seen[var(q)] |= 1;
    }
    // then push it back to assumptions.
    for(int i = 1; i < out_nogood.size(); i++) {
      Lit q(out_nogood[i]);
      if(is_extractable(q)) continue;
      assert(!sat.reason[var(q)].isLazy());
      Clause& c = *sat.getExpl(~q);
      assert(&c != nullptr);
      removed.push(q);
      out_nogood[i] = out_nogood.last();
      out_nogood.pop();
      --i;

      for(int j = 1; j < c.size(); j++) {
        Lit r(c[j]);
        if(!(sat.seen[var(r)]&1)) {
          sat.seen[var(r)] |= 1;
          if(sat.trailpos[var(r)] < 0)
            removed.push(r);
          else
            out_nogood.push(r);
        }
      }
    }
  }
  // Clear the 'seen' bit.
	for (int i = 0; i < removed.size(); i++) sat.seen[var(removed[i])] &= (~1);
  for (int i = 1; i < out_nogood.size(); i++) sat.seen[var(out_nogood[i])] &= (~1);
}


#endif
