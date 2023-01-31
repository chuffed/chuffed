#ifndef assume_h
#define assume_h
#include <chuffed/support/misc.h>
#include <chuffed/core/sat-types.h>
#include <chuffed/core/sat.h>

// Helper for pushing a failure back to externally visible literals.
// WARNING: This assumes explanations are not lazy.
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
      Clause* c = sat.getExpl(~q);
      assert(c != nullptr);
      removed.push(q);
      out_nogood[i] = out_nogood.last();
      out_nogood.pop();
      --i;

      for(int j = 1; j < c->size(); j++) {
        Lit r((*c)[j]);
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

// General version, which permits lazy explanations.
// Basically a mix of pushback and normal conflict analysis.
template<class Pred>
void pushback_reason_lazy(const Pred& is_extractable, Lit p, vec<Lit>& out_nogood) {
  assert(sat.value(p) == l_False);
  out_nogood.push(~p);
  // TODO: Take literal subsumption into account.
  // Even though we can't _export_ integer bounds, we can still
  // use the semantics to weaken the nogood.
  vec<Lit> removed;
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
  }

  // There _should_ be at least one atom at the current decision level.
  int pending = 0;
  for(int jj = 1; jj < (*cp).size(); ++jj) {
    Lit p((*cp)[jj]);
    assert(sat.value(p) == l_False);

    sat.seen[var(p)] |= 1;
    if(sat.trailpos[var(p)] < 0) {
      removed.push(p); // If trailpos < 0, not needed.
    } else {
      pending++;
    }
  }
  assert(pending > 0);
  if(pending == 0)
    return;

  // Process the levels in order.
  Reason last_reason = sat.reason[var(p)];

  int lev = sat.decisionLevel();
  // Should never need to touch level 0.
  while(lev > 0) {
	  vec<Lit>& ctrail = sat.trail[lev];

    int& index = sat.index;
    index = ctrail.size();
    while(index) {
      // Skip variables we haven't seen
      if(!(sat.seen[var(ctrail[--index])]&1))
        continue;
      
      // Found the next literal.
      Lit p(ctrail[index]);
      pending--;

      assert(sat.value(p) == l_True);
      if(is_extractable(p)) {
        // p is an assumption.
        // See if we can drop it anyway.
        Clause* expl(sat.getExpl(p));
        if(!expl) {
          out_nogood.push(~p);
        } else {
          // If every antecedent is already seen, we don't need it.
          for(int j = 1; j < (*expl).size(); ++j) {
            if(!(sat.seen[var((*expl)[j])]&1)) {
              // Needed after all
              out_nogood.push(~p);
              goto processed_assump;
            }
          }
          // Remember to reset seen at the end.
          removed.push(p);
        }
processed_assump:
        // Have we seen enough?
        if(!pending)
          goto pushback_finished;
        continue;
      }

      // Not an assumption; mark the antecedents as seen.
      assert(var(p) >= 0 && var(p) < sat.nVars());

      // Sign doesn't really matter here; just the var.
      removed.push(p);

      if (last_reason == sat.reason[var(p)]) continue;
      last_reason = sat.reason[var(p)];

      Clause& c = *sat.getExpl(p);
      assert(&c);

      for (int j = 1; j < c.size(); j++) {
        Lit q = c[j];
        if (!(sat.seen[var(q)]&1)) {
          sat.seen[var(q)] |= 1;
          assert(sat.value(q) == l_False);
          assert(sat.trailpos[var(q)] <= engine.trail.size());
          if(sat.trailpos[var(q)] < 0) {
            removed.push(q);
          } else {
            pending++;
          }
        }
      }
      assert(pending > 0);
    }
    // Finished at the current level.
    lev--;
    // We need to explicitly backtrack, because
    // getExpl calls btToPos, which accesses the _current_
    // decision level's trail.
    sat.btToLevel(lev);
  }

pushback_finished:
  assert(pending == 0);

	for (int i = 0; i < removed.size(); i++) sat.seen[var(removed[i])] &= (~1);
	for(int i = 0; i < out_nogood.size(); i++) sat.seen[var(out_nogood[i])] &= (~1);
}


#endif
