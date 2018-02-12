#ifndef CHUFFED_WARMSTART__H
#define CHUFFED_WARMSTART__H
#include <chuffed/branching/branching.h>

// Warm-start brancher.
// Once activated, it optimistically branches on the given literals
// in order. It de-activates itself as soon as the first (post-activation) conflict
// is hit.

class WarmStartBrancher : public Branching {
public:
  WarmStartBrancher(vec<Lit>& _decs, bool _revive = false)
    : decs(_decs), revive(_revive), init_conflicts(INT_MAX) {

  }

  WarmStartBrancher(vec<IntVar*> xs, vec<int>& vs, bool _revive = false)
    : revive(_revive), init_conflicts(INT_MAX) {
     
  }
    
	bool finished() {
    // Already deactivated
    if(engine.conflicts > init_conflicts)
      return true;

    if(pos < decs.size()) {
      if(sat.value(decs[pos]) == l_Undef)
        return false;
      if(engine.conflicts < init_conflicts)
        trailSave(pos);
      for(++pos; pos < decs.size(); ++pos) {
        if(sat.value(decs[pos]) == l_Undef) 
          return false;
      }
    }
    return true;
  }

	double getScore(VarBranch vb) { NEVER; }

	DecInfo* branch() {
    // Check if this is the first activation
    if(engine.conflicts < init_conflicts) {
      if(revive) {
        trailSave(init_conflicts);
        trailSave(pos);
      }
      init_conflicts = engine.conflicts;
    }
    if(engine.conflicts == init_conflicts && pos < decs.size()) {
      for(; pos < decs.size(); ++pos) {
        if(sat.value(decs[pos]) == l_Undef) {
          return new DecInfo(nullptr, toInt(decs[pos]));
        }
      }
    }
    return nullptr;
  }

protected:
  vec<Lit> decs; // Decisions to make
  int pos; // Current position
  bool revive; // Should be brancher be revived 


  int init_conflicts; // Number of conflicts at time of activation.
};
#endif
