#ifndef impact_h
#define impact_h
#ifdef HAS_VAR_IMPACT
#include <chuffed/support/misc.h>
#include <chuffed/support/vec.h>

double processImpact(vec<int> const& previousSizes, vec<int> const& newSizes);
double solvedImpact(vec<int> const& previousSizes);

#endif
#endif
