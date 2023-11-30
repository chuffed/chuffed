#ifndef impact_h
#define impact_h
#ifdef HAS_VAR_IMPACT
#include "chuffed/support/misc.h"
#include "chuffed/support/vec.h"

double processImpact(const vec<int>& previousSizes, const vec<int>& newSizes);
double solvedImpact(const vec<int>& previousSizes);

#endif
#endif
