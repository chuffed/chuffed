#ifndef vars_h
#define vars_h

#include <chuffed/branching/branching.h>

enum EVENT_TYPE {
	EVENT_C = 1,		// Any change in the domain of the variable
	EVENT_L = 2,		// Lower bound change of the variable
	EVENT_U = 4,		// Upper bound change of the variable
	EVENT_F = 8,		// When the variable is fixed
	EVENT_LU = 6,		// Lower and upper bound change of the variable
	EVENT_LF = 10,		// Lower bound change and fixation of the variable
	EVENT_UF = 12		// Upper bound change and fixation of the variable
};

enum VarType {
	BOOL_VAR,		// Boolean variable
	INT_VAR,		// Integer variable
	INT_VAR_EL,		// Integer variable with eager literals
	INT_VAR_LL,		// Integer variable with lazy literals
	INT_VAR_SL
};

enum PreferredVal {
	PV_MIN,
	PV_MAX,
	PV_SPLIT_MIN,
	PV_SPLIT_MAX,
	PV_MEDIAN
};

// t = 0: [x != v], t = 1: [x = v], t = 2: [x >= v], t = 3: [x <= v]
enum LitRel {
  LR_NE = 0,
  LR_EQ = 1,
  LR_GE = 2,
  LR_LE = 3
};

class Var : public Branching {
public:
	virtual VarType getType() = 0;
	virtual void setPreferredVal(PreferredVal vb) = 0;
  virtual ~Var(void) {}
};

#endif

