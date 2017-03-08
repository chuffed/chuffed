#ifndef branching_h
#define branching_h

#include <cstdio>
#include <cassert>
#include <climits>
#include <chuffed/support/misc.h>
#include <chuffed/core/engine.h>

//-----

enum VarBranch {
	VAR_DEFAULT,             // autonomous search
	VAR_INORDER,             // inorder
	VAR_SIZE_MIN,            // smallest domain 
	VAR_SIZE_MAX,            // largest domain
	VAR_MIN_MIN,             // smallest smallest value in domain
	VAR_MIN_MAX,             // largest smallest value in domain
	VAR_MAX_MIN,             // smallest largest value in domain
	VAR_MAX_MAX,             // largest largest value in domain
	VAR_DEGREE_MIN,          // smallest degree
	VAR_DEGREE_MAX,          // largest degree
	VAR_REGRET_MIN_MAX,      // largest min regret
	VAR_REGRET_MAX_MAX,      // largest max regret
	VAR_REDUCED_COST,        // largest reduced cost from MIP
	VAR_PSEUDO_COST,         // largest pseudo cost from MIP
	VAR_ACTIVITY,            // largest vsids activity
	VAR_RANDOM               // random
};

//-----

enum ValBranch {
	VAL_DEFAULT,            // preferred pol (static), then global pol (dynamic)
	VAL_MIN,                // smallest value
	VAL_MAX,                // largest value
	VAL_MIDDLE,             // middle value
	VAL_MEDIAN,             // median value
	VAL_SPLIT_MIN,          // lower half
	VAL_SPLIT_MAX,          // upper half
	VAL_RANDOM              // random
};

class Tint;

class DecInfo {
public:
	void *var; int val; int type;
	DecInfo(void *_var, int _val, int _type = -1) :
		var(_var), val(_val), type(_type) {}
};

class Branching {
public:
	virtual bool finished() = 0;
	virtual double getScore(VarBranch vb) = 0;
	virtual DecInfo* branch() = 0;
};

class BranchGroup : public Branching {
public:
	vec<Branching*> x;
	VarBranch var_branch;
	bool terminal;

	// Persistent data
	Tint fin;
	Tint cur;

	// Intermediate data
	vec<int> moves;

	BranchGroup(VarBranch vb = VAR_INORDER, bool t = false);
	BranchGroup(vec<Branching*>& _x, VarBranch vb, bool t = false);

	bool finished();
	double getScore(VarBranch vb);
	DecInfo* branch();

	void add(Branching *n) { x.push(n); }

};

BranchGroup* branch(vec<Branching*> x, VarBranch var_branch, ValBranch val_branch);

class PriorityBranchGroup : public BranchGroup {
public:
	vec<Branching*> decisionVars;
    vec<Branching*> annotations;
	VarBranch var_branch;

	// Persistent data
	Tint fin;
	Tint cur;

	// Intermediate data
	vec<int> moves;

	PriorityBranchGroup(vec<Branching*>& _x, VarBranch vb);

	bool finished();
	double getScore(VarBranch vb);
	DecInfo* branch();

	void add(Branching *n) { annotations.push(n); }

};

#endif
