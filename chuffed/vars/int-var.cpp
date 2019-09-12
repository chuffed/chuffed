#include <map>
#include <chuffed/vars/int-var.h>
#include <chuffed/mip/mip.h>
#include <sstream>

// When set, branch variable (first_fail) and value (indomain_median,
// indomain_split, indomain_reverse_split) specifications will count domain
// sizes by the number of active values rather than the bounds (max-min).
// (There is not too much penalty if INT_DOMAIN_LIST enabled in int-var.h).
#define INT_BRANCH_HOLES 0

using namespace std;

map<int,IntVar*> ic_map;

extern std::map<IntVar*, std::string> intVarString;

IntVar::IntVar(int _min, int _max) :
		var_id(engine.vars.size())
	, min(_min)
	, max(_max)
	, min0(_min)
	, max0(_max)
	, shadow_val(0)
	, in_scip(false)
	, all_in_scip(true)
  , should_be_learnable(true)
  , should_be_decidable(true)
  , vals(NULL)
  , preferred_val(PV_MIN)
  , activity(0)
  , in_queue(false)
{
	assert(min_limit <= min && min <= max && max <= max_limit);
	engine.vars.push(this);
	changes = EVENT_C | EVENT_L | EVENT_U;
	if (isFixed()) changes |= EVENT_F;
}

// Allocate enough memory to specialise IntVar later using the same memory block
IntVar* newIntVar(int min, int max) {
	size_t size = sizeof(IntVar);
	if (sizeof(IntVarEL) > size) size = sizeof(IntVarEL);
	if (sizeof(IntVarLL) > size) size = sizeof(IntVarLL);
	if (sizeof(IntVarSL) > size) size = sizeof(IntVarSL);
	void *mem = malloc(size);
	IntVar *var = new (mem) IntVar(min, max);
	return var;
}

IntVar* getConstant(int v) {
	map<int,IntVar*>::iterator it = ic_map.find(v);
	if (it != ic_map.end()) return it->second;
	IntVar *var = newIntVar(v,v);

        std::stringstream ss;
        ss << "constant_" << v;
        intVarString[var] = ss.str();

        var->specialiseToEL();
	ic_map.insert(pair<int,IntVar*>(v, var));

        
	return var;
}

void IntVar::specialiseToEL() {
	switch (getType()) {
		case INT_VAR_EL: return;
		case INT_VAR_SL: return;
		case INT_VAR: new (this) IntVarEL(*((IntVar*) this)); break;
		default: NEVER;
	}
}

void IntVar::specialiseToLL() {
	switch (getType()) {
		case INT_VAR_EL: return;
		case INT_VAR_SL: return;
		case INT_VAR: new (this) IntVarLL(*((IntVar*) this)); break;
		default: NEVER;
	}
}

void IntVar::specialiseToSL(vec<int>& values) {
	if (getType() == INT_VAR_EL) return;
	if (getType() == INT_VAR_SL) return;
	assert(getType() == INT_VAR);

	vec<int> v = values;
	std::sort((int*) v, (int*) v + v.size());
	int i, j;
	for (i = j = 0; i < v.size(); i++) {
		if (i == 0 || v[i] != v[i-1]) v[j++] = v[i];
	}
	v.resize(j);


//	for (int i = 0; i < values.size(); i++) printf("%d ", values[i]);
//	printf("\n");

	// determine whether it is sparse or dense
	if (v.last()-v[0] >= v.size() * mylog2(v.size())) {
//		fprintf(stderr, "SL\n");
		new (this) IntVarSL(*((IntVar*) this), v);
	} else {
		new (this) IntVarEL(*((IntVar*) this));
		if (!allowSet(v)) TL_FAIL();
	}
}

void IntVar::initVals(bool optional) {
	if (vals) return;
	if (min == min_limit || max == max_limit) {
		if (optional) return;
		CHUFFED_ERROR("Cannot initialise vals in unbounded IntVar\n");
	}
	vals = (Tchar*) malloc((max-min+2) * sizeof(Tchar));
	if (!vals) { perror("malloc()"); exit(1); }
	memset(vals, 1, max-min+2);
	if (!(vals -= min)) vals++;      // Hack to make vals != NULL whenever it's allocated
#if INT_DOMAIN_LIST
	vals_list = (Tint*) malloc(2*(max-min) * sizeof(Tint));
	if (!vals_list) { perror("malloc()"); exit(1); }
	vals_list -= 2*min+1;
	for (int i = min; i < max; ++i) {
		vals_list[2*i+1].v = i+1; // forward link
		vals_list[2*i+2].v = i; // backward link from next value
	}
	vals_count.v = max+1-min;
#endif
}

void IntVar::attach(Propagator *p, int pos, int eflags) {
	if (isFixed()) p->wakeup(pos, eflags);
	else pinfo.push(PropInfo(p, pos, eflags));
}

void IntVar::wakePropagators() {
	for (int i = pinfo.size(); i--; ) {
		PropInfo& pi = pinfo[i];
		if ((pi.eflags & changes) == 0) continue;
		if (pi.p->satisfied) continue;
		if (pi.p == engine.last_prop) continue;
		pi.p->wakeup(pi.pos, changes);
	}
	clearPropState();
}

int IntVar::simplifyWatches() {
	int i, j;
	for (i = j = 0; i < pinfo.size(); i++) {
		if (!pinfo[i].p->satisfied) pinfo[j++] = pinfo[i];
	}
	pinfo.resize(j);
	return j;
}

//-----
// Branching stuff

double IntVar::getScore(VarBranch vb) {
	switch(vb) {
		case VAR_MIN_MIN       : return -min;
		case VAR_MIN_MAX       : return min;
		case VAR_MAX_MIN       : return -max;
		case VAR_MAX_MAX       : return max;
#if INT_BRANCH_HOLES
		// note slight inconsistency, if INT_BRANCH_HOLES=0 then we
		// use the domain size-1, same behaviour but more efficient?
 		case VAR_SIZE_MIN      : return vals ? -size() : min - (max + 1);
		case VAR_SIZE_MAX      : return vals ? size() : max + 1 - min;
#else
		case VAR_SIZE_MIN      : return min-max;
		case VAR_SIZE_MAX      : return max-min;
#endif
		case VAR_DEGREE_MIN    : return -pinfo.size();
		case VAR_DEGREE_MAX    : return pinfo.size();
		case VAR_REDUCED_COST  : return mip->getRC(this);
		case VAR_ACTIVITY      : return activity;
                case VAR_REGRET_MIN_MAX: return isFixed() ? 0 : (vals ? *++begin() - *begin() : 1);
		default: NOT_SUPPORTED;
	}
}

DecInfo* IntVar::branch() {
//	vec<int> possible;
//	for (int i = min; i <= max; i++) if (indomain(i)) possible.push(i);
//	return new DecInfo(this, possible[rand()%possible.size()], 1);


	switch (preferred_val) {
		case PV_MIN       : return new DecInfo(this, min, 1);
		case PV_MAX       : return new DecInfo(this, max, 1);
#if INT_BRANCH_HOLES
		// note slight inconsistency, if INT_BRANCH_HOLES=0 then we
		// round down rather than up (vice versa for PV_SPLIT_MAX),
		// should probably revisit this and make them consistent
		case PV_SPLIT_MIN : {
				if (!vals)
					return new DecInfo(this, min + (max - min) / 2, 3);
				int values = (size()- 1) / 2;
				iterator j = begin();
				for (int i = 0; i < values; ++i)
					++j;
				return new DecInfo(this, *j, 3);
			}
		case PV_SPLIT_MAX : {
				if (!vals)
					return new DecInfo(this, min + (max - min - 1) / 2, 2);
				int values = size() / 2;
				iterator j = begin();
				for (int i = 0; i < values; ++i)
					++j;
				return new DecInfo(this, *j, 2);
			}
		case PV_MEDIAN: {
				if (!vals)
					return new DecInfo(this, min + (max - min) / 2, 1);
				int values = (size() - 1) / 2;
				iterator j = begin();
				for (int i = 0; i < values; ++i)
					++j;
				return new DecInfo(this, *j, 1);
			}
#else
		case PV_SPLIT_MIN:
			return new DecInfo(this, min+(max-min-1)/2, 3);
		case PV_SPLIT_MAX:
			return new DecInfo(this, min+(max-min)/2, 2);
		case PV_MEDIAN:
			if (!vals) {
				CHUFFED_ERROR("Median value selection is not supported this variable.\n");
			}
			else {
				int values = (size() - 1) / 2;
				iterator j = begin();
				for (int i = 0; i < values; ++i)
					++j;
				return new DecInfo(this, *j, 1);
			}
#endif
		default: NEVER;
	}
}

//-----
// Domain change stuff

#if !INT_DOMAIN_LIST
inline void IntVar::updateMin() {
	int v = min;
	if (!vals[v]) {
		while (!vals[v]) v++;
		min = v;
		changes |= EVENT_C | EVENT_L;
	}
}

inline void IntVar::updateMax() {
	int v = max;
	if (!vals[v]) {
		while (!vals[v]) v--;
		max = v;
		changes |= EVENT_C | EVENT_U;
	}
}
#endif

inline void IntVar::updateFixed() {
	if (isFixed()) changes |= EVENT_F;
}

bool IntVar::setMin(int64_t v, Reason r, bool channel) {
	assert(setMinNotR(v));
	if (v > max) return false;
#if INT_DOMAIN_LIST
	if (vals) {
		int i;
		int j = vals_count;
		for (i = min; i < v; i = vals_list[2*i+1])
			--j;
		min = i;
		vals_count = j;
	}
	else
		min = v;
	changes |= EVENT_C | EVENT_L;
#else
	min = v; changes |= EVENT_C | EVENT_L;
	if (vals) updateMin();
#endif
	updateFixed();
	pushInQueue();
	return true;
}

bool IntVar::setMax(int64_t v, Reason r, bool channel) {
	assert(setMaxNotR(v));
	if (v < min) return false;
#if INT_DOMAIN_LIST
	if (vals) {
		int i;
		int j = vals_count;
		for (i = max; i > v; i = vals_list[2*i])
			--j;
		max = i;
		vals_count = j;
	}
	else
		max = v;
	changes |= EVENT_C | EVENT_U;
#else
	max = v; changes |= EVENT_C | EVENT_U;
	if (vals) updateMax();
#endif
	updateFixed();
	pushInQueue();
	return true;
}

bool IntVar::setVal(int64_t v, Reason r, bool channel) {
	assert(setValNotR(v));
	if (!indomain(v)) return false;
	if (min < v) { min = v; changes |= EVENT_C | EVENT_L | EVENT_F; }
	if (max > v) { max = v; changes |= EVENT_C | EVENT_U | EVENT_F; }
#if INT_DOMAIN_LIST
	if (vals)
		vals_count = 1;
#endif
	pushInQueue();
	return true;
}

bool IntVar::remVal(int64_t v, Reason r, bool channel) {
	assert(remValNotR(v));
	if (isFixed()) return false;
	if (!vals) {
		if (!engine.finished_init) NEVER;
		return true;
	}
#if INT_DOMAIN_LIST
	if (v == min) {
		min = vals_list[2*min+1];
		changes |= EVENT_C | EVENT_L;
	}
	else if (v == max) {
		max = vals_list[2*max];
		changes |= EVENT_C | EVENT_U;
	}
	else {
		vals[v] = 0;
		vals_list[vals_list[2*v]*2+1] = vals_list[2*v+1];
		vals_list[vals_list[2*v+1]*2] = vals_list[2*v];
		changes |= EVENT_C;
	}
	--vals_count;
#else
	vals[v] = 0; changes |= EVENT_C;
	updateMin();
	updateMax();
#endif
	updateFixed();
	pushInQueue();
	return true;
}

// Assumes v is sorted
bool IntVar::allowSet(vec<int>& v, Reason r, bool channel) {
  initVals();
	if (!vals && !engine.finished_init) NOT_SUPPORTED;
	int i = 0;
	int m = min;
	while (i < v.size() && v[i] < m) i++;
	for ( ; i < v.size(); i++) {
		for ( ; m < v[i]; m++) {
			if (m > max) return true;
			if (remValNotR(m)) if (!remVal(m, r, channel)) return false;
		}
		m = v[i]+1;
	}
	for ( ; m <= max; m++) {
		if (remValNotR(m)) if (!remVal(m, r, channel)) return false;
	}
	return true;
}
