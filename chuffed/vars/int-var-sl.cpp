#include <chuffed/core/propagator.h>
#include <chuffed/core/sat.h>
#include <chuffed/vars/int-var.h>

extern std::map<IntVar*, std::string> intVarString;

IntVarSL::IntVarSL(const IntVar& other, vec<int>& _values) : IntVar(other), values(_values) {
	initVals();

	// handle min, max and vals
	int l = 0;
	while (values[l] < min) {
		if (++l == values.size()) {
			TL_FAIL();
		}
	}
	while (vals[values[l]] == 0) {
		if (++l == values.size()) {
			TL_FAIL();
		}
	}
	min = values[l];

	//	printf("l = %d\n", l);

	int u = values.size() - 1;
	while (values[u] > max) {
		if (u-- == 0) {
			TL_FAIL();
		}
	}
	while (vals[values[u]] == 0) {
		if (u-- == 0) {
			TL_FAIL();
		}
	}
	max = values[u];

	//	printf("u = %d\n", u);

	for (int i = min, k = l; i <= max; i++) {
		if (i == values[k]) {
			k++;
			continue;
		}
		vals[i] = 0;
	}

	for (int i = l; i <= u; i++) {
		values[i - l] = values[i];
	}
	values.resize(u - l + 1);

	//	for (int i = 0; i < values.size(); i++) printf("%d ", values[i]);
	//	printf("\n");

	// create the IntVarEL
	IntVar* v = newIntVar(0, values.size() - 1);
	// inherit the name from this SL
	intVarString[v] = intVarString[this];
	v->specialiseToEL();
	el = (IntVarEL*)v;

	// rechannel channel info
	for (int i = 0; i < values.size(); i++) {
		Lit p = el->getLit(i, LR_NE);
		sat.c_info[var(p)].cons_id = var_id;
	}
	for (int i = 0; i <= values.size(); i++) {
		Lit p = el->getLit(i, LR_GE);
		sat.c_info[var(p)].cons_id = var_id;
	}

	// transfer pinfo to el
	for (int i = 0; i < pinfo.size(); i++) {
		el->pinfo.push(pinfo[i]);
	}
	pinfo.clear(true);
}

void IntVarSL::attach(Propagator* p, int pos, int eflags) {
	if (isFixed()) {
		p->wakeup(pos, eflags);
	} else {
		el->pinfo.push(PropInfo(p, pos, eflags));
	}
}

int IntVarSL::transform(int v, int type) {
	int l = 0;
	int u = values.size() - 1;
	int m;
	while (true) {
		m = (l + u) / 2;
		if (values[m] == v) {
			return m;
		}
		if (values[m] < v) {
			l = m + 1;
		} else {
			u = m - 1;
		}
		if (u < l) {
			break;
		}
	}
	switch (type) {
		case 0:
			return u;
		case 1:
			return l;
		case 2:
			return -1;
		default:
			NEVER;
	}
}

// t = 0: [x != v], t = 1: [x = v], t = 2: [x >= v], t = 3: [x <= v]
Lit IntVarSL::getLit(int64_t v, LitRel t) {
	int u;
	switch (t) {
		case LR_NE:
			u = transform(v, 2);
			return (u == -1 ? lit_True : el->getLit(u, LR_NE));
		case LR_EQ:
			u = transform(v, 2);
			return (u == -1 ? lit_False : el->getLit(u, LR_EQ));
		case LR_GE:
			return el->getLit(transform(v, 1), LR_LE);
		case LR_LE:
			return el->getLit(transform(v, 0), LR_GE);
		default:
			NEVER;
	}
}

bool IntVarSL::setMin(int64_t v, Reason r, bool channel) {
	assert(setMinNotR(v));
	//	debug();
	//	printf("setMin: v = %d, u = %d\n", v, transform(v, 0));
	if (!el->setMin(transform(v, 1), r, channel)) {
		return false;
	}
	min = values[el->min];
	return true;
}

bool IntVarSL::setMax(int64_t v, Reason r, bool channel) {
	assert(setMaxNotR(v));
	//	debug();
	//	printf("setMax: v = %d, u = %d\n", v, transform(v, 0));
	if (!el->setMax(transform(v, 0), r, channel)) {
		return false;
	}
	max = values[el->max];
	return true;
}

bool IntVarSL::setVal(int64_t v, Reason r, bool channel) {
	assert(setValNotR(v));
	int u = transform(v, 2);
	if (u == -1) {
		if (channel) {
			sat.cEnqueue(lit_False, r);
		}
		assert(sat.confl);
		return false;
	}
	if (!el->setVal(u, r, channel)) {
		return false;
	}
	if (min < v) {
		min = v;
	}
	if (max > v) {
		max = v;
	}
	return true;
}

bool IntVarSL::remVal(int64_t v, Reason r, bool channel) {
	assert(remValNotR(v));
	int u = transform(v, 2);
	assert(u != -1);
	if (!el->remVal(u, r, channel)) {
		return false;
	}
	vals[v] = 0;
	min = values[el->min];
	max = values[el->max];
	return true;
}

void IntVarSL::channel(int val, int val_type, int sign) {
	//	fprintf(stderr, "funny channel\n");
	int type = val_type * 3 ^ sign;
	el->set(val, type, false);
	if (type == 0) {
		vals[values[val]] = 0;
	}
	min = values[el->min];
	max = values[el->max];
}

void IntVarSL::debug() {
	printf("min = %d, max = %d, el->min = %d, el->max = %d\n", (int)min, (int)max, (int)el->min,
				 (int)el->max);
	for (int i = 0; i < values.size(); i++) {
		printf("%d ", values[i]);
	}
	printf("\n");
}
