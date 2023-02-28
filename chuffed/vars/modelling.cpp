#include <chuffed/vars/modelling.h>

void createVar(IntVar*& x, int min, int max, bool el) {
	x = newIntVar(min, max);
	if (el) x->specialiseToEL();
}

void createVars(vec<IntVar*>& x, int n, int min, int max, bool el) {
	assert(x.size() == 0);
	x.growTo(n);
	for (int i = 0; i < n; i++) {
		x[i] = newIntVar(min, max);
		if (el) x[i]->specialiseToEL();
	}
}

void createVars(vec<vec<IntVar*> >& x, int n, int m, int min, int max, bool el) {
	assert(x.size() == 0);
	x.growTo(n);
	for (int i = 0; i < n; i++) {
		x[i].growTo(m);
		for (int j = 0; j < m; j++) {
			x[i][j] = newIntVar(min, max);
			if (el) x[i][j]->specialiseToEL();
		}
	}
}

void createVars(vec<BoolView>& x, int n) {
	assert(x.size() == 0);
	x.growTo(n);
	for (int i = 0; i < n; i++) {
		x[i] = newBoolVar();
	}
}

void createVars(vec<vec<BoolView> >& x, int n, int m) {
	assert(x.size() == 0);
	x.growTo(n);
	for (int i = 0; i < n; i++) {
		x[i].growTo(m);
		for (int j = 0; j < m; j++) {
			x[i][j] = newBoolVar();
		}
	}
}
