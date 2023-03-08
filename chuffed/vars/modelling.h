#ifndef modelling_h
#define modelling_h

#include <chuffed/support/misc.h>
#include <chuffed/vars/bool-view.h>
#include <chuffed/vars/int-var.h>

void createVar(IntVar*& x, int min, int max, bool el = false);
void createVars(vec<IntVar*>& x, int n, int min, int max, bool el = false);
void createVars(vec<vec<IntVar*> >& x, int n, int m, int min, int max, bool el = false);
void createVars(vec<BoolView>& x, int n);
void createVars(vec<vec<BoolView> >& x, int n, int m);

template <class U>
void transpose(vec<vec<U> >& x, vec<vec<U> >& y) {
	assert(y.size() == 0);
	int n = x[0].size();
	int m = x.size();
	y.growTo(n);
	for (int i = 0; i < n; i++) {
		y[i].growTo(m);
		for (int j = 0; j < m; j++) {
			y[i][j] = x[j][i];
		}
	}
}

template <class U>
void flatten(vec<vec<U> >& x, vec<U>& y) {
	assert(y.size() == 0);
	int n = x.size();
	int m = x[0].size();
	y.growTo(n * m);
	for (int i = 0; i < n; i++) {
		for (int j = 0; j < m; j++) {
			y[i * m + j] = x[i][j];
		}
	}
}

#endif
