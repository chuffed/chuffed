#include <chuffed/core/propagator.h>

void regular_check(vec<IntVar*>& x, int q, int s, vec<vec<int> >& d, int q0, vec<int>& f) {
	assert(q >= 1);
	assert(s >= 1);
	assert(d.size() == q);
	for (int i = 0; i < q; i++) {
		assert(d[i].size() == s);
		for (int j = 0; j < s; j++) {
			assert(d[i][j] >= 0 && d[i][j] <= q);
		}
	}
	assert(q0 >= 1 && q0 <= q);
	for (int i = 0; i < f.size(); i++) {
		assert(f[i] >= 1 && f[i] <= q);
	}
}

void regular(vec<IntVar*>& x, int q, int s, vec<vec<int> >& d, int q0, vec<int>& f) {
	regular_check(x, q, s, d, q0, f);
	//	bool accept[q+1];
	bool* accept = new bool[q + 1];
	for (int i = 0; i <= q; i++) {
		accept[i] = false;
	}
	for (int i = 0; i < f.size(); i++) {
		accept[f[i]] = true;
	}
	vec<vec<int> > start;
	vec<vec<int> > middle;
	vec<vec<int> > end;
	for (int i = 0; i < q; i++) {
		for (int j = 0; j < s; j++) {
			if (d[i][j] == 0) {
				continue;
			}
			if (i + 1 == q0) {
				start.push();
				start.last().push(j + 1);
				start.last().push(d[i][j]);
			}
			middle.push();
			middle.last().push(i + 1);
			middle.last().push(j + 1);
			middle.last().push(d[i][j]);
			if (accept[d[i][j]]) {
				end.push();
				end.last().push(i + 1);
				end.last().push(j + 1);
			}
		}
	}
	vec<IntVar*> y;
	for (int i = 1; i < x.size(); i++) {
		y.push(newIntVar(1, q));
	}
	vec<IntVar*> sx;
	sx.push(x[0]);
	sx.push(y[0]);
	table(sx, start);
	for (int i = 1; i < x.size() - 1; i++) {
		vec<IntVar*> mx;
		mx.push(y[i - 1]);
		mx.push(x[i]);
		mx.push(y[i]);
		table(mx, middle);
	}
	vec<IntVar*> ex;
	ex.push(y.last());
	ex.push(x.last());
	table(ex, end);
	delete[] accept;
}
