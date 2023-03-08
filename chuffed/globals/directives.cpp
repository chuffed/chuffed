#include <chuffed/core/propagator.h>

void output_var(Branching* v) { engine.outputs.push(v); }

void output_vars(vec<Branching*>& v) {
	for (int i = 0; i < v.size(); i++) {
		output_var(v[i]);
	}
}

void output_vars(vec<IntVar*>& v) {
	for (int i = 0; i < v.size(); i++) {
		output_var(v[i]);
	}
}
