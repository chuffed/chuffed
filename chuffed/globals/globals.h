#ifndef globals_h
#define globals_h

#include <chuffed/core/propagator.h>
#include <list>

//-----
// Directives

void output_var(Branching* v);
void output_vars(vec<Branching*>& v);
void output_vars(vec<IntVar*>& v);

// Well Foundedness Directives

void add_inductive_rule(BoolView hl, vec<BoolView>& posb, vec<BoolView>& negb, int wf_id);
void wf_init();

//-----
// Propagators

// alldiff.c

void all_different(vec<IntVar*>& x, ConLevel cl = CL_DEF);
void all_different_offset(vec<int>& a, vec<IntVar*>& x, ConLevel cl = CL_DEF);
void inverse(vec<IntVar*>& x, vec<IntVar*>& y, int o1 = 0, int o2 = 0, ConLevel cl = CL_DEF);

// circuit.c

void circuit(vec<IntVar*>& x, int offset = 0);
void path(vec<IntVar*>& x);

// subcircuit.c

void subcircuit(vec<IntVar*>& x, int offset = 0);
void subpath(vec<IntVar*>& _x);

// linear-bool.c

void bool_linear(vec<BoolView>& x, IntRelType t, IntVar* y);

// linear-bool-decomp.c
void bool_linear_decomp(vec<BoolView>& x, IntRelType t, int k);
void bool_linear_decomp(vec<BoolView>& x, IntRelType t, IntVar* y);

// minimum.c

void minimum(vec<IntVar*>& x, IntVar* y);
void maximum(vec<IntVar*>& x, IntVar* y);

// table.c

void table(vec<IntVar*>& x, vec<vec<int> >& t);

// regular.c

void regular(vec<IntVar*>& x, int q, int s, vec<vec<int> >& d, int q0, vec<int>& f);

// disjunctive.c

void disjunctive(vec<IntVar*>& s, vec<int>& d);

// cumulative.c

void cumulative(vec<IntVar*>& s, vec<int>& d, vec<int>& r, int b);
void cumulative(vec<IntVar*>& s, vec<int>& d, vec<int>& r, int b, std::list<std::string> opt);
void cumulative2(vec<IntVar*>& s, vec<IntVar*>& d, vec<IntVar*>& r, IntVar* b);
void cumulative2(vec<IntVar*>& s, vec<IntVar*>& d, vec<IntVar*>& r, IntVar* b, std::list<std::string> opt);
void cumulative_cal(vec<IntVar*>& s, vec<IntVar*>& d, vec<IntVar*>& r, IntVar* limit, vec<vec<int> >& cal, vec<int>& taskCal, int rho, int resCal);
void cumulative_cal(vec<IntVar*>& s, vec<IntVar*>& d, vec<IntVar*>& r, IntVar* limit, vec<vec<int> >& cal, vec<int>& taskCal, int rho, int resCal, std::list<std::string> opt);

// lex.c

void lex(vec<IntVar*>& x, vec<IntVar*>& y, bool strict);

// sym-break.c

void var_sym_break(vec<IntVar*>& x);
void val_sym_break(vec<IntVar*>& x, int l, int u);


//tree.c

void tree(vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _adj, vec< vec<int> >& _en);
void connected(vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _adj, vec< vec<int> >& _en);

//mst.c

void mst(vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _adj, vec< vec<int> >& _en, IntVar* _w, vec<int>& _ws);

//minimum_weight_tree.c

void steiner_tree(vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _adj, vec< vec<int> >& _en, IntVar* _w, vec<int> _ws);

//dconnected.c

void dconnected(int r, vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _in, vec< vec<int> >& _out, vec< vec<int> >& _en);

//dtree.c

void dtree(int r, vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _in, vec< vec<int> >& _out, vec< vec<int> >& _en);
void reversedtree(int r, vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _in, vec< vec<int> >& _out, vec< vec<int> >& _en);
void path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _in, vec< vec<int> >& _out, vec< vec<int> >& _en);

//dag.c

void dag(int r, vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _in, vec< vec<int> >& _out, vec< vec<int> >& _en);

//bounded_path.c

void bounded_path(int from, int to, vec<BoolView>& _vs, vec<BoolView>& _es, vec< vec<int> >& _in, vec< vec<int> >& _out, vec< vec<int> >& _en, vec<int>& _ws, IntVar* w);

#endif
