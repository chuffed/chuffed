#include <map>
#include <utility>
#include <chuffed/core/propagator.h>

#define DEBUG 0
#define PREPROCESS 1
#define CALC_SCC 1
#define COMPLETE 1
#define ADD_CLAUSES 0
#define FLIP_NEG 1

using namespace std;

class ConjRule {
public:
	int head;
	int sz;
	Lit body_lit;
	int w;
	int body[0];

	ConjRule(int h, vec<int>& b, Lit bl) : head(h), sz(b.size()), body_lit(bl) {
		for (int i = 0; i < b.size(); i++) body[i] = b[i];
	}

	inline bool isFalse() { return sat.value(body_lit) == l_False; }

};

ConjRule* ConjRule_new(int h, vec<int>& b, Lit bl) {
	void* mem = malloc(sizeof(ConjRule) + b.size() * sizeof(int));
	return new (mem) ConjRule(h, b, bl);
}

class WellFounded : public Propagator {
public:
	// constant data

	vec<BoolView> raw_heads;
	vec<vec<BoolView> > raw_posb;
	vec<vec<BoolView> > raw_negb;
	vec<BoolView> raw_bl;

	vec<Lit> lits;                         // Boolean variable corresponding to the index
	vec<ConjRule*> rules;
	vec<int> scc_ids;

	multimap<int,int> raw_head_to_body;

	map<int,int> lit_to_index;
	map<int,ConjRule*> body_lit_to_rule;

	vec<vec<ConjRule*> > head_occ_rules;   // occurences in rule head
	vec<vec<ConjRule*> > body_occ_rules;   // occurences in rule body
	vec<vec<ConjRule*> > watches;          // rules where it is being watched

	// SCC calc stuff

	int index;
	vec<int> S;
	vec<bool> in_S;
	vec<int> indices;
	vec<int> lowlink;
	vec<vec<int> > sccs;



	// Persistent trailed state


	// Persistent non-trailed state

	vec<ConjRule*> support;

	// Intermediate state

	vec<vec<int> > no_support;             // set of non-false literals which has lost support
	vec<bool> no_support_bool;
	vec<int> ushead;
	vec<int> pufhead;

	vec<int> dead_rules;

	// Local variables

	vec<int> ufset;                        // the unfounded set we are constructing
	vec<bool> ufset_bool;
	vec<int> nfset;                        // the resupported literals

public:

	WellFounded() {
		// set priority
		priority = 3; 
	}

	int getId(Lit l) {
		pair<map<int,int>::iterator,bool> p = lit_to_index.insert(pair<int,int>(toInt(l), lits.size()));
		if (p.second) lits.push(l);
		return p.first->second;
	}

	void addRule(BoolView hl, vec<BoolView>& posb, vec<BoolView>& negb) {
		raw_heads.push(hl);
		raw_posb.push();
		posb.copyTo(raw_posb.last());
		raw_negb.push();
		negb.copyTo(raw_negb.last());
		raw_bl.push(bv_false);
	}

	void preprocess() {
		for (int i = 0; i < raw_heads.size(); i++) {
			raw_head_to_body.insert(pair<int,int>(toInt((Lit) raw_heads[i]), i));
		}

		for (int i = 0; i < raw_heads.size(); i++) {
			if (raw_posb[i].size() == 1 && raw_negb[i].size() == 0) {
				if (raw_head_to_body.count(toInt((Lit) raw_posb[i][0])) == 1) {
					int r = raw_head_to_body.find(toInt((Lit) raw_posb[i][0]))->second;
					raw_bl[i] = raw_posb[i][0];
					raw_posb[r].copyTo(raw_posb[i]);
					raw_negb[r].copyTo(raw_negb[i]);
					raw_heads[r] = bv_false;
				}
			}
		}

		for (int i = 0; i < raw_heads.size(); i++) {
			if (raw_heads[i] == bv_false) continue;
			getId(raw_heads[i]);
		}

	}

/*
	void strongconnect(int v) {
		indices[v] = index;
		lowlink[v] = index;
		index++;
		S.push(v);
		in_S[v] = true;

		for (int i = 0; i < head_occ_rules[v].size(); i++) {
			ConjRule& r = *head_occ_rules[v][i];
			for (int j = 0; j < r.sz; j++) {
				int w = r.body[j];
				if (indices[w] == -1) {
					strongconnect(w);
					if (lowlink[w] < lowlink[v]) lowlink[v] = lowlink[w];
				} else if (in_S[w]) {
					if (indices[w] < lowlink[v]) lowlink[v] = indices[w];
				}
			}
		}

    if (lowlink[v] == indices[v]) {
//			printf("SCC %d: ", scc_id);
			while (true) {
				int w = S.last();
				S.pop();
				in_S[w] = false;
				scc_ids[w] = scc_id;
//				printf("%d ", w);
				if (w == v) break;
			}
//			printf("\n");
			scc_id++;
		}
	}
*/

	static void getStaticEdges(WellFounded* wf, int v, vec<int>& edges) {
		edges.clear();
		for (int i = 0; i < wf->head_occ_rules[v].size(); i++) {
			ConjRule& r = *wf->head_occ_rules[v][i];
			for (int j = 0; j < r.sz; j++) {
				edges.push(r.body[j]);
			}
		}
	}

	static void getDynamicEdges(WellFounded* wf, int v, vec<int>& edges) {
		edges.clear();
		for (int i = 0; i < wf->head_occ_rules[v].size(); i++) {
			ConjRule& r = *wf->head_occ_rules[v][i];
			if (r.isFalse()) continue;
			edges.push(r.body[r.w]);
		}
//		fprintf(stderr, "%d: ", v);
//		for (int i = 0; i < edges.size(); i++) fprintf(stderr, "%d ", edges[i]);
//		fprintf(stderr, "\n");
	}



	void strongconnect(int v, void (*getEdges)(WellFounded*, int, vec<int>&)) {
		indices[v] = index;
		lowlink[v] = index;
		index++;
		S.push(v);
		in_S[v] = true;

		vec<int> edges;
		getEdges(this, v, edges);

		for (int i = 0; i < edges.size(); i++) {
			int w = edges[i];
			if (indices[w] == -1) {
				strongconnect(w, getEdges);
				if (lowlink[w] < lowlink[v]) lowlink[v] = lowlink[w];
			} else if (in_S[w]) {
				if (indices[w] < lowlink[v]) lowlink[v] = indices[w];
			}
		}
//		printf("%d: indices = %d, lowlink = %d\n", v, indices[v], lowlink[v]);

    if (lowlink[v] == indices[v]) {
			if (DEBUG) printf("SCC %d: ", sccs.size());
			sccs.push();
			while (true) {
				int w = S.last(); S.pop();
				in_S[w] = false;
				sccs.last().push(w);
				if (DEBUG) printf("%d ", w);
				if (w == v) break;
			}
			if (DEBUG) printf("\n");
		}
	}


	void init() {

		if (PREPROCESS) preprocess();
		else {
			for (int i = 0; i < raw_heads.size(); i++) getId(raw_heads[i]);
		}


		in_S.growTo(lits.size(), false);
		scc_ids.growTo(lits.size(), -1);
		indices.growTo(lits.size(), -1);
		lowlink.growTo(lits.size(), -1);

		head_occ_rules.growTo(lits.size());
		body_occ_rules.growTo(lits.size());

		watches.growTo(lits.size());
		support.growTo(lits.size(), NULL);

		no_support_bool.growTo(lits.size(), false);
		ufset_bool.growTo(lits.size(), false);

		// form rules
		for (int i = 0; i < raw_heads.size(); i++) {
			if (raw_heads[i] == bv_false) continue;
			if (raw_bl[i] == bv_false) raw_bl[i] = newBoolVar();
			if (FLIP_NEG) {
				vec<BoolView> b;
				for (int j = 0; j < raw_posb[i].size(); j++) b.push(raw_posb[i][j]);
				for (int j = 0; j < raw_negb[i].size(); j++) b.push(raw_negb[i][j]);
				array_bool_and(b, raw_bl[i]);
			} else {
				array_bool_and(raw_posb[i], raw_negb[i], raw_bl[i]);
			}
			if (so.well_founded) raw_bl[i].attach(this, rules.size(), EVENT_U);

			vec<int> b;
			for (int j = 0; j < raw_posb[i].size(); j++) {
				map<int,int>::iterator it = lit_to_index.find(toInt((Lit) raw_posb[i][j]));
				if (it == lit_to_index.end()) continue;
				b.push(it->second);
			}
			ConjRule *r = ConjRule_new(getId(raw_heads[i]), b, raw_bl[i]);
			rules.push(r);
		}

		for (int i = 0; i < rules.size(); i++) {
			ConjRule& r = *rules[i];
			for (int j = 0; j < r.sz; j++) {
				body_occ_rules[r.body[j]].push(&r);
			}
			head_occ_rules[r.head].push(&r);
		}

		// post array_bool_or's

		for (int i = 0; i < lits.size(); i++) {
			vec<BoolView> b;
			for (int j = 0; j < head_occ_rules[i].size(); j++) {
				b.push(BoolView(head_occ_rules[i][j]->body_lit));
				if (!COMPLETE) bool_rel(~BoolView(head_occ_rules[i][j]->body_lit), BRT_OR, BoolView(lits[i]));
			}
			if (COMPLETE) array_bool_or(b, BoolView(lits[i]));
		}

		// calc SCC's
		if (CALC_SCC) {
			index = 0;
			assert(S.size() == 0);
			for (int i = 0; i < indices.size(); i++) {
				indices[i] = -1;
				lowlink[i] = -1;
			}
			sccs.clear();

			for (int i = 0; i < lits.size(); i++) {
				if (indices[i] == -1) {
//					printf("SCC root: %d\n", i);
					strongconnect(i, &getStaticEdges);
//					printf("num scc's: %d\n", scc_id);
				}
			}
			assert(S.size() == 0);

			for (int i = 0; i < sccs.size(); i++) {
				for (int j = 0; j < sccs[i].size(); j++) {
					scc_ids[sccs[i][j]] = i;
				}
			}

		} else {
			sccs.push();
			for (int i = 0; i < lits.size(); i++) {
				scc_ids[i] = 0;
			}
		}

		no_support.growTo(sccs.size());
		ushead.growTo(sccs.size(), 0);
		pufhead.growTo(sccs.size(), 0);

		for (int i = 0; i < lits.size(); i++) {
			if (BoolView(lits[i]).isFalse()) continue;
			assert(scc_ids[i] >= 0);
			assert(scc_ids[i] < no_support.size());
//			fprintf(stderr, "%d ", scc_ids[i]);
			no_support[scc_ids[i]].push(i);
			no_support_bool[i] = true;
		}


//		if (DEBUG) {
			printf("Lits: %d\n", lits.size());
			printf("Rules: %d\n", rules.size());
			printf("SCCs: %d\n", sccs.size());
//		}

		if (DEBUG) for (int i = 0; i < rules.size(); i++) {
			ConjRule& r = *rules[i];
			printf("Rule %d: ", i);
			printf("%d <- ", r.head);
			for (int j = 0; j < r.sz; j++) printf("%d ", r.body[j]);
			printf("\n");
		}

		if (so.well_founded) pushInQueue();

	}


	void wakeup(int i, int c) {
		if (DEBUG) printf("wake up from rule %d\n", i);
		dead_rules.push(i);
		pushInQueue();
	}

	void killSupport(ConjRule *r) {
		int h = r->head;
		if (support[h] != r) return;
		if (BoolView(lits[h]).isFalse()) return;
		if (no_support_bool[h]) return;
		no_support[scc_ids[h]].push(h);
		no_support_bool[h] = true;
	}

	bool propagate() {
		// find all unsupported
		if (DEBUG) printf("propagating\n");

		for (int i = 0; i < dead_rules.size(); i++) killSupport(rules[dead_rules[i]]);
		
		for (int i = 0; i < no_support.size(); i++) {
			while (ushead[i] < no_support[i].size()) {
				int x = no_support[i][ushead[i]++];
				for (int j = 0; j < body_occ_rules[x].size(); j++) {
					killSupport(body_occ_rules[x][j]);
				}
			}
		}

		if (DEBUG) printf("Decision level: %d\n", engine.decisionLevel());

		if (DEBUG) printf("No support: ");
		if (DEBUG) for (int i = 0; i < no_support.size(); i++) {
			for (int j = 0; j < no_support[i].size(); j++) {
				printf("%d, ", no_support[i][j]);
			}
		}
		if (DEBUG) printf("\n");

		int start = -1;
		// pick one to start building unfounded set
		for (int i = 0; i < no_support.size(); i++) {
			for ( ; pufhead[i] < no_support[i].size(); pufhead[i]++) {
				int x = no_support[i][pufhead[i]];
				if (no_support_bool[x] && !BoolView(lits[x]).isFalse()) {
					start = x;
					break;
				}
			}
			if (start != -1) break;
		}

		// if all processed, we're done
		if (start == -1) {
			if (DEBUG) printf("all done\n");
			for (int i = 0; i < no_support.size(); i++) {
				no_support[i].clear();
				ushead[i] = 0;
				pufhead[i] = 0;
			}
			return true;
		}

		// start building unfounded set

		ufset.clear();
		ufset.push(start);
		ufset_bool[start] = true;

		if (DEBUG) printf("starting with %d\n", start);

		nfset.clear();
		int nfshead = 0;

		for (int uf = 0; uf < ufset.size(); uf++) {
			int h = ufset[uf];
			if (!no_support_bool[h]) {
				fprintf(stderr, "not no_support %d!\n", h);
				for (int k = 0; k < ufset.size(); k++) fprintf(stderr, "%d ", ufset[k]);
				fprintf(stderr, "- %d %d\n", uf, h);
			}
			assert(no_support_bool[h]);
			// add rules with h as head
			for (int i = 0; i < head_occ_rules[h].size(); i++) {
				if (DEBUG) printf("checking %dth rule for %d\n", i, h);
				ConjRule *r = head_occ_rules[h][i];
				if (r->isFalse()) continue;
				r->w = r->sz-1;
				if (DEBUG) printf("proping rule\n");
				if (propRule(*r)) break;
			}
				
			// propagate nfset

			while (nfshead < nfset.size()) {
				int x = nfset[nfshead++];
				for (int i = 0; i < watches[x].size(); i++) {
					ConjRule *r = watches[x][i];
					// if head already founded by another rule, ignore
					if (!no_support_bool[r->head]) continue;
					if (r->isFalse()) continue;
					r->w--;
					propRule(*r);
				}
				watches[x].clear();
			}
		}

		// we have now found an unfounded set! i.e., everything in ufset which is still not justified

		// if empty, should jump straight back up!

		// calc dynamic SCC
//		fprintf(stderr, "calc Dyn SCC\n");

		index = 0;
		assert(S.size() == 0);
		for (int i = 0; i < indices.size(); i++) {
			indices[i] = -1;
			lowlink[i] = -1;
		}
		sccs.clear();

		for (int i = 0; i < ufset.size(); i++) {
			int h = ufset[i];
			if (!no_support_bool[h]) continue;
			if (indices[h] != -1) continue;
//			fprintf(stderr, "root %d ", h);
			strongconnect(h, &getDynamicEdges);
		}

		assert(S.size() == 0);

//		if (sccs.size() > 0) fprintf(stderr, "d %d ", sccs.size());

		// create an explanation

		vec<Lit> ps(1);

		for (int i = 0; i < ufset.size(); i++) {
			ufset_bool[ufset[i]] = false;
			watches[ufset[i]].clear();
			int h = ufset[i];
			if (!no_support_bool[h]) continue;
			for (int i = 0; i < head_occ_rules[h].size(); i++) {
				ConjRule *r = head_occ_rules[h][i];
				if (r->isFalse()) {
					ps.push(r->body_lit);
				}
			}
		}


		Clause *expl = Reason_new(ps.size());
		for (int i = 1; i < ps.size(); i++) (*expl)[i] = ps[i];
		for (int i = 0; i < ufset.size(); i++) {
			int h = ufset[i];
			if (!no_support_bool[h]) continue;
			if (DEBUG) printf("making %d false\n", h);
			if (ADD_CLAUSES) {
				ps[0] = ~lits[h];
				sat.addClause(*Clause_new(ps, false), false);
			}
			assert(!BoolView(lits[h]).isFalse());
			if (!BoolView(lits[h]).setVal(0, expl)) return false;
			no_support_bool[h] = false;
		}

		if (DEBUG) printf("reawaken\n");

		// reawaken, this is not quite correct
		engine.p_queue[priority].push(this);

		return true;
	}

	bool propRule(ConjRule& r) {
		for ( ; r.w >= 0; r.w--) {
			if (no_support_bool[r.body[r.w]]) break;
		}
		if (r.w < 0) {
			if (DEBUG) printf("found support for %d\n", r.head);
			// all literals are founded, make h founded.
			no_support_bool[r.head] = false;
			nfset.push(r.head);
			support[r.head] = &r;
			return true;
		}
		int x = r.body[r.w];
		watches[x].push(&r);
		if (!ufset_bool[x]) {
			if (DEBUG) printf("%d added to ufset\n", x);
			ufset.push(x);
			ufset_bool[x] = true;
		}
		return false;
	}

	void clearPropState() {
		in_queue = false;
		dead_rules.clear();
		if (sat.confl) {
			for (int i = 0; i < no_support.size(); i++) {
				for ( ; pufhead[i] < no_support[i].size(); pufhead[i]++) {
					no_support_bool[no_support[i][pufhead[i]]] = false;
				}
				no_support[i].clear();
				ushead[i] = 0;
				pufhead[i] = 0;
			}
		}
	}

};

vec<WellFounded> wf_props;

void add_inductive_rule(BoolView hl, vec<BoolView>& posb, vec<BoolView>& negb, int wf_id) {
	wf_props.growTo(wf_id);
	wf_props[wf_id-1].addRule(hl, posb, negb);
}

void wf_init() {
	for (int i = 0; i < wf_props.size(); i++) wf_props[i].init();
//	exit(0);
}

