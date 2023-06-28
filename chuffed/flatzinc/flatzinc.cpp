/*
 *  Permission is hereby granted, free of charge, to any person obtaining
 *  a copy of this software and associated documentation files (the
 *  "Software"), to deal in the Software without restriction, including
 *  without limitation the rights to use, copy, modify, merge, publish,
 *  distribute, sublicense, and/or sell copies of the Software, and to
 *  permit persons to whom the Software is furnished to do so, subject to
 *  the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 *  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 *  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 *  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */

#include <chuffed/branching/branching.h>
#include <chuffed/branching/warm-start.h>
#include <chuffed/core/engine.h>
#include <chuffed/flatzinc/flatzinc.h>
#include <chuffed/support/vec.h>

using namespace std;

namespace FlatZinc {

FlatZincSpace* s;

VarBranch ann2ivarsel(AST::Node* ann) {
	if (auto* s = dynamic_cast<AST::Atom*>(ann)) {
		if (s->id == "input_order") {
			return VAR_INORDER;
		}
		if (s->id == "first_fail") {
			return VAR_SIZE_MIN;
		}
		if (s->id == "anti_first_fail") {
			return VAR_SIZE_MAX;
		}
		if (s->id == "smallest") {
			return VAR_MIN_MIN;
		}
		if (s->id == "smallest_largest") {
			return VAR_MAX_MIN;
		}
		if (s->id == "largest") {
			return VAR_MAX_MAX;
		}
		if (s->id == "largest_smallest") {
			return VAR_MIN_MAX;
		}
		if (s->id == "occurrence") {
			return VAR_DEGREE_MAX;
		}
		if (s->id == "most_constrained") {
			return VAR_SIZE_MIN;
		}
		if (s->id == "max_regret") {
			return VAR_REGRET_MIN_MAX;
		}
		if (s->id == "random_order") {
			return VAR_RANDOM;
		}
#ifdef HAS_VAR_IMPACT
		if (s->id == "impact") return VAR_IMPACT;
#endif
	}
	cerr << "% Warning: Unknown or not support variable selection annotation '";
	ann->print(cerr);
	cerr << "'! Ignore variable selection annotation and replace it by 'input_order'." << endl;
	return VAR_INORDER;
}

ValBranch ann2ivalsel(AST::Node* ann) {
	if (auto* s = dynamic_cast<AST::Atom*>(ann)) {
		if (s->id == "default") {
			return VAL_DEFAULT;
		}
		if (s->id == "indomain") {
			return VAL_MIN;
		}
		if (s->id == "indomain_min") {
			return VAL_MIN;
		}
		if (s->id == "indomain_max") {
			return VAL_MAX;
		}
		// if (s->id == "indomain_middle") return VAL_MIDDLE;
		if (s->id == "indomain_middle") {
			CHUFFED_ERROR("The value choice annotation 'indomain_middle' is not supported yet!\n");
		}
		if (s->id == "indomain_median") {
			return VAL_MEDIAN;
		}
		if (s->id == "indomain_split") {
			return VAL_SPLIT_MIN;
		}
		if (s->id == "indomain_reverse_split") {
			return VAL_SPLIT_MAX;
		}
		// if (s->id == "indomain_random") return VAL_RANDOM;
		if (s->id == "indomain_random") {
			CHUFFED_ERROR("The value choice annotation 'indomain_random' is not supported yet!\n");
		}
	}
	std::cerr << "% Warning, ignored search annotation: ";
	ann->print(std::cerr);
	std::cerr << std::endl;
	return VAL_DEFAULT;
}

FlatZincSpace::FlatZincSpace(int intVars, int boolVars, int setVars)
		: intVarCount(0),
			boolVarCount(0),
			iv(intVars),
			iv_introduced(intVars),
			bv(boolVars),
			bv_introduced(boolVars),
			output(nullptr) {
	s = this;
}

void FlatZincSpace::newIntVar(IntVarSpec* vs, const std::string& name) {
	// Resizing of the vectors if required
	if (intVarCount == iv.size()) {
		const int newSize = intVarCount > 0 ? 2 * intVarCount : 1;
		iv.growTo(newSize);
		iv_introduced.resize(newSize);
	}
	bool considerIntroduced = false;
	if (so.use_var_is_introduced) {
		considerIntroduced = vs->introduced;
	} else {
		considerIntroduced = !vs->output;
	}
	if (so.introduced_heuristic && vs->looks_introduced) {
		considerIntroduced = true;
	}
	if (vs->alias) {
		iv[intVarCount++] = iv[vs->i];
	} else {
		IntVar* v = nullptr;
		if (vs->assigned) {
			v = getConstant(vs->i);
		} else if (vs->domain()) {
			AST::SetLit* sl = vs->domain.some();
			if (sl->interval) {
				v = ::newIntVar(sl->min, sl->max);
				intVarString.insert(std::pair<IntVar*, std::string>(v, name));
			} else {
				vec<int> d;
				for (int& i : sl->s) {
					d.push(i);
				}
				sort((int*)d, (int*)d + d.size());
				v = ::newIntVar(d[0], d.last());
				intVarString.insert(std::pair<IntVar*, std::string>(v, name));
				if ((d.last() - d[0] >= d.size() * mylog2(d.size())) ||
						(d.size() <= so.eager_limit && (d.last() - d[0] + 1) > so.eager_limit)) {
					new (v) IntVarSL(*v, d);
				} else {
					if (!v->allowSet(d)) {
						TL_FAIL();
					}
				}
			}
		} else {
			v = ::newIntVar();
		}
		/* std::cerr << "int var: " << intVarCount << " " << v << "\n"; */

		if (so.exclude_introduced && considerIntroduced) {
			v->should_be_learnable = false;
		}
		if (!so.decide_introduced && considerIntroduced) {
			v->should_be_decidable = false;
		}
		iv[intVarCount++] = v;
	}
	iv_introduced[intVarCount - 1] = considerIntroduced;
}

void FlatZincSpace::newBoolVar(BoolVarSpec* vs) {
	// Resizing of the vectors if required
	if (boolVarCount == bv.size()) {
		const int newSize = boolVarCount > 0 ? 2 * boolVarCount : 1;
		bv.growTo(newSize);
		bv_introduced.resize(newSize);
	}
	bool considerIntroduced = false;
	if (so.use_var_is_introduced) {
		considerIntroduced = vs->introduced;
	} else {
		considerIntroduced = !vs->output;
	}
	if (so.introduced_heuristic && vs->looks_introduced) {
		considerIntroduced = true;
	}
	if (vs->alias) {
		bv[boolVarCount++] = bv[vs->i];
	} else {
		BoolView v;
#if EXPOSE_INT_LITS
		if (vs->alias_var >= 0) {
			iv[vs->alias_var]->specialiseToEL();
			switch (vs->alias_irt) {
				case IRT_EQ:
					v = BoolView(iv[vs->alias_var]->getLit(vs->alias_val, LR_EQ));
					break;
				case IRT_NE:
					v = BoolView(iv[vs->alias_var]->getLit(vs->alias_val, LR_NE));
					break;
				case IRT_GE:
					v = BoolView(iv[vs->alias_var]->getLit(vs->alias_val, LR_GE));
					break;
				case IRT_GT:
					v = BoolView(iv[vs->alias_var]->getLit(vs->alias_val + 1, LR_GE));
					break;
				case IRT_LE:
					v = BoolView(iv[vs->alias_var]->getLit(vs->alias_val, LR_LE));
					break;
				case IRT_LT:
					v = BoolView(iv[vs->alias_var]->getLit(vs->alias_val - 1, LR_LE));
					break;
				default:
					NEVER;
			}
		} else
#endif
			v = ::newBoolVar();

		if (vs->assigned) {
			v.setVal(vs->i != 0);
		} else if (vs->domain()) {
			AST::SetLit* sl = vs->domain.some();
			assert(sl->interval);
			assert(sl->min <= 1);
			assert(sl->max >= 0);
			assert(sl->min <= sl->max);
			if (sl->min == 1) {
				v.setVal(true);
			}
			if (sl->max == 0) {
				v.setVal(false);
			}
		}
		if (so.exclude_introduced && considerIntroduced) {
			v.setLearnable(false);
			v.setDecidable(false);
			v.setUIPable(false);
		}
		if (!so.decide_introduced && considerIntroduced) {
			v.setDecidable(false);
		}
		bv[boolVarCount++] = v;
	}
	bv_introduced[boolVarCount - 1] = considerIntroduced;
}

void FlatZincSpace::newSetVar(SetVarSpec* /*unused*/) {
	throw FlatZinc::Error("LazyGeoff", "set variables not supported");
}

void FlatZincSpace::postConstraint(const ConExpr& ce, AST::Node* ann) {
	try {
		registry().post(ce, ann);
	} catch (AST::TypeError& e) {
		throw FlatZinc::Error("Type error", e.what());
	} catch (exception& e) {
		throw FlatZinc::Error("LazyGeoff", e.what());
	}
}

// Parsing the 'int_search' annotation and setting up the branching for it
void FlatZincSpace::parseSolveAnnIntSearch(AST::Node* elemAnn, BranchGroup* branching,
																					 int& nbNonEmptySearchAnnotations) {
	assert(elemAnn->isCall("int_search"));
	try {
		// Retrieval of the data
		AST::Call* call = elemAnn->getCall("int_search");
		AST::Array* args = call->getArgs(4);
		AST::Array* vars = args->a[0]->getArray();
		vec<Branching*> va;
		for (auto& i : vars->a) {
			// Removal of constants
			if (i->isInt()) {
				continue;
			}
			IntVar* v = iv[i->getIntVar()];
			// Removal of fixed variables
			if (v->isFixed()) {
				continue;
			}
			va.push(v);
		}
		branching->add(createBranch(va, ann2ivarsel(args->a[1]), ann2ivalsel(args->a[2])));
		if (auto* s = dynamic_cast<AST::String*>(args->a[3])) {
			if (s->s == "all") {
				so.nof_solutions = 0;
			}
		}
		nbNonEmptySearchAnnotations++;
	} catch (AST::TypeError& e) {
		throw FlatZinc::Error("Type error in int_search annotation", e.what());
	}
}

// Parsing the 'bool_search' annotation and setting up the branching for it
void FlatZincSpace::parseSolveAnnBoolSearch(AST::Node* elemAnn, BranchGroup* branching,
																						int& nbNonEmptySearchAnnotations) {
	assert(elemAnn->isCall("bool_search"));
	try {
		// Retrieval of the data
		AST::Call* call = elemAnn->getCall("bool_search");
		AST::Array* args = call->getArgs(4);
		AST::Array* vars = args->a[0]->getArray();
		vec<Branching*> va(vars->a.size());
		for (int i = vars->a.size(); (i--) != 0;) {
			va[i] = new BoolView(bv[vars->a[i]->getBoolVar()]);
		}
		branching->add(createBranch(va, ann2ivarsel(args->a[1]), ann2ivalsel(args->a[2])));
		if (auto* s = dynamic_cast<AST::String*>(args->a[3])) {
			if (s->s == "all") {
				so.nof_solutions = 0;
			}
		}
		nbNonEmptySearchAnnotations++;
	} catch (AST::TypeError& e) {
		throw FlatZinc::Error("Type error in bool_search annotation", e.what());
	}
}

// Parsing the 'priority_search' annotation and setting up the branching for it
void FlatZincSpace::parseSolveAnnPrioritySearch(AST::Node* elemAnn, BranchGroup* branching,
																								int& nbNonEmptySearchAnnotations) {
	assert(elemAnn->isCall("priority_search"));
	try {
		// Retrieval of the data
		AST::Call* call = elemAnn->getCall("priority_search");
		AST::Array* args = call->getArgs(4);
		AST::Array* vars = args->a[0]->getArray();
		AST::Array* annotations = args->a[1]->getArray();
		// Retrieval of all variables
		// NOTE that constants or fixed variables cannot be removed, because they act as
		// delegates for choosing the branch group to search on next
		vec<Branching*> va;
		for (auto& i : vars->a) {
			// Removal of constants
			IntVar* v = nullptr;
			if (i->isInt()) {
				int value = i->getInt();
				v = getConstant(value);
			} else {
				v = iv[i->getIntVar()];
			}
			va.push(v);
		}
		// Create a new priority branch group and add to branching
		auto* priorityBranching = new PriorityBranchGroup(va, ann2ivarsel(args->a[2]));
		// Parse search annotations
		int nbChildSearchAnnotations = 0;
		parseSolveAnn(annotations, priorityBranching, nbChildSearchAnnotations);
		if (vars->a.size() != nbChildSearchAnnotations) {
			throw FlatZinc::Error("Type error in priority_search annotation",
														"Variable and annotation array must have the same size");
		}
		if (auto* s = dynamic_cast<AST::String*>(args->a[3])) {
			if (s->s == "all") {
				so.nof_solutions = 0;
			}
		}
		branching->add(priorityBranching);
		nbNonEmptySearchAnnotations++;
	} catch (AST::TypeError& e) {
		throw FlatZinc::Error("Type error in priority_search annotation", e.what());
	}
}

void FlatZincSpace::parseSolveAnnWarmStart(AST::Node* elemAnn, BranchGroup* branching,
																					 int& nbNonEmptySearchAnnotations) {
	vec<Lit> decs;
	if (elemAnn->isCall("warm_start_bool")) {
		AST::Call* call = elemAnn->getCall("warm_start_bool");
		AST::Array* args = call->getArgs(2);
		AST::Array* vars = args->a[0]->getArray();
		AST::Array* vals = args->a[1]->getArray();
		if (vars->a.size() != vals->a.size()) {
			fprintf(stderr, "WARNING: length mismatch in warm_start_bool annotation.\n");
		}
		int sz = min(vars->a.size(), vals->a.size());
		for (int ii = 0; ii < sz; ii++) {
			decs.push(bv[vars->a[ii]->getBoolVar()].getLit(vals->a[ii]->getBool()));
		}
	} else {
		AST::Call* call = elemAnn->getCall("warm_start_int");
		AST::Array* args = call->getArgs(2);
		AST::Array* vars = args->a[0]->getArray();
		AST::Array* vals = args->a[1]->getArray();
		if (vars->a.size() != vals->a.size()) {
			fprintf(stderr, "WARNING: length mismatch in warm_start_int annotation.\n");
		}
		int sz = min(vars->a.size(), vals->a.size());
		for (int ii = 0; ii < sz; ii++) {
			IntVar* x(iv[vars->a[ii]->getIntVar()]);
			int k(vals->a[ii]->getInt());
			switch (x->getType()) {
				case INT_VAR_EL:
				case INT_VAR_SL:
					decs.push(x->getLit(k, LR_EQ));
					break;
				default:
					// Fallback. TODO: Do something nicer here.
					BoolView r = ::newBoolVar();
					int_rel_reif(x, IRT_EQ, k, r);
					decs.push(r.getLit(true));
					break;
			}
		}
	}
	branching->add(new WarmStartBrancher(decs));
}

void FlatZincSpace::parseSolveAnnAux(AST::Node* elemAnn, BranchGroup* branching,
																		 int& nbNonEmptySearchAnnotations) {
	if (elemAnn->isCall("int_search")) {
		parseSolveAnnIntSearch(elemAnn, branching, nbNonEmptySearchAnnotations);
	} else if (elemAnn->isCall("bool_search")) {
		parseSolveAnnBoolSearch(elemAnn, branching, nbNonEmptySearchAnnotations);
	} else if (elemAnn->isCall("priority_search")) {
		parseSolveAnnPrioritySearch(elemAnn, branching, nbNonEmptySearchAnnotations);
	} else if (elemAnn->isCall("warm_start_int") || elemAnn->isCall("warm_start_bool")) {
		parseSolveAnnWarmStart(elemAnn, branching, nbNonEmptySearchAnnotations);
	} else {
		throw FlatZinc::Error("Error in search annotation", "Unknown search annotation");
	}
}

// Users should add search annotation with (core vars, default, default) even if they know nothing

// Entry function for parsing the solve annotation
void FlatZincSpace::parseSolveAnn(AST::Array* ann) {
	assumptions.clear();
	int nbNonEmptySearchAnnotations = 0;
	try {
		// Parse the search annotation
		parseSolveAnn(ann, engine.branching, nbNonEmptySearchAnnotations);
	} catch (FlatZinc::Error& e) {
		cerr << "% " << e.toString() << ". Ignore search annotation!" << endl;
		// Removal of successful parsed parts of the search annotation
		engine.branching = new BranchGroup();
		// Reset counter
		nbNonEmptySearchAnnotations = 0;
	}
	// Check whether a search was specified
	if (nbNonEmptySearchAnnotations == 0) {
		if (!so.vsids) {
			so.vsids = true;
			engine.branching->add(&sat);
		}
	}
}

void FlatZincSpace::parseSolveAnn(AST::Array* ann, BranchGroup* branching,
																	int& nbNonEmptySearchAnnotations) {
	if (ann != nullptr) {
		for (auto& i : ann->a) {
			if (i->isCall("restart_none") && so.restart_type_override) {
				so.restart_type = NONE;
			} else if (i->isCall("restart_constant")) {
				AST::Call* call = i->getCall("restart_constant");
				if (so.restart_type_override) {
					so.restart_type = CONSTANT;
				}
				if (so.restart_scale_override) {
					so.restart_scale = static_cast<unsigned int>(call->args->getInt());
				}
			} else if (i->isCall("restart_linear")) {
				AST::Call* call = i->getCall("restart_linear");
				if (so.restart_type_override) {
					so.restart_type = LINEAR;
				}
				if (so.restart_scale_override) {
					so.restart_scale = static_cast<unsigned int>(call->args->getInt());
				}
			} else if (i->isCall("restart_luby")) {
				AST::Call* call = i->getCall("restart_luby");
				if (so.restart_type_override) {
					so.restart_type = LUBY;
				}
				if (so.restart_scale_override) {
					so.restart_scale = static_cast<unsigned int>(call->args->getInt());
				}
			} else if (i->isCall("restart_geometric")) {
				AST::Call* call = i->getCall("restart_geometric");
				if (so.restart_type_override) {
					so.restart_type = GEOMETRIC;
				}
				AST::Array* args = call->getArgs(2);
				if (so.restart_base_override) {
					so.restart_base = args->a[0]->getFloat();
				}
				if (so.restart_base < 1.0) {
					CHUFFED_ERROR("Illegal restart base. Restart count will converge to zero.");
				}
				if (so.restart_scale_override) {
					so.restart_scale = static_cast<unsigned int>(args->a[1]->getInt());
				}
			} else if (i->isCall("assume")) {
				AST::Call* call = i->getCall("assume");
				AST::Array* vars = call->args->getArray();
				for (auto& ii : vars->a) {
					assumptions.push(bv[ii->getBoolVar()]);
				}
			} else if (i->isCall("seq_search") || i->isCall("warm_start_array")) {
				// Get the call
				AST::Call* c = i->getCall();
				// Create a new branch group and add to the branching
				auto* newBranching = new BranchGroup();
				branching->add(newBranching);
				if (c->args->isArray()) {
					// Parse annotation and add to the newly created branching
					int nbChildSearchAnnotations = 0;
					parseSolveAnn(c->args->getArray(), newBranching, nbChildSearchAnnotations);
					if (nbChildSearchAnnotations > 0) {
						nbNonEmptySearchAnnotations++;
					}
				} else {
					// Parse annotation and add to the newly created branching
					parseSolveAnnAux(c->args, newBranching, nbNonEmptySearchAnnotations);
				}
			} else {
				// Parse annotation and add to the branching
				parseSolveAnnAux(i, branching, nbNonEmptySearchAnnotations);
			}
		}
	}
}

void FlatZincSpace::fixAllSearch() {
	vec<Branching*> va;
	for (int i = 0; i < intVarCount; i++) {
		if (iv_introduced[i]) {
			continue;
		}
		IntVar* v = iv[i];
		if (v->isFixed()) {
			continue;
		}
		va.push(v);
	}
	for (int i = 0; i < boolVarCount; i++) {
		if (bv_introduced[i]) {
			continue;
		}
		va.push(new BoolView(bv[i]));
	}
	for (int i = intVarCount; (i--) != 0;) {
		if (!iv_introduced[i]) {
			continue;
		}
		IntVar* v = iv[i];
		if (v->isFixed()) {
			continue;
		}
		va.push(v);
	}
	for (int i = 0; i < boolVarCount; i++) {
		if (!bv_introduced[i]) {
			continue;
		}
		va.push(new BoolView(bv[i]));
	}
	if (va.size() != 0) {
		branch(va, VAR_INORDER, VAL_DEFAULT);
	}
}

void FlatZincSpace::solve(AST::Array* ann) {
	parseSolveAnn(ann);
	fixAllSearch();
}

void FlatZincSpace::minimize(int var, AST::Array* ann) {
	parseSolveAnn(ann);
	optimize(iv[var], OPT_MIN);
	fixAllSearch();
}

void FlatZincSpace::maximize(int var, AST::Array* ann) {
	parseSolveAnn(ann);
	optimize(iv[var], OPT_MAX);
	fixAllSearch();
}

void FlatZincSpace::setOutputElem(AST::Node* ai) const {
	if (ai->isIntVar()) {
		output_var(iv[ai->getIntVar()]);
	} else if (ai->isBoolVar()) {
		output_var(new BoolView(bv[ai->getBoolVar()]));
	}
}

void FlatZincSpace::setOutput() const {
	if (output == nullptr) {
		return;
	}
	for (auto* ai : output->a) {
		if (ai->isArray()) {
			AST::Array* aia = ai->getArray();
			int size = aia->a.size();
			for (int j = 0; j < size; j++) {
				setOutputElem(aia->a[j]);
			}
		} else if (ai->isCall("ifthenelse")) {
			AST::Array* aia = ai->getCall("ifthenelse")->getArgs(3);
			setOutputElem(aia->a[1]);
			setOutputElem(aia->a[2]);
		} else {
			setOutputElem(ai);
		}
	}
}

void FlatZincSpace::printElem(AST::Node* ai, ostream& out) const {
	int k;
	if (ai->isInt(k)) {
		out << k;
	} else if (ai->isIntVar()) {
		out << iv[ai->getIntVar()]->getVal();
	} else if (ai->isBoolVar()) {
		if (bv[ai->getBoolVar()].isTrue()) {
			out << "true";
		} else if (bv[ai->getBoolVar()].isFalse()) {
			out << "false";
		} else {
			out << "false..true";
		}
	} else if (ai->isBool()) {
		out << (ai->getBool() ? "true" : "false");
	} else if (ai->isSet()) {
		AST::SetLit* s = ai->getSet();
		if (s->interval) {
			out << s->min << ".." << s->max;
		} else {
			out << "{";
			for (unsigned int i = 0; i < s->s.size(); i++) {
				out << s->s[i] << (i < s->s.size() - 1 ? ", " : "}");
			}
		}
	} else if (ai->isString()) {
		std::string s = ai->getString();
		for (unsigned int i = 0; i < s.size(); i++) {
			if (s[i] == '\\' && i < s.size() - 1) {
				switch (s[i + 1]) {
					case 'n':
						out << "\n";
						break;
					case '\\':
						out << "\\";
						break;
					case 't':
						out << "\t";
						break;
					default:
						out << "\\" << s[i + 1];
				}
				i++;
			} else {
				out << s[i];
			}
		}
	}
}

void FlatZincSpace::storeSolution() {
	solution_found = true;
	if (!enable_store_solution) {
		return;
	}

	for (auto& i : int_sol) {
		i[1] = iv[i[0]]->getVal();
	}
	for (auto& i : bool_sol) {
		std::get<1>(i) = bv[std::get<0>(i)].isTrue();
	}
	new_solution = true;
}

bool FlatZincSpace::onRestart(Engine* e) {
	if (!enable_on_restart) {
		return false;
	}
	if (mark_complete) {
		return true;
	}

	// Reset Assumptions if not called from constrain()
	if (e->assumptions.size() != 0) {
		if (!solution_found) {
			e->assumptions.clear();
		} else if (e->assumptions.size() > 1) {
			Lit p = e->opt_type != 0 ? e->opt_var->getLit(e->best_sol + 1, LR_GE)
															 : e->opt_var->getLit(e->best_sol - 1, LR_LE);
			e->assumptions.clear();
			e->assumptions.push(toInt(p));
		}
	}

	// Helper functions to create assumptions using value assignments
	auto assume_int_val = [&](IntVar* iv, int v) {
		if (iv->getType() == INT_VAR_LL) {
			e->assumptions.push(toInt(iv->getLit(v, LR_GE)));
			e->assumptions.push(toInt(iv->getLit(v, LR_LE)));
		} else {
			e->assumptions.push(toInt(iv->getLit(v, LR_EQ)));
		}
	};
	auto assume_bool_val = [&](BoolView bv, bool v) {
		BoolView nv = v ? bv : ~bv;
		e->assumptions.push(toInt(nv));
	};

	// Set restart status
	if (restart_status > 0) {
		if (new_solution) {
			assume_int_val(iv[restart_status], 4);  // SAT
		} else if (!solution_found) {
			assume_int_val(iv[restart_status], 1);  // START
		} else {
			assume_int_val(iv[restart_status], 2);  // UNKNOWN
		}
	}

	// Set variables to last captured assignments
	for (const auto& i : int_last_val) {
		assume_int_val(iv[i[0]], i[1]);
	}
	for (const auto& i : bool_last_val) {
		assume_bool_val(bv[i.first], i.second);
	}

	// Set new random values
	for (const auto& i : int_uniform) {
		std::uniform_int_distribution<int> rnd_range(i[0], i[1]);
		assume_int_val(iv[i[2]], rnd_range(engine.rnd));
	}

	// Set last found solutions values
	for (const auto& i : int_sol) {
		assume_int_val(iv[i[2]], i[1]);
	}
	for (const auto& i : bool_sol) {
		assume_bool_val(bv[std::get<2>(i)], std::get<1>(i));
	}

	new_solution = false;
	return false;
}

}  // namespace FlatZinc
