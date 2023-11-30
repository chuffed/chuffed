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

#ifndef flatzinc_h
#define flatzinc_h

#include "chuffed/core/engine.h"
#include "chuffed/core/propagator.h"
#include "chuffed/flatzinc/ast.h"
#include "chuffed/support/vec.h"

#include <algorithm>
#include <array>
#include <iostream>
#include <map>
#include <ostream>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <utility>
#include <vector>

extern std::map<IntVar*, std::string> intVarString;
extern std::map<BoolView, std::string> boolVarString;

// Controls whether expressions like bool_sum_eq([x[i] = j | i in 1..n], 1)
// access the underlying literals x[i] = j or new ones via int_eq_reif(...)
// NOTE:    Implemention isn't 100% ideal at this stage so kept it conditional
#define EXPOSE_INT_LITS 0

namespace FlatZinc {

/// Alias for a variable specification
class Alias {
public:
	const int v;
	Alias(int v0) : v(v0) {}
};

/// Optional value
template <class Val>
struct Option {
private:
	bool _some;
	Val _v;

public:
	bool operator()() const { return _some; }
	const Val& some() const { return _v; }
	static Option<Val> none() {
		Option<Val> o;
		o._some = false;
		new (&o._v) Val();
		return o;
	}
	static Option<Val> some(const Val& v) {
		Option<Val> o;
		o._some = true;
		o._v = v;
		return o;
	}
};

/// Base class for variable specifications
class VarSpec {
public:
	/// Whether the variable has an "output" annotation
	bool output;
	/// Whether the variable was introduced in the mzn2fzn translation
	bool introduced;
	/// Whether the variable *looks* introduced by the mzn2fzn translation
	bool looks_introduced;
	/// Destructor
	virtual ~VarSpec() = default;
	/// Variable index
	int i;
	/// Whether the variable aliases another variable
	bool alias;
	/// Whether the variable is assigned
	bool assigned;
	/// Constructor
	VarSpec(bool output0, bool introduced0, bool looks0)
			: output(output0), introduced(introduced0), looks_introduced(looks0) {}
	void set_looks_introduced(bool b) { looks_introduced = b; }
};

/// Specification for integer variables
class IntVarSpec : public VarSpec {
public:
	Option<AST::SetLit*> domain;
	IntVarSpec(const Option<AST::SetLit*>& d, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = false;
		assigned = false;
		domain = d;
	}
	IntVarSpec(int i0, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = false;
		assigned = true;
		i = i0;
	}
	IntVarSpec(const Alias& eq, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = true;
		i = eq.v;
	}
	~IntVarSpec() override {
		if (!alias && !assigned && domain()) {
			delete domain.some();
		}
	}
};

/// Specification for Boolean variables
class BoolVarSpec : public VarSpec {
public:
	Option<AST::SetLit*> domain;
#if EXPOSE_INT_LITS
	// whether it aliases an int literal such as [x <= 5]: (-1=no)
	int alias_var;
	IntRelType alias_irt;
	int alias_val;
#endif
	BoolVarSpec(Option<AST::SetLit*>& d, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = false;
		assigned = false;
		domain = d;
#if EXPOSE_INT_LITS
		alias_var = -1;
#endif
	}
	BoolVarSpec(bool b, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = false;
		assigned = true;
		i = static_cast<int>(b);
#if EXPOSE_INT_LITS
		alias_var = -1;
#endif
	}
	BoolVarSpec(const Alias& eq, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = true;
		i = eq.v;
#if EXPOSE_INT_LITS
		alias_var = -1;
#endif
	}
	~BoolVarSpec() override {
		if (!alias && !assigned && domain()) {
			delete domain.some();
		}
	}
};

/// Specification for set variables
class SetVarSpec : public VarSpec {
public:
	Option<AST::SetLit*> upperBound;
	SetVarSpec(bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = false;
		assigned = false;
		upperBound = Option<AST::SetLit*>::none();
	}
	SetVarSpec(const Option<AST::SetLit*>& v, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = false;
		assigned = false;
		upperBound = v;
	}
	SetVarSpec(AST::SetLit* v, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = false;
		assigned = true;
		upperBound = Option<AST::SetLit*>::some(v);
	}
	SetVarSpec(const Alias& eq, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = true;
		i = eq.v;
	}
	~SetVarSpec() override {
		if (!alias && upperBound()) {
			delete upperBound.some();
		}
	}
};

/// Specification for floating point variables
class FloatVarSpec : public VarSpec {
public:
	Option<std::vector<double>*> domain;
	FloatVarSpec(Option<std::vector<double>*>& d, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = false;
		assigned = false;
		domain = d;
	}
	FloatVarSpec(bool b, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = false;
		assigned = true;
		i = static_cast<int>(b);
	}
	FloatVarSpec(const Alias& eq, bool output, bool introduced, bool looks = false)
			: VarSpec(output, introduced, looks) {
		alias = true;
		i = eq.v;
	}
	~FloatVarSpec() override {
		if (!alias && !assigned && domain()) {
			delete domain.some();
		}
	}
};

/// Abstract representation of a constraint
class ConExpr {
public:
	/// Identifier for the constraint
	std::string id;
	/// Constraint arguments
	AST::Array* args;
	/// Constructor
	ConExpr(std::string id0, AST::Array* args0) : id(std::move(id0)), args(args0) {}
	/// Return argument \a i
	AST::Node* operator[](int i) const { return args->a[i]; }
	/// Destructor
	~ConExpr() { delete args; }
};

/// Map from constraint identifier to constraint posting functions
class Registry {
public:
	/// Type of constraint posting function
	using poster = void (*)(const ConExpr&, AST::Node*);
	/// Add posting function \a p with identifier \a id
	void add(const std::string& id, poster p);
	/// Post constraint specified by \a ce
	void post(const ConExpr& ce, AST::Node* ann);

private:
	/// The actual registry
	std::map<std::string, poster> r;
};

/// Return global registry object
Registry& registry();

/// Symbol table mapping identifiers (strings) to values
template <class Val>
class SymbolTable {
private:
	std::map<std::string, Val> m;

public:
	/// Insert \a val with \a key
	void put(const std::string& key, const Val& val) { m[key] = val; }
	/// Return whether \a key exists, and set \a val if it does exist
	bool get(const std::string& key, Val& val) const {
		typename std::map<std::string, Val>::const_iterator i = m.find(key);
		if (i == m.end()) {
			return false;
		}
		val = i->second;
		return true;
	}
};

class FlatZincSpace : public Problem {
public:
	/// Number of integer variables
	int intVarCount{0};
	/// Number of Boolean variables
	int boolVarCount{0};

	/// The integer variables
	vec<IntVar*> iv;
	/// Indicates whether an integer variable is introduced by mzn2fzn
	std::vector<bool> iv_introduced;
	/// The Boolean variables
	vec<BoolView> bv;
	/// Indicates whether a Boolean variable is introduced by mzn2fzn
	std::vector<bool> bv_introduced;

	vec<BoolView> assumptions;

	AST::Array* output{nullptr};

	// === Experimental `on_restart` support ===
	// Index of the status() variable
	int restart_status = -1;
	// When set to true, the search is marked as complete the next time onRestart() is called
	bool mark_complete = false;
	// Whether any solution has been found
	bool solution_found = false;
	// Whether a solution was found since the last restart
	bool new_solution = false;
	// Definition for variables given uniformly random values on restart
	// (lower bound, upper bound, variable index)
	std::vector<std::array<int, 3>> int_uniform;
	// Definition for solution values stored and assigned on restart
	// (variable index for solution being stored, stored value, variable index being assigned)
	std::vector<std::array<int, 3>> int_sol;
	std::vector<std::tuple<int, bool, int>> bool_sol;
	// Definition for last assigned values stored and assigned on restart
	// (variable index being assigned, value stored)
	// Note that `LastVal` propagators are used to store the values when assigned
	std::vector<std::array<int, 2>> int_last_val;
	std::vector<std::pair<int, bool>> bool_last_val;

	// Method called when a new solution is found.
	// Note this method is a no-op if `int_sol` is empty.
	void storeSolution();
	// Whether storeSolution() should be called
	bool enable_store_solution = false;
	// Method called before the search process is restarted
	// Returns false when the search should be marked as complete
	bool onRestart(Engine* e);
	// Whether onRestart() should be called
	bool enable_on_restart = false;

	// === End `on_restart` ===

	/// Construct problem with given number of variables
	FlatZincSpace(int intVars, int boolVars, int setVars);

	/// Create priority branch group
	PriorityBranchGroup* priorityBranch(vec<Branching*> x, AST::Array* ann, VarBranch var_branch);

	/// Parse the solve annotations and create corresponding branchings
	void parseSolveAnn(AST::Array* ann);
	/// Create final branching that fixes all variables
	void fixAllSearch();

	/// Create new integer variable from specification
	void newIntVar(IntVarSpec* vs, const std::string& name);
	/// Create new Boolean variable from specification
	void newBoolVar(BoolVarSpec* vs);
	/// Create new set variable from specification
	static void newSetVar(SetVarSpec* vs);

	/// Post a constraint specified by \a ce
	static void postConstraint(const ConExpr& ce, AST::Node* annotation);

	/// Post the solve item
	void solve(AST::Array* annotation);
	/// Post that integer variable \a var should be minimized
	void minimize(int var, AST::Array* annotation);
	/// Post that integer variable \a var should be maximized
	void maximize(int var, AST::Array* annotation);

	/// Define output variables
	void setOutputElem(AST::Node* ai) const;
	void setOutput() const;

	void printElem(AST::Node* ai, std::ostream& out = std::cout) const;
	// Needed by the profiler
	void print(std::ostream& out) override {
		if (output == nullptr) {
			return;
		}
		for (auto* ai : output->a) {
			if (ai->isArray()) {
				AST::Array* aia = ai->getArray();
				int size = aia->a.size();
				out << "[";
				for (int j = 0; j < size; j++) {
					printElem(aia->a[j], out);
					if (j < size - 1) {
						out << ", ";
					}
				}
				out << "]";
			} else if (ai->isCall("ifthenelse")) {
				AST::Array* aia = ai->getCall("ifthenelse")->getArgs(3);
				if (aia->a[0]->isBool()) {
					if (aia->a[0]->getBool()) {
						printElem(aia->a[1], out);
					} else {
						printElem(aia->a[2], out);
					}
				} else if (aia->a[0]->isBoolVar()) {
					BoolView b = bv[aia->a[0]->getBoolVar()];
					if (b.isTrue()) {
						printElem(aia->a[1], out);
					} else if (b.isFalse()) {
						printElem(aia->a[2], out);
					} else {
						std::cerr << "% Error: Condition not fixed." << '\n';
					}
				} else {
					std::cerr << "% Error: Condition not Boolean." << '\n';
				}
			} else {
				printElem(ai, out);
			}
		}
	};
	void printStream(std::ostream& out);

	// Needed by the profiler
	void printDomains(std::ostream& out = std::cout) {
		out << "{";
		bool outerFirst = true;

		for (int i = 0; i < iv.size(); i++) {
			if (iv_introduced[i]) {
				continue;
			}

			IntVar* var = iv[i];
			std::string varName = intVarString[var];

			if (varName.empty() || varName.find(so.filter_domains) == std::string::npos) {
				continue;
			}

			if (!outerFirst) {
				out << ",";
			}
			outerFirst = false;

			out << '"' << varName << '"' << ":";
			out << "[";
			if (var->vals != nullptr) {
				bool first = true;
				for (int val = var->getMin(); val <= var->getMax(); val++) {
					if (var->vals[val] != 0) {
						if (!first) {
							out << ",";
						}
						first = false;
						out << val;
					}
				}
			} else {
				out << '[' << var->getMin() << "," << var->getMax() << ']';
			}
			out << "]";
		}

		for (int i = 0; i < bv.size(); i++) {
			if (bv_introduced[i]) {
				continue;
			}

			BoolView bview = bv[i];
			std::string bvstring = boolVarString[bview];

			if (bvstring.find(so.filter_domains) == std::string::npos) {
				continue;
			}

			// TODO: see if this is actually necessary
			if (bvstring.empty()) {
				// Try the other value
				BoolView otherval = bview;
				otherval.setSign(!otherval.getSign());
				bvstring = boolVarString[otherval];
			}

			if (bvstring == "ASSIGNED_AT_ROOT") {
				continue;
			}

			if (!outerFirst) {
				out << ",";
			}
			outerFirst = false;

			out << boolVarString[bview] << ":";
			/* out << litString[toInt(bview.getLit(true))] << ":"; */
			/* out << litString[toInt(bview.getLit(false))] << ":"; */
			bool first = true;
			if (!bview.isFixed()) {
				out << "'undef'";
			} else if (bview.isTrue()) {
				out << "'true'";
			} else if (bview.isFalse()) {
				out << "'false'";
			} else {
				abort();
			}
		}
		out << "}";
	};
	// Needed by the profiler
	std::string getDomainsString() {
		std::stringstream ss;
		printDomains(ss);
		return ss.str();
	}

	// Private membership functions
private:
	/// Auxiliary functions for parsing the solve annotations and creating corresponding branchings
	void parseSolveAnn(AST::Array* ann, BranchGroup* branching, int& nbNonEmptySearchAnnotations);
	void parseSolveAnnAux(AST::Node* elemAnn, BranchGroup* branching,
												int& nbNonEmptySearchAnnotations);
	void parseSolveAnnIntSearch(AST::Node* elemAnn, BranchGroup* branching,
															int& nbNonEmptySearchAnnotations);
	void parseSolveAnnBoolSearch(AST::Node* elemAnn, BranchGroup* branching,
															 int& nbNonEmptySearchAnnotations);
	void parseSolveAnnPrioritySearch(AST::Node* elemAnn, BranchGroup* branching,
																	 int& nbNonEmptySearchAnnotations);
	void parseSolveAnnWarmStart(AST::Node* elemAnn, BranchGroup* branching,
															int& nbNonEmptySearchAnnotations);
};

extern FlatZincSpace* s;

using intvartype = std::pair<std::string, Option<std::vector<int>*>>;
using varspec = std::pair<std::string, VarSpec*>;

/// State of the FlatZinc parser
class ParserState {
public:
	ParserState(const std::string& b, std::ostream& err0)
			: buf(b.c_str()), pos(0), length(b.size()), fg(nullptr), hadError(false), err(err0) {}

	ParserState(const char* buf0, int length0, std::ostream& err0)
			: buf(buf0), pos(0), length(length0), fg(nullptr), hadError(false), err(err0) {}

	void* yyscanner;
	const char* buf;
	unsigned int pos, length;
	FlatZinc::FlatZincSpace* fg;
	std::vector<std::pair<std::string, AST::Node*>> _output;

	SymbolTable<int> intvarTable;
	SymbolTable<int> boolvarTable;
	SymbolTable<int> floatvarTable;
	SymbolTable<int> setvarTable;
	SymbolTable<std::vector<int>> intvararrays;
	SymbolTable<std::vector<int>> boolvararrays;
	SymbolTable<std::vector<int>> floatvararrays;
	SymbolTable<std::vector<int>> setvararrays;
	SymbolTable<std::vector<int>> intvalarrays;
	SymbolTable<std::vector<int>> boolvalarrays;
	SymbolTable<int> intvals;
	SymbolTable<bool> boolvals;
	SymbolTable<AST::SetLit> setvals;
	SymbolTable<std::vector<AST::SetLit>> setvalarrays;

	std::vector<varspec> intvars;
	std::vector<varspec> boolvars;
	std::vector<varspec> setvars;

	std::vector<std::pair<int, int>> last_val_bool;
	std::vector<std::pair<int, int>> last_val_int;

	std::vector<ConExpr*> domainConstraints;
#if EXPOSE_INT_LITS
	// for some reason the above list is posted in reverse order,
	// don't want to disturb things so add the following (forward):
	std::vector<std::pair<ConExpr*, AST::Node*>> domainConstraints2;
#endif

	bool hadError;
	std::ostream& err;

	int fillBuffer(char* lexBuf, unsigned int lexBufSize) {
		if (pos >= length) {
			return 0;
		}
		int num = std::min(length - pos, lexBufSize);
		memcpy(lexBuf, buf + pos, num);
		pos += num;
		return num;
	}

	void output(const std::string& x, AST::Node* n) { _output.emplace_back(x, n); }

	AST::Array* getOutput() {
		std::sort(_output.begin(), _output.end());
		auto* a = new AST::Array();
		for (auto& i : _output) {
			a->a.push_back(new AST::String(i.first + " = "));
			if (i.second->isArray()) {
				AST::Array* oa = i.second->getArray();
				for (auto& j : oa->a) {
					a->a.push_back(j);
					j = nullptr;
				}
				delete i.second;
			} else {
				a->a.push_back(i.second);
			}
			a->a.push_back(new AST::String(";\n"));
		}
		return a;
	}

	void postOnRestartPropagators() {
		fg->bool_last_val.resize(last_val_bool.size());
		for (size_t i = 0; i < last_val_bool.size(); ++i) {
			fg->bool_last_val[i] = std::pair<int, bool>{last_val_bool[i].second, false};
			last_val(&fg->bv[last_val_bool[i].first], &(fg->bool_last_val[i].second));
		}
		fg->int_last_val.resize(last_val_int.size());
		for (size_t i = 0; i < last_val_int.size(); ++i) {
			fg->int_last_val[i] =
					std::array<int, 2>{last_val_int[i].second, fg->iv[last_val_int[i].first]->getMin()};
			last_val(fg->iv[last_val_int[i].first], &(fg->int_last_val[i][1]));
		}
	}
};

/// Exception class for FlatZinc errors
class Error {
private:
	const std::string msg;

public:
	Error(const std::string& where, const std::string& what) : msg(where + ": " + what) {}
	~Error() noexcept = default;
	const std::string& toString() const { return msg; }
};

void solve(const std::string& filename, std::ostream& err = std::cerr);
void solve(std::istream& is, std::ostream& err = std::cerr);

}  // namespace FlatZinc

#endif
