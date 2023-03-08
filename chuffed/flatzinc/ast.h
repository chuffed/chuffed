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

#ifndef ast_h
#define ast_h

#include <cstdlib>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

/**
 * \namespace FlatZinc::AST
 * \brief Abstract syntax trees for the %FlatZinc interpreter
 */

namespace FlatZinc {
namespace AST {

class Call;
class Array;
class SetLit;

/// Exception signaling type error
class TypeError {
private:
	const char* _what = nullptr;

public:
	TypeError() {}
	TypeError(const char* what) : _what(what) {}
	std::string what() const {
		if (_what != nullptr) {
			std::string what = _what;
			return what;
		}
		return "";
	};
};

/**
 * \brief A node in a FlatZinc abstract syntax tree
 */
class Node {
public:
	/// Destructor
	virtual ~Node();

	/// Append \a n to an array node
	void append(Node* n);

	/// Test if node has atom with \a id
	bool hasAtom(const std::string& id);
	/// Test if node is int, if yes set \a i to the value
	bool isInt(int& i);
	/// Test if node is function call with \a id
	bool isCall(const std::string& id);
	/// Return function call
	Call* getCall();
	/// Test if node is function call or array containing function call \a id
	bool hasCall(const std::string& id);
	/// Return function call \a id
	Call* getCall(const std::string& id);
	/// Cast this node to an array node
	Array* getArray();
	/// Cast this node to an integer variable node
	int getIntVar();
	/// Cast this node to a Boolean variable node
	int getBoolVar();
	/// Cast this node to a set variable node
	int getSetVar();

	/// Cast this node to an integer node
	int getInt();
	/// Cast this node to a Boolean node
	bool getBool();
	/// Cast this node to a Float node
	double getFloat();
	/// Cast this node to a set literal node
	SetLit* getSet();

	/// Cast this node to a string node
	std::string getString();

	/// Test if node is an integer variable node
	bool isIntVar();
	/// Test if node is a Boolean variable node
	bool isBoolVar();
	/// Test if node is a set variable node
	bool isSetVar();
	/// Test if node is an integer node
	bool isInt();
	/// Test if node is a Boolean node
	bool isBool();
	/// Test if node is a string node
	bool isString();
	/// Test if node is an array node
	bool isArray();
	/// Test if node is a set literal node
	bool isSet();

	/// Output string representation
	virtual void print(std::ostream&) = 0;
};

/// Boolean literal node
class BoolLit : public Node {
public:
	bool b;
	BoolLit(bool b0) : b(b0) {}
	void print(std::ostream& os) override { os << "b(" << (b ? "true" : "false") << ")"; }
};
/// Integer literal node
class IntLit : public Node {
public:
	int i;
	IntLit(int i0) : i(i0) {}
	void print(std::ostream& os) override { os << "i(" << i << ")"; }
};
/// Float literal node
class FloatLit : public Node {
public:
	double d;
	FloatLit(double d0) : d(d0) {}
	void print(std::ostream& os) override { os << "f(" << d << ")"; }
};
/// Set literal node
class SetLit : public Node {
public:
	bool interval;
	int min;
	int max;
	std::vector<int> s;
	SetLit() {}
	SetLit(int min0, int max0) : interval(true), min(min0), max(max0) {}
	SetLit(std::vector<int> s0) : interval(false), s(std::move(s0)) {}
	bool empty() const { return ((interval && min > max) || (!interval && s.empty())); }
	void print(std::ostream& os) override { os << "s()"; }
};

/// Variable node base class
class Var : public Node {
public:
	int i;
	Var(int i0) : i(i0) {}
};
/// Boolean variable node
class BoolVar : public Var {
public:
	BoolVar(int i0) : Var(i0) {}
	void print(std::ostream& os) override { os << "xb(" << i << ")"; }
};
/// Integer variable node
class IntVar : public Var {
public:
	IntVar(int i0) : Var(i0) {}
	void print(std::ostream& os) override { os << "xi(" << i << ")"; }
};
/// Float variable node
class FloatVar : public Var {
public:
	FloatVar(int i0) : Var(i0) {}
	void print(std::ostream& os) override { os << "xf(" << i << ")"; }
};
/// Set variable node
class SetVar : public Var {
public:
	SetVar(int i0) : Var(i0) {}
	void print(std::ostream& os) override { os << "xs(" << i << ")"; }
};

/// Array node
class Array : public Node {
public:
	std::vector<Node*> a;
	Array(std::vector<Node*> a0) : a(std::move(a0)) {}
	Array(Node* n) : a(1) { a[0] = n; }
	Array(int n = 0) : a(n) {}
	void print(std::ostream& os) override {
		os << "[";
		for (unsigned int i = 0; i < a.size(); i++) {
			a[i]->print(os);
			if (i < a.size() - 1) {
				os << ", ";
			}
		}
		os << "]";
	}
	~Array() override {
		for (int i = a.size(); (i--) != 0;) {
			delete a[i];
		}
	}
};

/// Node representing a function call
class Call : public Node {
public:
	std::string id;
	Node* args;
	Call(std::string id0, Node* args0) : id(std::move(id0)), args(args0) {}
	~Call() override { delete args; }
	void print(std::ostream& os) override {
		os << id << "(";
		args->print(os);
		os << ")";
	}
	Array* getArgs(unsigned int n) const {
		Array* a = args->getArray();
		if (a->a.size() != n) {
			throw TypeError("arity mismatch");
		}
		return a;
	}
};

/// Node representing an array access
class ArrayAccess : public Node {
public:
	Node* a;
	Node* idx;
	ArrayAccess(Node* a0, Node* idx0) : a(a0), idx(idx0) {}
	~ArrayAccess() override {
		delete a;
		delete idx;
	}
	void print(std::ostream& os) override {
		a->print(os);
		os << "[";
		idx->print(os);
		os << "]";
	}
};

/// Node representing an atom
class Atom : public Node {
public:
	std::string id;
	Atom(std::string id0) : id(std::move(id0)) {}
	void print(std::ostream& os) override { os << id; }
};

/// String node
class String : public Node {
public:
	std::string s;
	String(std::string s0) : s(std::move(s0)) {}
	void print(std::ostream& os) override { os << "s(\"" << s << "\")"; }
};

inline Node::~Node() {}

inline void Node::append(Node* newNode) {
	auto* a = dynamic_cast<Array*>(this);
	if (a == nullptr) {
		std::cerr << "type error" << std::endl;
		std::exit(-1);
	}
	a->a.push_back(newNode);
}

inline bool Node::hasAtom(const std::string& id) {
	if (auto* a = dynamic_cast<Array*>(this)) {
		for (int i = a->a.size(); (i--) != 0;) {
			if (Atom* at = dynamic_cast<Atom*>(a->a[i])) {
				if (at->id == id) {
					return true;
				}
			}
		}
	} else if (Atom* a = dynamic_cast<Atom*>(this)) {
		return a->id == id;
	}
	return false;
}

inline bool Node::isCall(const std::string& id) {
	if (Call* a = dynamic_cast<Call*>(this)) {
		if (a->id == id) {
			return true;
		}
	}
	return false;
}

inline Call* Node::getCall() {
	if (Call* a = dynamic_cast<Call*>(this)) {
		return a;
	}
	throw TypeError("call expected");
}

inline bool Node::hasCall(const std::string& id) {
	if (auto* a = dynamic_cast<Array*>(this)) {
		for (int i = a->a.size(); (i--) != 0;) {
			if (Call* at = dynamic_cast<Call*>(a->a[i])) {
				if (at->id == id) {
					return true;
				}
			}
		}
	} else if (Call* a = dynamic_cast<Call*>(this)) {
		return a->id == id;
	}
	return false;
}

inline bool Node::isInt(int& i) {
	if (auto* il = dynamic_cast<IntLit*>(this)) {
		i = il->i;
		return true;
	}
	return false;
}

inline Call* Node::getCall(const std::string& id) {
	if (auto* a = dynamic_cast<Array*>(this)) {
		for (int i = a->a.size(); (i--) != 0;) {
			if (Call* at = dynamic_cast<Call*>(a->a[i])) {
				if (at->id == id) {
					return at;
				}
			}
		}
	} else if (Call* a = dynamic_cast<Call*>(this)) {
		if (a->id == id) {
			return a;
		}
	}
	throw TypeError("call expected");
}

inline Array* Node::getArray() {
	if (auto* a = dynamic_cast<Array*>(this)) {
		return a;
	}
	throw TypeError("array expected");
}

inline int Node::getIntVar() {
	if (auto* a = dynamic_cast<IntVar*>(this)) {
		return a->i;
	}
	throw TypeError("integer variable expected");
}
inline int Node::getBoolVar() {
	if (auto* a = dynamic_cast<BoolVar*>(this)) {
		return a->i;
	}
	throw TypeError("bool variable expected");
}
inline int Node::getSetVar() {
	if (auto* a = dynamic_cast<SetVar*>(this)) {
		return a->i;
	}
	throw TypeError("set variable expected");
}
inline int Node::getInt() {
	if (auto* a = dynamic_cast<IntLit*>(this)) {
		return a->i;
	}
	throw TypeError("integer literal expected");
}
inline bool Node::getBool() {
	if (auto* a = dynamic_cast<BoolLit*>(this)) {
		return a->b;
	}
	throw TypeError("bool literal expected");
}
inline double Node::getFloat() {
	if (auto* a = dynamic_cast<FloatLit*>(this)) {
		return a->d;
	}
	throw TypeError("float literal expected");
}
inline SetLit* Node::getSet() {
	if (auto* a = dynamic_cast<SetLit*>(this)) {
		return a;
	}
	throw TypeError("set literal expected");
}
inline std::string Node::getString() {
	if (auto* a = dynamic_cast<String*>(this)) {
		return a->s;
	}
	throw TypeError("string literal expected");
}
inline bool Node::isIntVar() { return (dynamic_cast<IntVar*>(this) != nullptr); }
inline bool Node::isBoolVar() { return (dynamic_cast<BoolVar*>(this) != nullptr); }
inline bool Node::isSetVar() { return (dynamic_cast<SetVar*>(this) != nullptr); }
inline bool Node::isInt() { return (dynamic_cast<IntLit*>(this) != nullptr); }
inline bool Node::isBool() { return (dynamic_cast<BoolLit*>(this) != nullptr); }
inline bool Node::isSet() { return (dynamic_cast<SetLit*>(this) != nullptr); }
inline bool Node::isString() { return (dynamic_cast<String*>(this) != nullptr); }
inline bool Node::isArray() { return (dynamic_cast<Array*>(this) != nullptr); }

inline Node* extractSingleton(Node* n) {
	if (auto* a = dynamic_cast<Array*>(n)) {
		if (a->a.size() == 1) {
			Node* ret = a->a[0];
			a->a[0] = nullptr;
			delete a;
			return ret;
		}
	}
	return n;
}

}  // namespace AST
}  // namespace FlatZinc

#endif
