#include <chuffed/branching/branching.h>
#include <chuffed/core/engine.h>
#include <chuffed/core/propagator.h>
#include <chuffed/globals/mddglobals.h>

#include <cassert>
#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <iostream>
#include <utility>
// #include <chuffed/globals/circglobals.h>
#include <chuffed/mdd/circ_fns.h>
#include <chuffed/support/ParseUtils.h>
#include <chuffed/vars/modelling.h>
// #include <chuffed/hlist.h>
// #include <chuffed/hlutils.h>

#define ROTATE 1
#define REFLECT 2
#define RESTR 4

#include <utility>

// hlist.h
//=======================================
// Some syntactic sugar for cons-cell style lists;
//=======================================
template <class T>
class hlnode {
public:
	int extcount;
	unsigned int length;
	T data;
	hlnode<T>* next;

	hlnode(T _data) : extcount(0), length(1), data(_data), next(NULL) {
		//        fprintf(stdout,"Created: %d\n", _data);
	}

	~hlnode() {
		//      std::cout << "Dead: " << *data << std::endl;
		//      delete data;
		//      data = NULL;

		if (next) {
			(next->extcount)--;
			if (!(next->extcount)) {
				delete next;
				next = nullptr;
			}
		}
	}

	hlnode(T _data, hlnode<T>* _next)
			: extcount(0), length(_next ? _next->length + 1 : 1), data(std::move(_data)), next(_next) {
		if (_next) {
			(_next->extcount)++;
		}
		//        fprintf(stdout,"Created: %d\n", _data);
	}
};

template <class T>
class hlist {
public:
	hlnode<T>* root;

	hlist() : root(nullptr) {}

	hlist<T>& operator=(const hlist<T>& rhs) {
		if (this != &rhs) {
			if (rhs.root) {
				(rhs.root->extcount)++;
			}

			if (root) {
				(root->extcount)--;
				if (!(root->extcount)) {
					delete root;
				}
			}
			root = rhs.root;
		}
		return *this;
	}

	hlist(const hlist<T>& other) : root(other.root) {
		//      std::cout << "CP" << this << std::endl;

		if (root) {
			(root->extcount)++;
		}
	}

	hlist(const T& data, const hlist<T>& other) : root(new hlnode<T>(data, other.root)) {
		if (root) {
			(root->extcount)++;
		}
	}

	hlist(hlnode<T>* _root) : root(_root) {
		//      std::cout << "ND" << this << std::endl;

		if (_root) {
			(_root->extcount)++;
		}
	}

	int length() { return root ? root->length : 0; }

	T el(unsigned int n) {
		assert(root && root->length > n);

		hlnode<T>* curr = root;

		while (n > 0) {
			n++;
			curr = curr->next;
		}

		return curr->data;
	}

	bool is_empty() { return root == nullptr; }

	~hlist() {
		//      std::cout << "DES" << this << std::endl;
		if (root) {
			(root->extcount)--;
			assert(root->extcount >= 0);
			if (!(root->extcount)) {
				delete root;
				root = nullptr;
			}
		}
	}

	//  int count(void)
	//  {
	//     if( root )
	//        return root->extcount;
	//     return 0;
	//  }

	hlist<T> cons(const T el) {
		//      hlnode<T>* next = new hlnode<T>(el,root);
		//      return hlist<T>(next);
		return hlist<T>(el, root);
	}

	T head() {
		assert(root);
		return root->data;
	}

	hlist<T> tail() {
		assert(root);

		return hlist<T>(root->next);
	}

	hlist<T> operator+(hlist<T> other) { return hlist<T>(concat(root, other.root)); }

	bool operator==(hlist<T>& other) {
		hlnode<T>* a = root;
		hlnode<T>* b = other.root;

		while (a != b) {
			if (!a || !b) {
				return false;
			}
			if (a->data != b->data) {
				return false;
			}

			a = a->next;
			b = b->next;
		}
		return true;
	}
};

template <class T>
hlnode<T>* concat(hlnode<T>* a, hlnode<T>* b) {
	if (!a) {
		return b;
	}

	return new hlnode<T>(a->data, concat(a->next, b));
}

template <class T>
hlist<T> cons(T data, const hlist<T>& old) {
	return hlist<T>(data, old);
}

template <class T>
T head(hlist<T> old) {
	return old.head();
}

template <class T>
hlist<T> tail(hlist<T> old) {
	return old.tail();
}

template <class T>
static hlist<T> reversep(hlist<T> old, hlist<T> acc) {
	if (old.is_empty()) {
		return acc;
	}
	return reversep(tail(old), cons(head(old), acc));
}

template <class T>
hlist<T> reverse(hlist<T> old) {
	return reversep(old, hlist<T>());
}

template <class T>
static T max(hlist<T> list, T acc) {
	if (head(list) > acc) {
		return max(tail(list), head(list));
	}

	return max(tail(list), acc);
}

template <class T>
T max(hlist<T> list) {
	assert(!list.is_empty());
	return max(tail(list), head(list));
}

template <class T>
hlist<T> array2hl(const T* array, unsigned int sz) {
	hlist<T> ret;

	for (int offset = sz - 1; offset >= 0; offset--) {
		ret = cons(array[offset], ret);
	}

	return ret;
}

template <class T>
std::ostream& operator<<(std::ostream& out, hlist<T> list) {
	// if (list.is_empty())
	// {
	//     out << "[]";
	// } else {
	//     out << "(" << head(list) << "," << tail(list) << ")";
	// }
	out << "[";
	bool first = true;
	while (!list.is_empty()) {
		if (first) {
			first = false;
		} else {
			out << ",";
		}
		//        out << head(list) << ":" << list.count();
		out << head(list);
		list = tail(list);
	}
	out << "]";
	return out;
}

// hlutils.h
template <class T>
hlist<T> vec2hl(vec<T>& vs) {
	hlist<T> in;
	for (int i = vs.size() - 1; i >= 0; i--) {
		in = cons(vs[i], in);
	}
	return in;
}

template <class T>
void hl2vec(hlist<T> hl, vec<T>& out, bool first = true) {
	if (first) {
		out.clear();
	}

	if (hl.is_empty()) {
		return;
	}

	out.push(head(hl));
	hl2vec(tail(hl), out, false);
}

template <class T1, class T2>
hlist<T1> map(T1 (*fn)(T2), hlist<T2> in) {
	if (in.is_empty()) {
		return hlist<T1>();
	}

	return cons(fn(head(in)), map(fn, tail(in)));
}

template <class T>
hlist<T> filter(bool (*fn)(hlist<T>), hlist<T> list) {
	if (list.is_empty()) {
		return list;
	}

	if (fn(head(list))) {
		return cons(head(list), filter(fn, tail(list)));
	}
	return filter(fn, tail(list));
}

template <class T1, class T2>
T1 foldl(T1 (*fn)(T1, T2), hlist<T2> list, T1 acc) {
	if (list.is_empty()) {
		return acc;
	}

	return (fn, tail(list), fn(acc, head(list)));
}

template <class T1, class T2>
T1 foldr(T1 (*fn)(T1, T2), hlist<T2> list, T1 init) {
	if (list.is_empty()) {
		return init;
	}

	return fn(foldr(fn, tail(list), init), head(list));
}

template <class T>
hlist<hlist<T> > transpose(hlist<hlist<T> > primal) {
	if (primal.is_empty()) {
		return hlist<hlist<T> >();
	}

	return cons(map<T, hlist<T> >(head, primal), transpose(map<hlist<T>, hlist<T> >(tail, primal)));
}

// Consider whether this needs to use the copy
// constructor.
template <class T>
hlist<T> replicate(int n, T el) {
	hlist<T> res;
	while (n > 0) {
		res = cons(el, res);
		n--;
	}
	return res;
}

//============================================

class Opts {
public:
	Opts() : reflect(true), rotate(true), restr(false), symbreak(false) {}

	bool reflect;
	bool rotate;
	bool restr;
	bool symbreak;
};

// combine(a, bs) === zipWith (:) a bs
// Adds each element of a to the beginning of each list b.
template <class T>
hlist<hlist<T> > combine(hlist<T> a, hlist<hlist<T> > b) {
	if (a.is_empty() || b.is_empty()) {
		return hlist<hlist<T> >();
	}
	return cons(cons(head(a), head(b)), combine(tail(a), tail(b)));
}

// Code for rotating a matrix.
template <class T>
hlist<hlist<T> > rotatePr(hlist<hlist<T> > original, hlist<hlist<T> > acc) {
	if (original.is_empty()) {
		return acc;
	}

	return rotatePr(tail(original), combine(head(original), acc));
}

template <class T>
hlist<hlist<T> > rotate(hlist<hlist<T> > original) {
	assert(!original.is_empty());

	return rotatePr(original, replicate(head(original).length(), hlist<T>()));
}

// Pentominoes
// =============
// In this context, we assume the width has already been padded.
//
// Given a shape, we generate the pattern for the regex to match.
hlist<int> pent_seq(int width, hlist<hlist<int> > pattern) {
	//   std::cout << pattern << std::endl;
	if (pattern.is_empty()) {
		return hlist<int>();
	}

	if (pattern.length() == 1) {
		return head(pattern);
	}
	return head(pattern) +
				 (replicate(width - head(pattern).length(), 0) + pent_seq(width, tail(pattern)));
}

static hlist<intpair> pentDFApr(hlist<int> pattern, int node) {
	// Assumes leading 0s and garbage state has been handled.
	assert(node > 1);

	if (pattern.is_empty()) {
		return cons(intpair(node, 1), hlist<intpair>());
	}

	return cons(intpair(head(pattern) == 0 ? node + 1 : 1, head(pattern) == 1 ? node + 1 : 1),
							pentDFApr(tail(pattern), node + 1));
}

static hlist<intpair> pentDFA(hlist<int> pattern, int node = 0) {
	assert(!pattern.is_empty());

	// Handle garbage state.
	if (node == 1) {
		return cons(intpair(1, 1), pentDFA(pattern, node + 1));
	}

	if (head(pattern) == 0) {
		return cons(intpair(node != 0 ? node + 1 : node + 2, 1), pentDFA(tail(pattern), node + 1));
	}

	if (node == 0) {
		return cons(intpair(0, 2), cons(intpair(1, 1), pentDFApr(tail(pattern), 2)));
	}
	return cons(intpair(node, node + 1), pentDFApr(tail(pattern), node + 1));
}

static MDD pentFD(MDDTable& tab, int domain, int val, int height, int width,
									hlist<hlist<int> > pattern, Opts& opts) {
	hlist<int> pentseq;
	hlist<intpair> dfa;
	MDD pentmdd = tab.fff();

	MDD restr = tab.ttt();

	//  if( flags&RESTR )
	//  {
	//     std::vector<unsigned int> doms;
	//     for( int i = 0; i < height*width; i++ )
	//         doms.push_back(domain);

	//     for( int i = 0; i < height; i++ )
	//     {
	//        for( int j = 0; j < width-1; j++ )
	//        {
	//           restr = tab.mdd_and( tab.mdd_not( doms, tab.mdd_vareq((i*width + j),domain - 1) ),
	//           restr );
	//        }
	//        restr = tab.mdd_and( tab.mdd_vareq( ((i+1)*width)-1,domain - 1 ), restr );
	//     }
	//  }

	for (int i = 0; i < 4; i++) {
		if (pattern.length() <= height && head(pattern).length() < width) {
			pentseq = pent_seq(width, pattern);
			dfa = pentDFA(pentseq);

			//         std::vector<dfa_trans> transition;
			vec<vec<int> > transition;
			int count = 0;
			while (!dfa.is_empty()) {
				intpair node = head(dfa);

				assert(transition.size() == count);
				transition.push();
				for (int v = 0; v < domain; v++) {
					// NOLINTBEGIN
					assert(transition.last().size() == v);
					if (v == val) {
						/*
						 dfa_trans t = {
								count,      // Current node
								v,          // Value
								node.second // Destination
						 };
						 transition.push_back(t);
						 */
						transition.last().push(node.second + 1);
					} else {
						/*
						 dfa_trans t = {
								count,      // Current node
								v,          // Value
								node.first  // Destination
						 };
						 transition.push_back(t);
						 */
						transition.last().push(node.first + 1);
					}
					// NOLINTEND
				}

				dfa = tail(dfa);
				count++;
			}

			vec<int> accepts;
			// accepts.push_back(count-1);
			accepts.push(count);
			int q0 = 1;
			MDD orientation =
					MDD(&tab, fd_regular(tab, height * width, count + 1, transition, q0, accepts, false));
			pentmdd = (restr & orientation) | pentmdd;
		}

		if (!(opts.rotate)) {
			break;
		}
		pattern = rotate(pattern);  // Next layout
	}

	if (opts.reflect) {
		pattern = reverse(pattern);  // Reflection

		for (int i = 0; i < 4; i++) {
			if (pattern.length() <= height && head(pattern).length() < width) {
				pentseq = pent_seq(width, pattern);
				dfa = pentDFA(pentseq);

				// std::vector<dfa_trans> transition;
				vec<vec<int> > transition;
				int count = 0;
				while (!dfa.is_empty()) {
					intpair node = head(dfa);

					assert(transition.size() == count);
					transition.push();
					for (int v = 0; v < domain; v++) {
						// NOLINTBEGIN
						assert(transition.last().size() == v);
						if (v == val) {
							/*
							 dfa_trans t = {
									count,      // Current node
									v,          // Value
									node.second // Destination
							 };
							 transition.push_back(t);
							 */
							transition.last().push(node.second + 1);

						} else {
							/*
							 dfa_trans t = {
									count,      // Current node
									v,          // Value
									node.first  // Destination
							 };
							 transition.push_back(t);
							 */
							transition.last().push(node.first + 1);
						}
						// NOLINTEND
					}

					dfa = tail(dfa);
					count++;
				}

				vec<int> accepts;
				// accepts.push_back(count-1);
				// pentmdd = tab.mdd_or( tab.mdd_and( restr, fd_regular(tab, domain, height*width, count,
				// transition, accepts)),
				//                         pentmdd );
				accepts.push(count);
				int q0 = 1;
				MDD orientation =
						MDD(&tab, fd_regular(tab, height * width, count + 1, transition, q0, accepts, false));
				pentmdd = (restr & orientation) | pentmdd;
			}

			if (!(opts.rotate)) {
				break;
			}

			pattern = rotate(pattern);  // Next layout
		}
	}

	//   assert( pentmdd != MDDFALSE );
	return pentmdd;
}

class Pent : public Problem {
public:
	Pent(Opts& opts) {
		MDDOpts mopts;
		// == Read shapes. ==
		gzFile file(gzdopen(0, "rb"));
		Parse::StreamBuffer in(file);

		hlist<hlist<hlist<int> > > shapes;
		hlist<int> counts;

		height = Parse::parseInt(in);
		width = Parse::parseInt(in);
		int nshapes = 0;
		while (*in != EOF) {
			Parse::skipWhitespace(in);
			while (*in == '#') {
				Parse::skipLine(in);
			}
			int r = Parse::parseInt(in);
			int c = Parse::parseInt(in);
			(void)c;

			//      parseInt(in);
			int count = Parse::parseInt(in);
			counts = cons(count, counts);
			nshapes += count;
			Parse::skipLine(in);

			hlist<hlist<int> > shape;

			for (int i = 0; i < r; i++) {
				hlist<int> row;
				while (*in != '\n') {
					row = cons(*in == 'x' || *in == 'X' ? 1 : 0, row);
					++in;
				}
				shape = cons(reverse(row), shape);
				Parse::skipLine(in);
				while (*in == '\n') {
					skipLine(in);
				}
			}

			shapes = cons(reverse(shape), shapes);
		}

		// Set-up variables
		// height*width variables, domain 0..nshapes-1.
		createVars(xs, height * width, 0, nshapes - 1);

		// Dead column.
		vec<IntVar*> deadcol;
		createVars(deadcol, height, nshapes, nshapes);

		// Keep shapes reversed, so shape # is shapes.length()-1.

		vec<IntVar*> inst;
		for (int r = 0; r < height; r++) {
			for (int c = 0; c < width; c++) {
				inst.push(xs[r * width + c]);
			}
			inst.push(deadcol[r]);
		}

		int shapeid = nshapes - 1;
		while (!shapes.is_empty()) {
			// Remember to correct for extra column.
			int reps = head(counts);
			for (int rep = 0; rep < reps; rep++) {
				//         std::cout << "START:" << shapeid << std::endl;
				MDDTable tab((width + 1) * height);

				MDD b(pentFD(tab, nshapes + 1, shapeid, height, width + 1, head(shapes), opts));

				addMDD(inst, b, mopts);

				shapeid--;
			}
			shapes = tail(shapes);
			counts = tail(counts);

			//      if( shapes.length() == 1 )
			//          break;
		}

		// Setup extra column.

		//  vec<Lit> dead;
		//  dead.push(Lit(0,0));
		//  for( int i = 0; i < height; i++ )
		//  {
		//     dead[0] = Lit(deadcol[i][dom-1],1);
		//     S.addClause(dead);
		//  }

		//  for( int i = 0; i < width*height; i++ )
		//  {
		//      dead[0] = Lit(sets[i][dom-1],0);
		//      S.addClause(dead);
		//  }

		// Handle symmetry breaking.

		/*
		if( symbreak )
		{
			 MDDTable htab(2*width, dom);
			 vec<Lit> syminst;
			 vec<int> symdom;
			 std::vector<unsigned int> sa;
			 std::vector<unsigned int> sb;

			 // Vertical reflection
			 for( int i = 0; i < width; i++ )
			 {
					symdom.push(dom);
					symdom.push(dom);
					sa.push_back(2*i);
					sb.push_back(2*i+1);

					for( unsigned int j = 0; j < dom; j++ )
					{
						 syminst.push(Lit(sets[i][j],1));
					}
					for( unsigned int j = 0; j < dom; j++ )
					{
						 syminst.push(Lit(sets[(height-1)*width + i][j],1));
					}
			 }

			 MDD hmdd = fd_lexlt(htab,dom,sa,sb);
			 int hinst( S.newMDDProp(htab,symdom,hmdd) );
			 S.addMDDInst(hinst,syminst,symdom,0);

			 // Rotation
			 syminst.clear();
			 for( int i = 0; i < width; i++ )
			 {
					for( unsigned int j = 0; j < dom; j++ )
					{
						 syminst.push(Lit(sets[i][j],1));
					}
					for( unsigned int j = 0; j < dom; j++ )
					{
						 syminst.push(Lit(sets[height*width - i - 1][j],1));
					}
			 }
			 S.addMDDInst(hinst,syminst,symdom,0);

			 // Horizontal reflection
			 MDDTable vtab(2*height, dom);
			 sa.clear();
			 sb.clear();
			 syminst.clear();
			 symdom.clear();

			 for( int i = 0; i < height; i++ )
			 {
					symdom.push(dom);
					symdom.push(dom);
					sa.push_back(2*i);
					sb.push_back(2*i+1);

					for( unsigned int j = 0; j < dom; j++ )
					{
						 syminst.push(Lit(sets[width*i][j],1));
					}
					for( unsigned int j = 0; j < dom; j++ )
					{
						 syminst.push(Lit(sets[width*(i+1)-1][j],1));
					}
			 }

			 MDD vmdd = fd_lexlt(vtab,dom,sa,sb);
			 int vinst( S.newMDDProp(vtab,symdom,vmdd) );
			 S.addMDDInst(vinst,syminst,symdom,0);
		}
	 */
		branch(xs, VAR_INORDER, VAL_MIN);
		output_vars(xs);
	}

	void print(std::ostream& os) override {
		int xi = 0;
		for (int ri = 0; ri < height; ri++) {
			bool first = true;
			os << "[";
			for (int ci = 0; ci < width; ci++) {
				os << (first ? "" : ", ");
				os << (char)('A' + xs[xi]->getVal());
				first = false;
				xi++;
			}
			os << "]\n";
		}
	}

	// Data
	int width;
	int height;

	// Variables
	vec<IntVar*> xs;
};

int main(int argc, char** argv) {
	Opts opts;

	int i;
	int j;
	for (i = j = 0; i < argc; i++) {
		if (strcmp(argv[i], "-noreflect") == 0) {
			opts.reflect = false;
		} else if (strcmp(argv[i], "-norotate") == 0) {
			opts.rotate = false;
		} else if (strcmp(argv[i], "-norestr") == 0) {
			opts.restr = false;
		} else if (strcmp(argv[i], "-sym") == 0) {
			opts.symbreak = true;
		} else {
			argv[j++] = argv[i];
		}
	}

	argc = j;
	parseOptions(argc, argv);

	Problem* p(new Pent(opts));
	engine.solve(p);
}
