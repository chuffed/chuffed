#ifndef MDD_H_
#define MDD_H_

// #define SPLIT_CACHE
// #define USE_MAP

#include "chuffed/mdd/opcache.h"
#include "chuffed/support/vec.h"

#include <cassert>
#include <map>
#include <unordered_map>
#include <vector>

typedef unsigned int MDDNodeInt;

// _MDD node format: var #edges low {(v_0, d_0), (v_1, d_1), ..., (v_k, d_k)}
// Values [v_0, v_1) -> d_0, [v_1, v_2) -> d_1, etc.
// (-inf, v_0) -> low.
// [v_k, inf) -> d_k.

// Allows negation, with arbitrary domains, and canonicity.

typedef struct {
	int val;
	unsigned int dest;
} MDDEdge;

typedef struct {
	unsigned int var;
	unsigned int sz;

	unsigned int low;  // (-inf,...)
	MDDEdge edges[1];
} MDDNodeEl;

typedef MDDNodeEl* MDDNode;

typedef std::pair<int, MDDNodeInt> edgepair;
typedef std::pair<int, int> intpair;
#define MDDTRUE 1
#define MDDFALSE 0

struct ltnode {
	bool operator()(const MDDNode a1, const MDDNode a2) const {
		assert(0);  // FIXME: out of date.
		return false;
	}
};

struct eqnode {
	bool operator()(const MDDNode a1, const MDDNode a2) const {
		if (a1->var != a2->var) {
			return false;
		}
		if (a1->low != a2->low) {
			return false;
		}
		if (a1->sz != a2->sz) {
			return false;
		}

		for (unsigned int ii = 0; ii < a1->sz; ii++) {
			if (a1->edges[ii].val != a2->edges[ii].val || a1->edges[ii].dest != a2->edges[ii].dest) {
				return false;
			}
		}
		return true;
	}
};

struct hashnode {
	unsigned int operator()(const MDDNode a1) const {
		unsigned int hash = 5381;

		hash = ((hash << 5) + hash) + a1->var;
		hash = ((hash << 5) + hash) + a1->sz;
		hash = ((hash << 5) + hash) + a1->low;

		for (unsigned int ii = 0; ii < a1->sz; ii++) {
			hash = ((hash << 5) + hash) + a1->edges[ii].val;
			hash = ((hash << 5) + hash) + a1->edges[ii].dest;
		}
		return (hash & 0x7FFFFFFF);
	}
};

#ifdef USE_MAP
typedef std::map<const MDDNode, int, ltnode> NodeCache;
#else
typedef std::unordered_map<const MDDNode, int, hashnode, eqnode> NodeCache;
#endif

// class OpCache {
// public:
// 	enum { OP_AND, OP_OR, OP_NOT, OP_BOUND, OP_EXIST, OP_EXPAND, OP_LEQ };

// 	OpCache(unsigned int size);
// 	~OpCache(void);

// 	unsigned int check(char op, unsigned int a, unsigned int b);  // Returns UINT_MAX on failure.
// 	void insert(char op, unsigned int a, unsigned int b, unsigned int res);

// 	typedef struct {
// 		unsigned int hash;
// 		char op;
// 		unsigned int a;
// 		unsigned int b;
// 		unsigned int res;
// 	} cache_entry;

// private:
// 	inline unsigned int hash(char op, unsigned int a, unsigned int b);

// 	// Implemented with sparse-array stuff.
// 	unsigned int tablesz;

// 	unsigned int members;
// 	unsigned int* indices;
// 	cache_entry* entries;
// };

class MDDTable;

class MDD {
public:
	MDD(MDDTable* _table, MDDNodeInt _val) : table(_table), val(_val) {}

	MDD() : table(nullptr), val(-1) {}

	MDDTable* table;
	MDDNodeInt val;
};

class MDDTable {
public:
	enum { OP_AND, OP_OR, OP_NOT, OP_BOUND, OP_EXIST, OP_EXPAND, OP_LEQ };

	MDDTable(int nvars);  // Allows open domain.
	~MDDTable();

	const std::vector<MDDNode>& getNodes() { return nodes; }

	std::vector<int>& getStatus() { return status; }

	void clear_status(MDDNodeInt r);

	void print_node(MDDNodeInt r);
	void print_nodes();
	void print_mdd(MDDNodeInt r);
	static void print_mdd_tikz(MDDNodeInt r);
	static void print_dot(MDDNodeInt r);
	int cache_sz() { return cache.size(); }

	MDDNodeInt insert(unsigned int var, unsigned int low, unsigned int start, bool expand = false);

	template <class T>
	MDDNodeInt tuple(vec<T>& /*tpl*/);
	//   MDDNodeInt tuple(std::vector<int>&);

	MDD vareq(int var, int val) { return MDD(this, mdd_vareq(var, val)); }
	MDD ttt() { return MDD(this, MDDTRUE); }
	MDD fff() { return MDD(this, MDDFALSE); }

	MDDNodeInt mdd_vareq(int var, int val);
	MDDNodeInt mdd_varlt(int var, int val);
	MDDNodeInt mdd_vargt(int var, int val);
	MDDNodeInt mdd_case(int var, std::vector<edgepair>& cases);

	static MDDNodeInt bound(MDDNodeInt /*root*/, vec<intpair>& range);
	MDDNodeInt expand(int var, MDDNodeInt r);

	MDDNodeInt mdd_or(MDDNodeInt /*a*/, MDDNodeInt /*b*/);
	MDDNodeInt mdd_and(MDDNodeInt /*a*/, MDDNodeInt /*b*/);
	MDDNodeInt mdd_not(MDDNodeInt /*root*/);
	bool mdd_leq(MDDNodeInt /*a*/, MDDNodeInt /*b*/);

	MDDNodeInt mdd_exist(MDDNodeInt /*root*/, unsigned int /*var*/);

private:
	static inline MDDNode allocNode(int n_edges);
	static inline void deallocNode(MDDNode node);

	int nvars;

	OpCache opcache;
#ifdef SPLIT_CACHE
	NodeCache* cache;
#else
	NodeCache cache;
#endif

	std::vector<MDDEdge> stack;
	unsigned int intermed_maxsz;
	MDDNode intermed;

	std::vector<MDDNode> nodes;
	std::vector<int> status;
};

MDD operator|(const MDD& a, const MDD& b);
MDD operator&(const MDD& a, const MDD& b);
MDD operator^(const MDD& a, const MDD& b);
MDD operator~(const MDD& r);
MDD mdd_iff(const MDD& a, const MDD& b);
bool operator<=(const MDD& a, const MDD& b);

// Convert the MDD to some other circuit.
template <class F>
F transform_mdd(F fff, F ttt, std::vector<std::vector<F> >& vals, MDDTable& tab, MDDNodeInt node) {
	std::vector<F> cache;
	F ret(transform_mdd(fff, ttt, vals, tab.getNodes(), tab.getStatus(), cache, node));
	tab.clear_status(node);
	return ret;
}

template <class F>
F transform_mdd(F fff, F ttt, std::vector<std::vector<F> >& vals, const std::vector<MDDNode>& nodes,
								std::vector<int>& status, std::vector<F>& cache, MDDNodeInt node) {
	if (node == MDDTRUE) {
		return ttt;
	}
	if (node == MDDFALSE) {
		return fff;
	}

	int n_id = node;
	if (status[n_id] != 0) {
		return cache[status[n_id] - 1];
	}

	F ret = fff;
	assert(nodes[n_id]->low == MDDFALSE);
	for (unsigned int ii = 0; ii < nodes[n_id]->sz - 1; ii++) {
		if (nodes[n_id]->edges[ii].dest == MDDFALSE) {
			continue;
		}
		int low = nodes[n_id]->edges[ii].val;
		int high = nodes[n_id]->edges[ii + 1].val;

		F val = fff;
		for (int v = low; v < high; v++) {
			val = val | vals[nodes[n_id]->var][nodes[n_id]->edges[ii].val];
		}
		ret = ret |
					(val & transform_mdd(fff, ttt, vals, nodes, status, cache, nodes[n_id]->edges[ii].dest));
	}
	cache.push_back(ret);
	status[n_id] = cache.size();

	return ret;
}
#endif
