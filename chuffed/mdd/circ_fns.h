#ifndef CIRC_FNS_H_
#define CIRC_FNS_H_
#include "chuffed/support/vec.h"

#include <cassert>

enum CardOp { CARD_EQ, CARD_LE, CARD_GE };

// lb <= sum (i \in [start..end-1]) args[i] <= ub.
template <class T>
T card_range(T fff, vec<T>& args, unsigned int start, unsigned int end, unsigned int lb,
						 unsigned int ub) {
	assert((int)start < args.size());
	assert((int)end <= args.size());

	if ((int)ub > args.size() - 1) {
		ub = args.size() - 1;
	}

	// Should be able to formulate without, but... whatever.
	T ttt(~fff);

	vec<T> counts;
	for (unsigned int cc = 0; cc <= ub; cc++) {
		if (cc >= lb) {
			counts.push(ttt);
		} else {
			counts.push(fff);
		}
	}

	for (int ii = end - 1; ii >= ((int)start); ii--) {
		for (unsigned int cc = 0; cc < ub; cc++) {
			counts[cc] = (args[ii] & counts[cc + 1]) | ((~args[ii]) & counts[cc]);
		}
		counts[ub] = (~args[ii]) & counts[ub];
	}

	return counts[0];
}

// sum args[i] OP k.
template <class T>
T card(T fff, vec<T>& args, CardOp op, unsigned int k) {
	unsigned int lb = 0;
	unsigned int ub = args.size() - 1;

	switch (op) {
		case CARD_LE:
			ub = k;
			break;
		case CARD_GE:
			lb = k;
			break;
		case CARD_EQ:
			lb = k;
			ub = k;
			break;
	}
	return card_range(fff, args, 0, args.size(), lb, ub);
}

// This is going to be TERRIBLE with NNF.
// As in, definitely not GAC.
// For DNNF, should convert to a DFA and then unroll.
template <class T>
T sequence(T fff, vec<T>& args, unsigned int l, unsigned int u, unsigned int window) {
	if (args.size() < window) {
		return card_range(fff, args, 0, args.size(), l, u);
	}

	assert(window > 0);

	T ret(~fff);
	//  for( int ii = args.size()-window; ii >= 0; ii-- )
	for (unsigned int ii = 0; ii < args.size() - window + 1; ii++) {
		ret = ret & (card_range(fff, args, ii, ii + window, l, u));
	}

	return ret;
}
#endif
