#include <chuffed/core/propagator.h>
#include <chuffed/vars/modelling.h>

// a[i] forms a circuit
// Value consistent propagator

template <int U = 0>
class Circuit : public Propagator {
public:
	bool const useCheck;       // use the 'check' algorithm
	bool const usePrevent;     // use the 'prevent' algorithm
	bool const useScc;         // use the 'scc' algorithm
	bool const pruneRoot;      // use 'prune root' option for scc algorithm
	bool const pruneSkip;      // prune arcs that skip subtrees (in scc)
	bool const fixReq;         // fix required back edges (in scc)
	bool const generaliseScc;  // use 'prune within' option for scc

	int const size;  // total number of nodes

	IntView<U>* const x;  // successor variables

	// Persistent state

	// Intermediate state
	vec<int> new_fixed;

	vec<int> prev;     // scc alg - vars in last subtree visited
	vec<int> earlier;  // scc alg - vars in the earlier subtrees
	vec<int> later;    // scc alg - vars in later subtrees

	vec<int> preRoot;  // contains indices of all vars collapsed into root node
	int root;

	// struct for recording propagations to be done
	struct PROP {
		Clause* reason;
		int var;   // the variable whose domain will be changed
		int val;   // the relevant domain member
		bool fix;  // true - use setVal, false - use remVal
	};

	vec<PROP> propQueue;

	int* index;
	int* lowlink;

	int nodesSeen;

	// for prevent algorithm
	int* end;
	int* lengthChain;

	Circuit(vec<IntView<U> > _x)
			: useCheck(so.circuitalg < 4),
				usePrevent(so.circuitalg >= 2 && so.circuitalg < 4),
				useScc(so.circuitalg >= 3),
				pruneRoot(so.sccoptions >= 3),
				pruneSkip(true),
				fixReq(true),
				generaliseScc(so.sccoptions == 2 || so.sccoptions == 4),
				size(_x.size()),
				x(_x.release()) {
		priority = 5;
		new_fixed.reserve(size);
		prev.reserve(size);
		earlier.reserve(size);
		later.reserve(size);
		index = (int*)malloc(size * sizeof(int));
		lowlink = (int*)malloc(size * sizeof(int));
		end = (int*)malloc(size * sizeof(int));
		lengthChain = (int*)malloc(size * sizeof(int));

		if (useScc) {
			for (int i = 0; i < size; i++) {
				x[i].attach(this, i, EVENT_C);
			}
		} else {
			for (int i = 0; i < size; i++) {
				x[i].attach(this, i, EVENT_F);
			}
		}
	}

	void wakeup(int i, int c) override {
		if ((c & EVENT_F) != 0) {
			new_fixed.push(i);
		}
		pushInQueue();
	}

	// 'prevent' algorithm
	// Prunes that partial assigned paths are not completed to cycles
	bool cyclePrevent() {
		// The path starting at assigned x[i] ends at x[end[j]] which is
		// not assigned.
		for (int i = 0; i < size; i++) {
			end[i] = -1;
			lengthChain[i] = -1;
		}

		for (int unfixedVar = 0; unfixedVar < size; unfixedVar++) {
			if (!x[unfixedVar].isFixed()) {
				// Non-assigned views serve as starting points for assigned paths
				// Try all connected values
				for (typename IntView<U>::iterator it = x[unfixedVar].begin(); it != x[unfixedVar].end();
						 ++it) {
					// Starting point for not yet followed assigned path found
					int j0 = *it;

					if (x[j0].isFixed() && (lengthChain[j0] < 0)) {
						// Follow assigned path until non-assigned view:
						// all assigned view on the paths can be skipped, as
						// if x[i] is assigned to j, then x[j] will only have
						// x[i] as predecessor due to propagating distinct.
						int j = j0;
						int chainLength = 1;
						do {
							j = x[j].getVal();
							chainLength++;
						} while (x[j].isFixed());

						// Now there cannot be a link from x[j] to x[j0]
						// so record the chain length and we will propagate afterwards
						lengthChain[j0] = chainLength;
						end[j0] = j;
					}
				}
			}
		}
		// now propagate the disallowed links we found
		for (int j0 = 0; j0 < size; j0++) {
			if (lengthChain[j0] > 0) {
				Clause* r = nullptr;
				if (so.lazy) {
					if (so.prevexpl == 1) {
						r = Reason_new(lengthChain[j0]);
						int j = j0;
						for (int index = 1; index < lengthChain[j0]; index++) {
							(*r)[index] = x[j].getValLit();
							j = x[j].getVal();
						}
					} else {
						// find the vars in the start of the chain and those not in the chain
						vec<int> inStartChain;
						vec<int> outside;
						for (int i = 0; i < size; i++) {
							if (i != end[j0]) {
								outside.push(i);
							}
						}
						int j = j0;
						for (int index = 1; index < lengthChain[j0]; index++) {
							inStartChain.push(j);
							outside.remove(j);
							j = x[j].getVal();
						}
						assert(inStartChain.size() + outside.size() + 1 == size);
						// reason is nothing in start of chain can reach outside chain
						r = Reason_new(inStartChain.size() * outside.size() + 1);
						explainAcantreachB(r, 1, 1 + inStartChain.size() * outside.size(), inStartChain,
															 outside);
					}
				}
				if (x[end[j0]].remValNotR(j0)) {
					// fprintf(stderr, "setting %d != %d\n", end[j0], j0);
					if (!x[end[j0]].remVal(j0, r)) {
						return false;
					}
				}
			}
		}

		return true;
	}

	// Add literals to reason to explain that no node in set A
	// reaches a node in set B
	// If there's a node a1 in A and a node b1 in B, the literal
	// involving those nodes is not included
	// checks the index after the last literal is added
	// (for debugging purposes)
	void explainAcantreachB(Clause* reason, int reasonIndex, int expectedEndIndex, vec<int> A,
													vec<int> B, int a1 = -1, int b1 = -1) {
		// fprintf(stderr, "explaining");
		bool found = false;
		for (int a = 0; a < A.size(); a++) {
			assert(A[a] < size && A[a] >= 0);
			for (int b = 0; b < B.size(); b++) {
				assert(B[b] < size && B[b] >= 0);
				if (A[a] != a1 || B[b] != b1) {
					assert(!x[A[a]].indomain(B[b]));
					//  fprintf(stderr, "add %d not equal to %d\n", A[a], B[b]);
					(*reason)[reasonIndex++] = ~x[A[a]].getLit(B[b], 0);
				} else {
					found = true;
				}
			}
		}
		assert(found || (a1 == -1 && b1 == -1));
		assert(reasonIndex == expectedEndIndex);
	}

	void addEqLits(Clause* r) {
		if (so.rootSelection == 5 || so.rootSelection == 6) {
			for (int i = 0; i < preRoot.size(); i++) {
				(*r)[i + 1] = x[preRoot[i]].getValLit();
			}
		}
	}

	void addPropagation(bool fix, int var, int val, Clause* r) {
		PROP newprop;
		newprop.reason = r;
		newprop.var = var;
		newprop.val = val;
		newprop.fix = fix;
		propQueue.push(newprop);
	}

	bool exploreSubtree(int thisNode, int startPrevSubtree, int endPrevSubtree, int* backfrom,
											int* backto, int* numback) {
		// fprintf(stderr,"exploring subtree\n");
		index[thisNode] = nodesSeen++;
		lowlink[thisNode] = index[thisNode];
		bool isFirstChild = true;
		int child;
		for (typename IntView<U>::iterator i = x[thisNode].begin(); i != x[thisNode].end(); ++i) {
			child = *i;
			// If we haven't visited the child yet, do so now
			if (index[child] == -1) {
				// fprintf(stderr,"new child %d\n", child);
				if (!exploreSubtree(child, startPrevSubtree, endPrevSubtree, backfrom, backto, numback)) {
					return false;  // fail if there was an scc contained within this child
				}

				if (lowlink[child] < lowlink[thisNode]) {
					lowlink[thisNode] = lowlink[child];
				}

				// If this is the first child and its lowlink is equal to the
				// parent's index, we can prune the edge from this node to the
				// child (as the circuit must come back up through an edge
				// from the child subtree to this node and therefore we can't
				// touch this node on the way down).
				// We can also prune any edges from a node outside the child's
				// subtree to this node, with the same reason.
				if (generaliseScc && isFirstChild && lowlink[child] == index[thisNode]) {
					// fprintf(stderr, "gen\n");
					//  XXX [AS] Commented following line, because propagator related statistics
					//  should be collected within the propagator class.
					// engine.prunedGeneralise++;
					//  The reason is that no node in the child's subtree reaches
					//  a node outside the subtree that isn't the parent
					//  First divide the nodes into those inside and outside
					//  the child's subtree
					vec<int> inside;
					vec<int> outside;
					for (int i = 0; i < size; i++) {
						if (index[i] >= index[child]) {
							inside.push(i);
						} else if (i != thisNode) {
							outside.push(i);
						}
					}

					assert(outside.size() > 0);
					assert(inside.size() + outside.size() == size - 1);
					/*fprintf(stderr, " this node is %d, it's index is %d\n", thisNode, index[thisNode]);
					fprintf(stderr, "inside:\n");
					for(int i = 0; i < inside.size(); i++)
							fprintf(stderr, "node %d with index %d\n", inside[i], index[inside[i]]);
					fprintf(stderr, "outside:\n");
					for(int i = 0; i < outside.size(); i++)
							fprintf(stderr, "node %d with index %d\n", outside[i], index[outside[i]]);        */
					Clause* r = nullptr;
					if (so.lazy) {
						r = Reason_new(inside.size() * outside.size() + 1 + preRoot.size());
						addEqLits(r);
						explainAcantreachB(r, preRoot.size() + 1,
															 inside.size() * outside.size() + 1 + preRoot.size(), inside,
															 outside);
					}
					addPropagation(false, thisNode, child, r);

					for (int i = 0; i < outside.size(); i++) {
						if (x[outside[i]].remValNotR(thisNode)) {
							// fprintf(stderr, "setting x[%d] neq %d\n", outside[i], thisNode);
							addPropagation(false, outside[i], thisNode, r);
						}
					}
				}

				isFirstChild = false;  // We've now visited at least one child
			} else                   // This is a node we've seen before
			{
				// fprintf(stderr,"old child %d\n", child);
				//  If child is within the last subtree we've found a backedge (from this node to the child)
				if (index[child] >= startPrevSubtree && index[child] <= endPrevSubtree) {
					// fprintf(stderr, "found back edge from %d to %d\n", thisNode, child);
					// If this is an edge back to a root node which isn't the first
					// then it will be pruned by alldiff later, so just ignore it
					if (index[child] != 0 || child == root) {
						(*numback)++;
						*backfrom = thisNode;
						*backto = child;
					}
				}

				// If w is from a subtree before the previous one prune this edge (if that option is set)
				else if (pruneSkip && index[child] < startPrevSubtree) {
					// XXX [AS] Commented following line, because propagator related statistics
					// should be collected within the propagator class.
					// engine.prunedSkip++;
					Clause* r = nullptr;
					if (so.lazy) {
						// The reason is that no node in an earlier subtree can
						// reach the prev or later subtrees, and no node
						// in the prev subtree can reach later subtrees.
						vec<int> prevAndLater;
						prevAndLater.reserve(prev.size() + later.size());
						for (int i = 0; i < prev.size(); i++) {
							prevAndLater.push(prev[i]);
						}
						for (int i = 0; i < later.size(); i++) {
							prevAndLater.push(later[i]);
						}
						r = Reason_new(earlier.size() * prevAndLater.size() + prev.size() * later.size() + 1 +
													 preRoot.size());
						addEqLits(r);
						int size1 = prev.size() * later.size();
						int size2 = earlier.size() * prevAndLater.size();
						explainAcantreachB(r, preRoot.size() + 1, 1 + size1 + preRoot.size(), prev, later);
						explainAcantreachB(r, preRoot.size() + 1 + size1, 1 + size1 + size2 + preRoot.size(),
															 earlier, prevAndLater);
					}
					addPropagation(false, thisNode, child, r);
				}

				if (index[child] < lowlink[thisNode]) {
					lowlink[thisNode] = index[child];
				}
			}
			// fprintf(stderr,"lowpoint is %d\n", lowlink[thisNode]);
		}

		// Fail if there's an scc rooted here
		if (lowlink[thisNode] == index[thisNode]) {
			// fprintf(stderr, "multi scc\n");
			//  XXX [AS] Commented following line, because propagator related statistics
			//  should be collected within the propagator class.
			// engine.multipleSCC++;
			Clause* r = nullptr;
			if (so.lazy) {
				// The reason is that no node in the subtree rooted by this node (including this one)
				// reaches a node outside that subtree.
				// Start by finding the nodes inside and outside the subtree
				vec<int> inside;
				vec<int> outside;
				for (int i = 0; i < size; i++) {
					if (index[i] >= index[thisNode]) {
						inside.push(i);
					} else {
						outside.push(i);
					}
				}
				/*fprintf(stderr, "nodes inside scc rooted at %d:\n", thisNode);
				for(int i = 0; i < inside.size(); i++)
						fprintf(stderr, "%d", inside[i]);
				fprintf(stderr, "nodes outside scc:\n");
				for(int i = 0; i < outside.size(); i++)
						fprintf(stderr, "%d with index %d", outside[i], index[i]);*/

				r = Reason_new(inside.size() * outside.size() + preRoot.size());
				addEqLits(r);
				explainAcantreachB(r, 1 + preRoot.size(), inside.size() * outside.size() + preRoot.size(),
													 inside, outside, inside[0], outside[0]);
				x[inside[0]].setVal(outside[0], r);
			}
			return false;
		}

		return true;
	}

	//(1-first non-fixed, 2-random non-fixed, 3-end of shortest chain, 4-end of longest chain,
	// 5- start of shortest chain (+ collapse), 6-start of longest chain (+collapse))
	// 7- first (even if fixed), 8 - random (even if fixed), 9-largest domain, 10-all
	int chooseRoot() {
		vec<int> chainStarts;  // indices which no var is fixed to
		for (int i = 0; i < size; i++) {
			chainStarts.push(i);
		}
		for (int i = 0; i < size; i++) {
			if (x[i].isFixed()) {
				chainStarts.remove(x[i].getVal());
			}
		}

		// if there are no chain starts everything is fixed, so just return
		// if we haven't already run check, do that first
		if (chainStarts.size() == 0) {
			return -1;
		}

		// now for each chain find the length and the end variable
		vec<int> chainLengths;
		vec<int> chainEnds;
		for (int i = 0; i < chainStarts.size(); i++) {
			int length = 1;
			int currIndex = chainStarts[i];
			while (x[currIndex].isFixed()) {
				length++;
				currIndex = x[currIndex].getVal();
			}
			chainLengths.push(length);
			chainEnds.push(currIndex);
		}

		root = -1;
		int len;
		int chosenChain;
		switch (so.rootSelection) {
			case 1:  // first non-fixed
				for (int i = 0; i < size; i++) {
					if (!x[i].isFixed()) {
						root = i;
						break;
					}
				}
				break;
			case 2:  // random non-fixed
			{
				// has to be one of the chain ends
				std::uniform_int_distribution<int> rnd_ce(0, chainEnds.size() - 1);
				chosenChain = rnd_ce(engine.rnd);
				// fprintf(stderr, "chose %d\n", chosenChain);
				root = chainEnds[chosenChain];
				// fprintf(stderr, "root is %d\n", root);
			} break;
			case 3:  // end of shortest chain,
				len = chainLengths[0];
				root = chainEnds[0];
				for (int i = 1; i < chainLengths.size(); i++) {
					if (chainLengths[i] < len) {
						len = chainLengths[i];
						root = chainEnds[i];
					}
				}
				break;
			case 4:  // end of longest chain,
				len = chainLengths[0];
				root = chainEnds[0];
				for (int i = 1; i < chainLengths.size(); i++) {
					if (chainLengths[i] > len) {
						len = chainLengths[i];
						root = chainEnds[i];
					}
				}
				break;
			case 5:  // start of shortest chain (+ collapse)
				len = chainLengths[0];
				root = chainStarts[0];
				chosenChain = 0;
				for (int i = 1; i < chainLengths.size(); i++) {
					if (chainLengths[i] < len) {
						len = chainLengths[i];
						root = chainStarts[i];
						chosenChain = i;
					}
				}
				break;
			case 6:  // start of longest chain (+collapse)
				len = chainLengths[0];
				root = chainStarts[0];
				chosenChain = 0;
				for (int i = 1; i < chainLengths.size(); i++) {
					if (chainLengths[i] > len) {
						len = chainLengths[i];
						root = chainStarts[i];
						chosenChain = i;
					}
				}
				break;
			case 7:  // first (even if fixed)
				root = 0;
				break;
			case 8:  // random (even if fixed)
			{
				std::uniform_int_distribution<int> rnd_node(0, size - 1);
				root = rnd_node(engine.rnd);
			} break;
			case 9:  // largest domain
				len = x[0].size();
				root = 0;
				for (int i = 1; i < size; i++) {
					if (x[i].size() > len) {
						len = x[i].size();
						root = i;
					}
				}
				break;
		}
		assert(root >= 0);
		return root;
	}

	bool circuitSCC(int rootEnd) {
		root = rootEnd;
		int backfrom = 0;  // the last back edge found
		int backto = 0;
		int numback = 0;  // the number of back edges found

		vec<int> thisSubtree;

		if (so.lazy) {
			thisSubtree.reserve(size);
			prev.clear();
			earlier.clear();
			later.clear();
		}

		for (int i = 0; i < size; i++) {
			index[i] = -1;  // unvisited
		}

		index[root] = 0;  // first node visited
		lowlink[root] = 0;
		nodesSeen = 1;  // only seen root node
		if (so.rootSelection == 5 || so.rootSelection == 6) {
			preRoot.clear();
			while (x[rootEnd].isFixed()) {
				// fprintf(stderr, "preroot %d\n", rootEnd);
				preRoot.push(rootEnd);
				rootEnd = x[rootEnd].getVal();
				index[rootEnd] = 0;
				nodesSeen++;
				lowlink[rootEnd] = 0;
			}
		}
		// fprintf(stderr, "rootEnd %d\n", rootEnd);
		propQueue.clear();

		// original subtree is just the root node
		int startSubtree = 0;
		int endSubtree = 0;

		// explore children of the root node
		for (typename IntView<U>::iterator i = x[rootEnd].begin(); i != x[rootEnd].end(); ++i) {
			int child = *i;

			if (index[child] == -1)  // if haven't explored this yet
			{
				numback = 0;
				if (!exploreSubtree(child, startSubtree, endSubtree, &backfrom, &backto, &numback)) {
					// fprintf(stderr, "failed in subtree\n");
					return false;  // fail if we found a scc within the child
				}

				// Find the nodes in the subtree we just explored and the ones still to be explored
				if (so.lazy) {
					thisSubtree.clear();
					later.clear();
					for (int i = 0; i < size; i++) {
						if (index[i] < 0) {
							later.push(i);
						} else if (index[i] > endSubtree) {
							thisSubtree.push(i);
						}
					}
				}

				// If there's no edge from the new subtree back to the previous one, fail
				if (numback == 0) {
					// XXX [AS] Commented following line, because propagator related statistics
					// should be collected within the propagator class.
					// engine.nobackedge++;
					if (so.lazy) {
						// If prev is empty then this is the first subtree,
						// and we just need to say that the nodes in this
						// subtree can't reach the unexplored nodes or the root.
						if (prev.size() == 0) {
							vec<int> alloutside;
							for (int i = 0; i < later.size(); i++) {
								alloutside.push(later[i]);
							}
							alloutside.push(root);
							assert(thisSubtree.size() + alloutside.size() + preRoot.size() == size);
							Clause* r = Reason_new(thisSubtree.size() * alloutside.size() + preRoot.size());
							addEqLits(r);
							// This subtree can't reach outside
							explainAcantreachB(r, 1 + preRoot.size(),
																 thisSubtree.size() * alloutside.size() + preRoot.size(),
																 thisSubtree, alloutside, thisSubtree[0], alloutside[0]);
							x[thisSubtree[0]].setVal(alloutside[0], r);

							return false;
						}

						// Assuming we have at least one previous subtree,
						// the reason we're failing is that
						// 1. nodes in earlier subtrees can't reach the
						// previous one this one or unexplored ones,
						// 2. nodes in the previous subtree can't reach
						// this one or unexplored ones,
						// 3. and nodes in this subtree can't reach the
						// previous one or unexplored ones.
						vec<int> prev_later;
						for (int i = 0; i < prev.size(); i++) {
							prev_later.push(prev[i]);
						}
						for (int i = 0; i < later.size(); i++) {
							prev_later.push(later[i]);
						}
						vec<int> prev_this_later;
						for (int i = 0; i < prev_later.size(); i++) {
							prev_this_later.push(prev_later[i]);
						}
						for (int i = 0; i < thisSubtree.size(); i++) {
							prev_this_later.push(thisSubtree[i]);
						}
						vec<int> this_later;
						for (int i = 0; i < thisSubtree.size(); i++) {
							this_later.push(thisSubtree[i]);
						}
						for (int i = 0; i < later.size(); i++) {
							this_later.push(later[i]);
						}

						int size1 = earlier.size() * prev_this_later.size();
						int size2 = prev.size() * this_later.size();
						int size3 = thisSubtree.size() * prev_later.size();
						assert(prev_later.size() > 0);
						assert(earlier.size() + prev.size() + later.size() + thisSubtree.size() +
											 preRoot.size() ==
									 size - 1);
						Clause* r = Reason_new(size1 + size2 + size3 + preRoot.size());
						addEqLits(r);
						// 1. Earlier can't reach prev, this or later
						explainAcantreachB(r, 1 + preRoot.size(), 1 + size1 + preRoot.size(), earlier,
															 prev_this_later);

						// 2. Prev can't reach this or later
						explainAcantreachB(r, 1 + size1 + preRoot.size(), 1 + size1 + size2 + preRoot.size(),
															 prev, this_later);

						// 3. this can't reach prev or unexplored
						explainAcantreachB(r, 1 + size1 + size2 + preRoot.size(),
															 size1 + size2 + size3 + preRoot.size(), thisSubtree, prev_later,
															 thisSubtree[0], prev_later[0]);
						x[thisSubtree[0]].setVal(prev_later[0], r);
					}
					return false;
				}

				// If there's only one, the back edge is required (only propagate if the option is set)
				if (fixReq && numback == 1) {
					// XXX [AS] Commented following line, because propagator related statistics
					// should be collected within the propagator class.
					// engine.fixedBackedge++;
					Clause* r = nullptr;
					if (so.lazy) {
						// If this is the first subtree, the reason we're setting this link is that
						// there is no other link between nodes of this subtree to nodes outside the subtree
						// including the root
						if (prev.size() == 0) {
							vec<int> alloutside;
							for (int i = 0; i < later.size(); i++) {
								alloutside.push(later[i]);
							}
							alloutside.push(root);
							r = Reason_new(thisSubtree.size() * alloutside.size() + preRoot.size());
							addEqLits(r);
							assert(thisSubtree.size() + alloutside.size() + preRoot.size() == size);

							// This subtree can't reach outside (except backfrom to backto)
							explainAcantreachB(r, 1 + preRoot.size(),
																 thisSubtree.size() * alloutside.size() + preRoot.size(),
																 thisSubtree, alloutside, backfrom, backto);
							// fprintf(stderr, "first subtree\n");

						} else {
							// Otherwise we have at least one previous subtree.
							// The reason is the same as when failing above
							vec<int> prev_later;
							for (int i = 0; i < prev.size(); i++) {
								prev_later.push(prev[i]);
							}
							for (int i = 0; i < later.size(); i++) {
								prev_later.push(later[i]);
							}
							vec<int> prev_this_later;
							for (int i = 0; i < prev_later.size(); i++) {
								prev_this_later.push(prev_later[i]);
							}
							for (int i = 0; i < thisSubtree.size(); i++) {
								prev_this_later.push(thisSubtree[i]);
							}
							vec<int> this_later;
							for (int i = 0; i < thisSubtree.size(); i++) {
								this_later.push(thisSubtree[i]);
							}
							for (int i = 0; i < later.size(); i++) {
								this_later.push(later[i]);
							}

							int size1 = earlier.size() * prev_this_later.size();
							int size2 = prev.size() * this_later.size();
							int size3 = thisSubtree.size() * prev_later.size();
							assert(prev_later.size() > 0);
							r = Reason_new(size1 + size2 + size3 + preRoot.size());
							addEqLits(r);
							// 1. Earlier can't reach prev, this or unexplored
							explainAcantreachB(r, 1 + preRoot.size(), 1 + size1 + preRoot.size(), earlier,
																 prev_this_later);

							// 2. Prev can't reach this or unexplored
							explainAcantreachB(r, 1 + size1 + preRoot.size(), 1 + size1 + size2 + preRoot.size(),
																 prev, this_later);

							// 3. this can't reach prev or unexplored (except for the one we're setting)
							explainAcantreachB(r, 1 + size1 + size2 + preRoot.size(),
																 size1 + size2 + size3 + preRoot.size(), thisSubtree, prev_later,
																 backfrom, backto);

							assert(earlier.size() + prev.size() + later.size() + thisSubtree.size() +
												 preRoot.size() ==
										 size - 1);
						}
					}
					addPropagation(true, backfrom, backto, r);
				}

				// When a new subtree has been explored, update the prev, earlier and later vectors (only
				// necessary if explaining)
				if (so.lazy) {
					for (int i = 0; i < prev.size(); i++) {
						earlier.push(prev[i]);
					}
					prev.clear();
					for (int i = 0; i < thisSubtree.size(); i++) {
						prev.push(thisSubtree[i]);
					}
				}

				// Set the new subtree boundaries
				startSubtree = endSubtree + 1;
				endSubtree = nodesSeen - 1;
			}
		}

		// If we haven't reached all of the nodes the graph is disconnected so circuit fails
		if (nodesSeen != size) {
			// XXX [AS] Commented following line, because propagator related statistics
			// should be collected within the propagator class.
			// engine.disconnected++;
			Clause* r = nullptr;

			if (so.lazy) {
				// need to say that each seen node doesn't reach any non-seen node
				// first find the seen and not-seen nodes
				vec<int> seen;
				vec<int> notseen;

				for (int var = 0; var < size; var++) {
					if (index[var] >= 0) {
						seen.push(var);
					} else {
						notseen.push(var);
					}
				}
				int numNotSeen = notseen.size();
				assert(seen.size() == nodesSeen);
				assert(numNotSeen + nodesSeen == size);

				// Now build the reason - seen can't reach notseen (but don't include the last literal)
				r = Reason_new(nodesSeen * numNotSeen);
				explainAcantreachB(r, 1, nodesSeen * numNotSeen, seen, notseen, seen[0], notseen[0]);
				x[seen[0]].setVal(notseen[0], r);
			}
			// fprintf(stderr, "disconnected (seen %d out of %d)\n", nodesSeen, size);
			return false;
		}

		// If we're pruning root edges and there was more than one subtree,
		// prune edges from the root to earlier subtrees
		if (pruneRoot && startSubtree > 1) {
			// Build the reason if neccessary (it will be the same for all of the pruned edges)
			Clause* r = nullptr;
			if (so.lazy) {
				// First find the nodes in the last subtree and those in the earlier ones
				vec<int> lastSubtree;
				vec<int> earlierSubtree;
				for (int i = 0; i < size; i++) {
					if (index[i] >= startSubtree) {
						lastSubtree.push(i);
					} else if (index[i] > 0) {  // The root is considered in no subtree
						earlierSubtree.push(i);
					}
				}

				// Reason should state that no var in an earlier sub tree reaches a var
				// in the last subtree
				r = Reason_new(earlierSubtree.size() * lastSubtree.size() + 1 + preRoot.size());
				addEqLits(r);
				explainAcantreachB(r, 1 + preRoot.size(),
													 earlierSubtree.size() * lastSubtree.size() + 1 + preRoot.size(),
													 earlierSubtree, lastSubtree);
			}

			// Prune all edges from the root to nodes in earlier subtrees
			for (typename IntView<U>::iterator i = x[rootEnd].begin(); i != x[rootEnd].end(); ++i) {
				if (index[*i] < startSubtree) {
					// XXX [AS] Commented following line, because propagator related statistics
					// should be collected within the propagator class.
					// engine.prunedRoot++;
					addPropagation(false, rootEnd, *i, r);
				}
			}
		}

		// Perform the propagations
		for (int i = 0; i < propQueue.size(); i++) {
			PROP p = propQueue[i];
			// fprintf(stderr, "propagating\n");
			if (p.fix) {
				if (x[p.var].setValNotR(p.val)) {
					if (!x[p.var].setVal(p.val, p.reason)) {
						return false;
					}
				}
			} else {
				if (x[p.var].remValNotR(p.val)) {
					if (!x[p.var].remVal(p.val, p.reason)) {
						return false;
					}
				}
			}
		}
		return true;
	}

	bool propagate() override {
		// fprintf(stderr, "started propagation\n");
		/*for(int i = 0; i < new_fixed.size(); i++)
				fprintf(stderr, "%d is newly fixed to %d\n", new_fixed[i], x[new_fixed[i]].getVal());*/
		assert(useCheck || useScc);  // prevent on its own is not sufficient

		if (useCheck && !testSmallCycle()) {
			// fprintf(stderr, "finished propagation\n");
			return false;
		}
		if (usePrevent && !cyclePrevent()) {
			// fprintf(stderr, "finished propagation\n");
			return false;
		}
		if (useScc) {
			if (so.rootSelection == 10) {
				// try all roots
				for (int root = 0; root < size; root++) {
					if (!circuitSCC(root)) {
						return false;
					}
				}
			} else {
				int root = chooseRoot();
				if (root < 0)  // means all vars are fixed
				{
					if (!useCheck) {
						return testSmallCycle();
					}
					return true;
				}
				if (!circuitSCC(root)) {
					return false;
				}
			}
		}
		// fprintf(stderr, "finished propagation\n");
		return true;
	}

	bool testSmallCycle() {
		// fprintf(stderr, "testing\n");
		bool foundSmallCycle = false;
		vec<int> bestCycle;
		double bestScore;  // we'll choose the highest

		// for each newly fixed variable, follow the chain and if you end up back
		// at that variable without reaching all nodes you've found a small cycle
		vec<int> thisCycle;
		double thisScore;
		bool thisIsCycle;
		while (new_fixed.size() > 0) {
			int startVar = new_fixed[0];
			int nextVar = startVar;
			thisCycle.clear();
			thisScore = 0;
			thisIsCycle = false;
			bool noScoreYet = true;

			// fprintf(stderr,"following chain\n");
			while (x[nextVar].isFixed()) {  // fprintf(stderr,"nextvar %d ", nextVar);
				thisCycle.push(nextVar);
				new_fixed.remove(nextVar);  // seen this one, don't look at it again

				// update the score
				int level;
				double act;
				switch (so.checkfailure) {
					case 1:  // first (no score required)
					case 2:  // smallest cycle
					case 3:  // largest cycle
						break;
					case 4:  // cycle with lowest ave level,
					case 5:  // cycle with highest ave level,
						// XXX [AS] Replaced 'sat.level' by 'sat.trailpos', because it was replaced in rev. 441
						// Maybe it shoud be replaced by sat.getLevel(.)?
						level = sat.trailpos[var(x[nextVar].getValLit())];
						// level = sat.getLevel(var(x[nextVar].getValLit()));
						thisScore += level;
						break;
					case 6:  // cycle with lowest ave activity,
					case 7:  // cycle with highest ave activity
						act = sat.activity[var(x[nextVar].getValLit())];
						thisScore += act;
						break;
					case 8:  // last (no score required)
						break;
					case 9:  // highest min level, so need to calculate min level
						// XXX [AS] Replaced 'sat.level' by 'sat.trailpos', because it was replaced in rev. 441
						// Maybe it shoud be replaced by sat.getLevel(.)?
						level = sat.trailpos[var(x[nextVar].getValLit())];
						// level = sat.getLevel(var(x[nextVar].getValLit()));
						if (thisScore > level || noScoreYet) {
							thisScore = level;
						}
						break;
					case 10:  // lowest max level, so need to calculate max level
						// XXX [AS] Replaced 'sat.level' by 'sat.trailpos', because it was replaced in rev. 441
						// Maybe it shoud be replaced by sat.getLevel(.)?
						level = sat.trailpos[var(x[nextVar].getValLit())];
						// level = sat.getLevel(var(x[nextVar].getValLit()));
						if (thisScore < level || noScoreYet) {
							thisScore = level;
						}
						break;
				}
				noScoreYet = false;
				// assert(chainLength <= size);
				if (x[nextVar].getVal() == startVar) {
					// fprintf(stderr,"found cycle\n");
					thisIsCycle = true;
					break;
				}
				nextVar = x[nextVar].getVal();
			}
			// fprintf(stderr,"end chain\n");
			if (thisCycle.size() == size) {
				break;  // all variables are included in this cycle
			}
			if (thisIsCycle) {
				// calculate the score for this cycle (we keep the highest)
				switch (so.checkfailure) {
					case 1:
						break;  // first cycle (no score required)
					case 2:
						thisScore = -1 * thisCycle.size();
						break;  // smallest cycle
					case 3:
						thisScore = thisCycle.size();
						break;  // largest cycle
					case 4:
						thisScore = -1 * thisScore / thisCycle.size();
						break;  // lowest ave level
					case 5:
						thisScore = thisScore / thisCycle.size();
						break;  // highest ave level
					case 6:
						thisScore = -1 * thisScore / thisCycle.size();
						break;  // lowest ave activity
					case 7:
						thisScore = thisScore / thisCycle.size();
						break;  // highest ave activity
					// 8-last, 9-highest min level, 10-lowest max level
					case 8:  // last cycle (no score - we just always overwrite the best)
					case 9:  // highest min level - already done
						break;
					case 10:
						thisScore = -1 * thisScore;  // lowest max level
				}
				// fprintf(stderr, "this score is %f\n", thisScore);
				if (!foundSmallCycle || so.checkfailure == 1 || so.checkfailure == 8 ||
						thisScore > bestScore) {
					foundSmallCycle = true;
					bestScore = thisScore;
					thisCycle.copyTo(bestCycle);
					if (so.checkfailure == 1) {
						break;
					}
				}
			}
		}

		// If we found at least one cycle, report failure
		// if we're not explaining we'll already return false which is fine
		if (foundSmallCycle && so.lazy) {
			Clause* r = nullptr;
			vec<int> notInCycle;
			bool doOutsideIn = false;
			bool result;

			// create the reason clause
			int chainLength = bestCycle.size();
			if (so.checkexpl == 1) {
				// equalities
				r = Reason_new(chainLength);
				// fprintf(stderr, "\nchain:");
				for (int j = 1; j < chainLength; j++) {
					(*r)[j] = x[bestCycle[j - 1]].getValLit();
				}
				result = x[bestCycle.last()].remVal(bestCycle[0], r);
			} else if (so.checkexpl == 6) {
				// inside can't reach out but smaller
				// find smallest and highest index anything inside the cycle is equal to
				int smallestIn = bestCycle[0];
				int largestIn = bestCycle[0];
				for (int i = 1; i < chainLength; i++) {
					if (bestCycle[i] < smallestIn) {
						smallestIn = bestCycle[i];
					}
					if (bestCycle[i] > largestIn) {
						largestIn = bestCycle[i];
					}
				}
				// find the indices outside the cycle which are btw the smallest and largest inside
				vec<int> outsidebetween;
				for (int i = smallestIn + 1; i < largestIn; i++) {
					// find out if it's in the cycle
					bool incycle = false;
					for (int j = 0; j < chainLength; j++) {
						if (bestCycle[j] == i) {
							incycle = true;
						}
					}
					// if not, this is an outside in index
					if (!incycle) {
						outsidebetween.push(i);
					}
				}
				// fprintf(stderr, "min in is %d, max in is %d\n", smallestIn, largestIn);

				// fprintf(stderr, "out ");
				// for(int i = 0; i < outsidebetween.size(); i++)
				//     fprintf(stderr, "%d,", outsidebetween[i]);
				// fprintf(stderr, "num in is %d\n", chainLength);
				//  for each var in the cycle, say that it's larger than or equal to the smallest
				//  index, less than or equal to the largest index, and not equal to any of the
				//  outside indices within that range
				//  leave out the first one, as this is the one we'll set
				r = Reason_new(chainLength * (2 + outsidebetween.size()));
				for (int i = 0; i < chainLength; i++) {
					int start = i * (2 + outsidebetween.size());
					int varIndex = bestCycle[i];
					if (i > 0) {                                            // leave out first literal
						(*r)[start] = x[varIndex].getLit(smallestIn - 1, 3);  // x <= smallest-1
					}
					(*r)[start + 1] = x[varIndex].getLit(largestIn + 1, 2);  // x >= largest+1
					for (int j = 0; j < outsidebetween.size(); j++) {
						(*r)[start + 2 + j] = x[varIndex].getLit(outsidebetween[j], 1);  // x == k
					}
				}

				result = x[bestCycle[0]].setMax(smallestIn - 1, r);

			} else {
				// find the vars in and not in the cycle
				for (int i = 0; i < size; i++) {
					bool cycleContains = false;
					for (int j = 0; j < bestCycle.size(); j++) {
						if (bestCycle[j] == i) {
							cycleContains = true;
							break;
						}
					}
					if (!cycleContains) {
						notInCycle.push(i);
					}
				}

				r = Reason_new(bestCycle.size() * notInCycle.size());

				if (so.checkexpl == 2) {  // inside can't reach out
					doOutsideIn = false;
				} else if (so.checkexpl == 3) {  // outside can't reach in
					doOutsideIn = true;
				} else if (so.checkexpl == 4) {  // smaller group can't reach bigger group
					doOutsideIn = notInCycle.size() < bestCycle.size();
				} else if (so.checkexpl == 5) {  // bigger group can't reach smaller group
					doOutsideIn = bestCycle.size() < notInCycle.size();
				} else {
					fprintf(stderr, "Unknown check explanation type\n");
				}

				if (doOutsideIn) {
					explainAcantreachB(r, 1, bestCycle.size() * notInCycle.size(), notInCycle, bestCycle,
														 notInCycle[0], bestCycle[0]);
					result = x[notInCycle[0]].setVal(bestCycle[0], r);
				} else {
					explainAcantreachB(r, 1, bestCycle.size() * notInCycle.size(), bestCycle, notInCycle,
														 bestCycle[0], notInCycle[0]);
					result = x[bestCycle[0]].setVal(notInCycle[0], r);
				}
			}

			assert(!result);
		}
		return !foundSmallCycle;
	}

	void clearPropState() override {
		in_queue = false;
		new_fixed.clear();
	}
};

void circuit(vec<IntVar*>& _x, int offset) {
	// fprintf(stderr,"\ncircuit constraint");
	all_different(_x, CL_DOM);
	vec<IntView<> > x;
	for (int i = 0; i < _x.size(); i++) {
		_x[i]->specialiseToEL();
	}

	if (offset == 0) {
		for (int i = 0; i < _x.size(); i++) {
			int_rel(_x[i], IRT_NE, i);
		}
		for (int i = 0; i < _x.size(); i++) {
			x.push(IntView<>(_x[i]));
		}
		new Circuit<0>(x);
	} else {
		for (int i = 0; i < _x.size(); i++) {
			int_rel(_x[i], IRT_NE, i + offset);
		}
		for (int i = 0; i < _x.size(); i++) {
			x.push(IntView<4>(_x[i], 1, -offset));
		}
		new Circuit<4>(x);
	}
}

void path(vec<IntVar*>& _x) {
	// add dummy node
	vec<IntVar*> x;
	_x.copyTo(x);
	IntVar* dummyVar;
	// dummy node can have any original node as its successor
	createVar(dummyVar, 0, _x.size() - 1, true);
	x.push(dummyVar);

	// nodes including dummy node must form circuit
	circuit(x);
}
