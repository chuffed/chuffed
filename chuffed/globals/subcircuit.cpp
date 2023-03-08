#include <chuffed/core/propagator.h>
#include <chuffed/vars/modelling.h>

// A variable with value its own index is considered out of the circuit.
// Any other value indicates the
// index of the successor variable in the cycle.
template <int U = 0>
class SubCircuit : public Propagator {
public:
	int const size;

	IntView<U>* const x;
	bool const check;    // use 'check' algorithm
	bool const prevent;  // use 'prevent' algorithm
	bool const scc;      // use strongly connected components algorithm
	bool const pruneRoot;
	bool const pruneSkip;
	bool const fixReq;
	bool const pruneWithin;
	vec<int> chain_start;
	bool* inCircuit;
	bool* isStartChain;
	int defaultRoot;  // index of var used as root of scc tree by default

	// Persistent state

	// Intermediate state
	vec<int> new_fixed;

	vec<int> prev;     // scc alg - vars in last subtree visited
	vec<int> earlier;  // scc alg - vars in the earlier subtrees
	vec<int> later;    // scc alg - vars in later subtrees

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

	SubCircuit(vec<IntView<U> > _x)
			: size(_x.size()),
				x(_x.release()),
				check(so.circuitalg <= 3),
				prevent(so.circuitalg >= 2 && so.circuitalg <= 3),
				scc(so.circuitalg >= 3),
				pruneRoot(so.sccoptions >= 3),
				pruneSkip(true),
				fixReq(true),
				pruneWithin(so.sccoptions == 2 || so.sccoptions == 4),
				defaultRoot(0) {
		priority = 5;

		new_fixed.reserve(size);
		chain_start.reserve(size);
		inCircuit = (bool*)malloc(size * sizeof(bool));
		isStartChain = (bool*)malloc(size * sizeof(bool));

		prev.reserve(size);
		earlier.reserve(size);
		later.reserve(size);
		index = (int*)malloc(size * sizeof(int));
		lowlink = (int*)malloc(size * sizeof(int));

		if (scc) {
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
		if (c & EVENT_F && x[i].getVal() != i) {
			new_fixed.push(i);  // only put in new_fixed if it's in the circuit
		}
		pushInQueue();
	}

	void addPropagation(bool fix, int var, int val, Clause* r) {
		PROP newprop;
		newprop.reason = r;
		newprop.var = var;
		newprop.val = val;
		newprop.fix = fix;
		propQueue.push(newprop);
	}

	// Prunes that partial assigned paths are not completed to cycles,
	// unless there is no variable outside the chain fixed to an index not its own
	bool propagatePrevent() {
		// fprintf(stderr, "Prevent\n");
		//  Assume no cycles (will be already checked).
		//  We have a set of chains, each one with a start index that no variable is fixed to.
		//  First find the start indices for the chains

		for (int i = 0; i < size; i++) {
			isStartChain[i] = true;
		}

		for (int i = 0; i < size; i++) {
			if (x[i].isFixed()) {
				isStartChain[x[i].getVal()] = false;
			} else {
				isStartChain[i] = false;
			}
		}

		chain_start.clear();
		for (int i = 0; i < size; i++) {
			if (isStartChain[i]) {
				chain_start.push(i);
			}
		}

		// For each chain, assuming we can find a var outside it which is not a self-loop,
		// follow the chain and set the end variable not equal to the index of the start
		// The evidence variable will be:
		// 5-start other chain, 1-first valid, 2-last, 3-high level, 4-low level
		// The start of another chain is valid as the justification because that will be a
		// var outside this chain that is fixed to value not its own index
		if (so.preventevidence == 5 && chain_start.size() < 2) {
			return true;
		}

		for (int chainNumber = 0; chainNumber < chain_start.size(); chainNumber++) {
			// get possible vars to use as evidence that we can't close this cycle
			// (for now vars which can't take their index as a value, later we
			// will remove the ones in this chain)
			vec<int> evidenceOptions;
			if (so.preventevidence == 5) {
				// if this is the first chain, use the
				// start of the second, otherwise use the start of the first
				if (chainNumber == 0) {
					evidenceOptions.push(chain_start[1]);
				} else {
					evidenceOptions.push(chain_start[0]);
				}
			} else {
				for (int i = 0; i < size; i++) {
					if (!x[i].remValNotR(i)) {  // if it can't equal its own index
						evidenceOptions.push(i);
					}
				}
			}

			// find the end of the chain, and remove evidence vars which are in this chain
			int startVar = chain_start[chainNumber];
			int chainLength = 1;
			int endVar = startVar;
			if (so.preventevidence != 5) {
				evidenceOptions.remove(startVar);
			}
			while (x[endVar].isFixed()) {
				chainLength++;
				endVar = x[endVar].getVal();
				if (so.preventevidence != 5) {
					evidenceOptions.remove(endVar);
				}
			}

			if (x[endVar].remValNotR(startVar) && evidenceOptions.size() > 0) {
				Clause* r = nullptr;
				if (so.lazy) {
					int evidenceVar = chooseEvidenceVar(evidenceOptions, so.preventevidence);

					if (so.preventevidence != 5) {
						evidenceOptions.remove(startVar);
					}
					if (so.prevexpl == 1) {
						r = Reason_new(chainLength + 1);
						int v = startVar;
						for (int index = 1; index < chainLength; index++) {
							(*r)[index] = x[v].getValLit();
							v = x[v].getVal();
						}

						(*r)[chainLength] = ~x[evidenceVar].getLit(evidenceVar, 0);
					} else {
						// find the vars in the start of the chain and those not in the chain
						vec<int> inStartChain;
						vec<int> outside;
						for (int i = 0; i < size; i++) {
							if (i != endVar) {
								outside.push(i);
							}
						}
						int v = startVar;
						for (int index = 1; index < chainLength; index++) {
							inStartChain.push(v);
							outside.remove(v);
							v = x[v].getVal();
						}
						assert(inStartChain.size() + outside.size() + 1 == size);
						// reason is nothing in start of chain can reach outside chain
						int explSize = inStartChain.size() * outside.size() + 2;
						r = Reason_new(explSize);

						explainAcantreachB(r, 1, inStartChain, outside);
						(*r)[explSize - 1] = ~x[evidenceVar].getLit(evidenceVar, 0);
					}
				}

				if (!x[endVar].remVal(startVar, r)) {
					return false;
				}
			}
		}

		return true;
	}

	Lit getEvidenceLit(vec<int> potentialVarIndices) {
		// filter out those that don't have to be in the circuit
		vec<int> varsIn;
		varsIn.clear();
		for (int i = 0; i < potentialVarIndices.size(); i++) {
			int varindex = potentialVarIndices[i];
			if (!x[varindex].indomain(varindex)) {
				varsIn.push(varindex);
			}
		}
		// now choose one using our selection method
		if (varsIn.size() > 0) {
			int chosen = chooseEvidenceVar(varsIn, so.sccevidence);
			assert(!x[chosen].indomain(chosen));
			bool found = false;
			for (int i = 0; i < potentialVarIndices.size(); i++) {
				if (potentialVarIndices[i] == chosen) {
					found = true;
				}
			}
			assert(found);
			Lit result = ~x[chosen].getLit(chosen, 0);
			assert(result != lit_True);
			return result;
		}
		return lit_True;
	}

	// Add literals to reason to explain that no node in set A
	// reaches a node in set B
	// If there's a node a1 in A and a node b1 in B, the literal
	// involving those nodes is not included
	void explainAcantreachB(Clause* reason, int reasonIndex, vec<int> A, vec<int> B, int a1 = -1,
													int b1 = -1) {
		// fprintf(stderr, "explaining");
		for (int a = 0; a < A.size(); a++) {
			assert(A[a] < size && A[a] >= 0);
			for (int b = 0; b < B.size(); b++) {
				assert(B[b] < size && B[b] >= 0);
				if (A[a] != a1 || B[b] != b1) {
					assert(!x[A[a]].indomain(B[b]));
					// fprintf(stderr, "add %d not equal to %d\n", A[a], B[b]);
					(*reason)[reasonIndex++] = ~x[A[a]].getLit(B[b], 0);
				}
			}
		}
		// fprintf(stderr, "done\n");
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
				// child (as the circuit must come back up through an edge from
				// the child to this node and therefore can't go in the other
				// direction). We can do this as long as there is a node outside
				// the child and this node which has to be in.
				// We can also prune any edges from a node outside the child's
				// subtree to this node, as long as something inside the child has to be in.
				if (pruneWithin && isFirstChild && lowlink[child] == index[thisNode]) {
					// XXX [AS] Commented following line, because propagator related statistics
					// should be collected within the propagator class.
					// engine.prunedGeneralise++;
					// The reason is that no node in the child's subtree reaches a node outside the subtree
					// that isn't the parent, and at least one node in the child's subtree is in the circuit
					// First divide the nodes into those inside and outside the child's subtree
					vec<int> inside;
					vec<int> outside;
					for (int i = 0; i < size; i++) {
						if (index[i] >= index[child]) {
							inside.push(i);
						} else if (index[i] != index[thisNode]) {
							outside.push(i);
						}
					}

					// Now check one node is definitely in
					Lit evidenceIn = getEvidenceLit(inside);
					Lit evidenceOut = getEvidenceLit(outside);
					if (evidenceOut != lit_True) {
						Clause* r = nullptr;
						if (so.lazy) {
							r = Reason_new(inside.size() * outside.size() + 2);
							(*r)[1] = evidenceOut;
							explainAcantreachB(r, 2, inside, outside);
						}
						addPropagation(false, thisNode, child, r);
					}
					if (evidenceIn != lit_True) {
						Clause* r = nullptr;
						if (so.lazy) {
							r = Reason_new(inside.size() * outside.size() + 2);
							(*r)[1] = evidenceIn;
							explainAcantreachB(r, 2, inside, outside);
						}
						for (int i = 0; i < outside.size(); i++) {
							if (x[outside[i]].indomain(thisNode)) {
								addPropagation(false, outside[i], thisNode, r);
							}
						}
					}
				}

				isFirstChild = false;        // We've now visited at least one child
			} else if (child != thisNode)  // This is a node we've seen before (ignore self-cycle edges)
			{
				// fprintf(stderr,"old child %d\n", child);
				//  If child is within the last subtree we've found a backedge (from this node to the child)
				if (index[child] >= startPrevSubtree && index[child] <= endPrevSubtree) {
					(*numback)++;
					*backfrom = thisNode;
					*backto = child;
				}

				// If w is from a subtree before the previous one prune this edge (if that option is set)
				if (pruneSkip && index[child] < startPrevSubtree) {
					Lit evidence = getEvidenceLit(prev);
					if (evidence != lit_True) {
						// XXX [AS] Commented following line, because propagator related statistics
						// should be collected within the propagator class.
						// engine.prunedSkip++;
						Clause* r = nullptr;
						if (so.lazy) {
							// The reason is that no node in an earlier
							// subtree can reach the prev or later subtrees,
							// and no node in the prev subtree can reach
							// later subtrees.
							vec<int> prevAndLater;
							prevAndLater.reserve(prev.size() + later.size());
							for (int i = 0; i < prev.size(); i++) {
								prevAndLater.push(prev[i]);
							}
							for (int i = 0; i < later.size(); i++) {
								prevAndLater.push(later[i]);
							}
							r = Reason_new(earlier.size() * prevAndLater.size() + prev.size() * later.size() + 2);
							(*r)[1] = evidence;
							explainAcantreachB(r, 2, prev, later);
							explainAcantreachB(r, prev.size() * later.size() + 2, earlier, prevAndLater);
						}
						addPropagation(false, thisNode, child, r);
					}
				}

				if (index[child] < lowlink[thisNode]) {
					lowlink[thisNode] = index[child];
				}
			}
			// fprintf(stderr,"lowpoint is %d\n", lowlink[thisNode]);
		}

		// Fail if there's an scc rooted here
		if (lowlink[thisNode] == index[thisNode]) {
			// The reason is that no node in the subtree rooted by this
			// one (including this one)
			// reaches a node outside that subtree, and some node inside
			// the subtree (not including this node) is required in the circuit.
			// Start by finding the nodes inside and outside the subtree.
			vec<int> inside;
			vec<int> outside;

			for (int i = 0; i < size; i++) {
				if (index[i] > index[thisNode]) {
					inside.push(i);
				} else if (i != thisNode) {
					outside.push(i);
				}
			}

			Lit evidenceInside = getEvidenceLit(inside);  // at this point inside excludes this node

			inside.push(thisNode);  // now include this node

			// Set all vars outside the component to be self-cycles
			if (evidenceInside != lit_True) {
				Clause* r = nullptr;
				if (so.lazy) {
					r = Reason_new(inside.size() * outside.size() + 2);
					(*r)[1] = evidenceInside;

					explainAcantreachB(r, 2, inside, outside);
				}
				for (int i = 0; i < outside.size(); i++) {
					int varOutside = outside[i];
					if (x[varOutside].setValNotR(varOutside)) {
						// XXX [AS] Commented following line, because propagator related statistics
						// should be collected within the propagator class.
						// engine.multipleSCC++;
						addPropagation(true, varOutside, varOutside, r);
						/* if(!x[varOutside].setVal(varOutside, r))
						 {
						 fprintf(stderr, "failing\n");
								 return false;
						 }*/
					}
				}
			}
		}

		return true;
	}

	int chooseRoot() {
		// choose variable for root of tree
		// make sure we don't choose a self-cycle
		// if all vars are self-cycles just return -1
		vec<int> options;
		for (int i = 0; i < size; i++) {
			if (!x[i].isFixed() || x[i].getVal() != i) {
				options.push(i);
			}
		}
		if (options.size() == 0) {
			return -1;
		}
		int root = options[0];
		int dom = 0;
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
				for (int i = 0; i < size; i++) {
					if (x[i].isFixed()) {
						options.remove(i);
					}
				}
				if (options.size() > 0) {
					root = options[(int)(((double)options.size()) * rand() / (RAND_MAX + 1.0))];
				}
				break;
			case 7:  // first (even if fixed) - this is the default
				break;
			case 8:  // random (even if fixed)
				root = options[(int)(((double)options.size()) * rand() / (RAND_MAX + 1.0))];
				break;
			case 9:  // largest domain
				dom = x[root].size();
				for (int i = 1; i < options.size(); i++) {
					if (x[options[i]].size() > dom) {
						dom = x[options[i]].size();
						root = options[i];
					}
				}
				break;
		}
		return root;
	}

	bool propagateSCC(int root) {
		int backfrom = 0;  // the last back edge found
		int backto = 0;
		int numback = 0;  // the number of back edges found

		vec<int> thisSubtree;

		thisSubtree.reserve(size);
		prev.clear();
		earlier.clear();
		later.clear();

		assert(!x[root].isFixed() || x[root].getVal() != root);
		for (int i = 0; i < size; i++) {
			index[i] = -1;  // unvisited
		}

		index[root] = 0;  // first node visited
		lowlink[root] = 0;

		nodesSeen = 1;  // only seen root node
		propQueue.clear();

		// original subtree is just the root node
		int startSubtree = 0;
		int endSubtree = 0;

		// explore children of the root node
		for (typename IntView<U>::iterator i = x[root].begin(); i != x[root].end(); ++i) {
			int child = *i;

			if (index[child] == -1)  // if haven't explored this yet
			{
				numback = 0;
				if (!exploreSubtree(child, startSubtree, endSubtree, &backfrom, &backto, &numback)) {
					// fprintf(stderr, "failed in subtree\n");
					return false;  // fail if we found a scc within the child
				}

				// Find the nodes in the subtree we just explored and the ones still to be explored
				thisSubtree.clear();
				later.clear();
				for (int i = 0; i < size; i++) {
					if (index[i] < 0) {
						later.push(i);
					} else if (index[i] > endSubtree) {
						thisSubtree.push(i);
					}
				}

				Lit evidenceThis = getEvidenceLit(thisSubtree);
				Lit evidenceOther = getEvidenceLit(prev);
				vec<int> alloutside;
				if (prev.size() == 0) {
					for (int i = 0; i < later.size(); i++) {
						alloutside.push(later[i]);
					}
					alloutside.push(root);
					evidenceOther = getEvidenceLit(alloutside);
				}

				if (evidenceThis != lit_True && evidenceOther != lit_True) {
					// If there's no edge from the new subtree back to the
					// previous one and both of these groups has
					// a variable definitely in, fail
					if (numback == 0) {
						// XXX [AS] Commented following line, because propagator related statistics
						// should be collected within the propagator class.
						// engine.nobackedge++;
						if (so.lazy) {
							// If prev is empty then this is the first subtree,
							// and we just need to say that
							// the nodes in this subtree can't reach the
							// unexplored nodes or the root.
							// This is only a problem if something outside this subtree has to be in.
							if (prev.size() == 0) {
								Clause* r = Reason_new(thisSubtree.size() * alloutside.size() + 2);
								(*r)[1] = evidenceThis;
								(*r)[2] = evidenceOther;
								// This subtree can't reach outside
								explainAcantreachB(r, 3, thisSubtree, alloutside, thisSubtree[0], alloutside[0]);
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
							Clause* r = Reason_new(size1 + size2 + size3 + 2);
							(*r)[1] = evidenceThis;
							(*r)[2] = evidenceOther;
							// 1. Earlier can't reach prev, this or later
							explainAcantreachB(r, 3, earlier, prev_this_later);

							// 2. Prev can't reach this or later
							explainAcantreachB(r, 3 + size1, prev, this_later);

							// 3. this can't reach prev or later
							explainAcantreachB(r, 3 + size1 + size2, thisSubtree, prev_later, thisSubtree[0],
																 prev_later[0]);
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
								r = Reason_new(thisSubtree.size() * alloutside.size() + 2);
								(*r)[1] = evidenceThis;
								(*r)[2] = evidenceOther;
								// This subtree can't reach outside (except backfrom to backto)
								explainAcantreachB(r, 3, thisSubtree, alloutside, backfrom, backto);
							} else {
								// Otherwise we have at least one previous subtree.
								// The reason is the same as when failing above,
								// but we leave out the one we're setting
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
								r = Reason_new(size1 + size2 + size3 + 2);
								(*r)[1] = evidenceThis;
								(*r)[2] = evidenceOther;

								// 1. Earlier can't reach prev, this or later
								explainAcantreachB(r, 3, earlier, prev_this_later);

								// 2. Prev can't reach this or later
								explainAcantreachB(r, 3 + size1, prev, this_later);

								// 3. this can't reach prev or unexplored (except for the one we're setting)
								explainAcantreachB(r, 3 + size1 + size2, thisSubtree, prev_later, backfrom, backto);
							}
						}

						addPropagation(true, backfrom, backto, r);
					}
				}

				// When a new subtree has been explored, update the prev and earlier vectors (only necessary
				// if explaining)
				for (int i = 0; i < prev.size(); i++) {
					earlier.push(prev[i]);
				}
				prev.clear();
				for (int i = 0; i < thisSubtree.size(); i++) {
					prev.push(thisSubtree[i]);
				}

				// Set the new subtree boundaries
				startSubtree = endSubtree + 1;
				endSubtree = nodesSeen - 1;
			}
		}

		// If we haven't reached all of the nodes and something we have reached has to
		// be included, then set everything outside to take its own index
		if (nodesSeen != size) {
			vec<int> seen;
			vec<int> notseen;

			for (int var = 0; var < size; var++) {
				if (index[var] >= 0) {
					seen.push(var);
				} else {
					notseen.push(var);
				}
			}
			int numNotSeen = size - nodesSeen;
			assert(seen.size() == nodesSeen);
			assert(notseen.size() == numNotSeen);

			Lit evidenceSeen = getEvidenceLit(seen);
			if (evidenceSeen != lit_True) {
				// XXX [AS] Commented following line, because propagator related statistics
				// should be collected within the propagator class.
				// engine.disconnected++;
				Clause* r = nullptr;

				if (so.lazy) {
					// need to say that each seen node doesn't reach any non-seen node
					r = Reason_new(nodesSeen * numNotSeen + 2);
					(*r)[1] = evidenceSeen;
					explainAcantreachB(r, 2, seen, notseen);
				}
				for (int i = 0; i < notseen.size(); i++) {
					int outsideVar = notseen[i];
					if (x[outsideVar].setValNotR(outsideVar)) {
						if (!x[outsideVar].setVal(outsideVar, r)) {
							return false;
						}
					}
				}
			}
		}

		// If we're pruning root edges and there was more than one subtree, prune edges from the root to
		// earlier subtrees
		if (pruneRoot && startSubtree > 1) {
			// Check there's evidence
			// First find the nodes in the last subtree (and disconnected nodes) and those in the earlier
			// ones

			vec<int> lastSubtreeAndOutside;
			vec<int> earlierSubtree;
			for (int i = 0; i < size; i++) {
				if (index[i] >= startSubtree || index[i] < 0) {
					lastSubtreeAndOutside.push(i);
				} else if (index[i] > 0) {  // The root is considered in no subtree
					earlierSubtree.push(i);
				} else {
					assert(i == root);
				}
			}
			assert(earlierSubtree.size() > 0);
			assert(earlierSubtree.size() + lastSubtreeAndOutside.size() + 1 == size);
			Lit evidenceLast = getEvidenceLit(lastSubtreeAndOutside);
			if (evidenceLast != lit_True) {
				// Build the reason if neccessary (it will be the same for all of the pruned edges)
				Clause* r = nullptr;
				if (so.lazy) {
					// Reason should state that no var in an earlier sub tree reaches a var
					// in the last subtree or outside
					r = Reason_new(earlierSubtree.size() * lastSubtreeAndOutside.size() + 2);
					(*r)[1] = evidenceLast;
					explainAcantreachB(r, 2, earlierSubtree, lastSubtreeAndOutside);
				}

				// Prune all edges from the root to nodes in earlier subtrees
				for (int i = 0; i < size; i++) {
					if (i != root && index[i] < startSubtree) {
						addPropagation(false, root, i, r);
					}
				}

				/* for (typename IntView<U>::iterator i = x[root].begin(); i != x[root].end(); ++i)
				 {
						 if(*i != root && index[*i] < startSubtree)
						 {
								 // XXX [AS] Commented following line, because propagator related statistics
								 // should be collected within the propagator class.
								 //engine.prunedRoot++;
								 addPropagation(false, root, *i, r);
						 }
				 }*/
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

	bool propagateCheck() {
		// for each newly fixed variable, follow the chain and if you find a circuit
		// then any variable not in the circuit must have its own index as a value
		for (int i = 0; i < new_fixed.size(); i++) {
			// new_fixed should only contain variables fixed to values other than their own indices
			int startVar = new_fixed[i];
			assert(x[startVar].isFixed());
			assert(x[startVar].getVal() != startVar);
			int nextVar = startVar;
			int chainLength = 0;

			// Clear the inCircuit array
			for (int i = 0; i < size; i++) {
				inCircuit[i] = false;
			}

			bool foundCycle = false;
			while (x[nextVar].isFixed()) {
				chainLength++;
				inCircuit[nextVar] = true;
				assert(chainLength <= size);
				if (x[nextVar].getVal() == startVar) {
					foundCycle = true;
					break;
				}
				nextVar = x[nextVar].getVal();
			}
			if (foundCycle && chainLength < size) {
				// fprintf(stderr,"found cycle length %d\n", chainLength);
				//  all variables not in the cycle must have their own indices as values
				Clause* r = nullptr;
				vec<int> notInCycle;
				bool doOutsideIn = false;
				if (so.lazy) {
					/*  r = Reason_new(chainLength + 1);
						int v = startVar;
						for(int j = 1 ; j <= chainLength; j++)
						{
								(*r)[j] = x[v].getValLit();
								v = x[v].getVal();
						}*/
					if (so.checkexpl == 1) {
						// equalities
						r = Reason_new(chainLength + 1);
						int v = startVar;
						for (int j = 1; j <= chainLength; j++) {
							(*r)[j] = x[v].getValLit();
							v = x[v].getVal();
						}
					} else {
						// find the vars in and not in the cycle
						notInCycle.growTo(size);
						for (int i = 0; i < size; i++) {
							notInCycle[i] = i;
						}
						vec<int> inCycle;
						inCycle.growTo(chainLength);
						int v = startVar;
						for (int j = 0; j < chainLength; j++) {
							inCycle[j] = v;
							notInCycle.remove(v);
							v = x[v].getVal();
						}
						r = Reason_new(inCycle.size() * notInCycle.size() + 2);
						// the first literal is an evidence literal from inside the circuit
						// choose the one from the highest level?
						int chosenVar = chooseEvidenceVar(inCycle, so.checkevidence);
						(*r)[1] = x[chosenVar].getLit(chosenVar, 1);  // xi == i (is false)

						if (so.checkexpl == 2) {  // inside can't reach out
							doOutsideIn = false;
						} else if (so.checkexpl == 3) {  // outside can't reach in
							doOutsideIn = true;
						} else if (so.checkexpl == 4) {  // smaller group can't reach bigger group
							doOutsideIn = notInCycle.size() < inCycle.size();
						} else if (so.checkexpl == 5) {  // bigger group can't reach smaller group
							doOutsideIn = inCycle.size() < notInCycle.size();
						} else {
							fprintf(stderr, "Unknown check explanation type\n");
						}

						if (doOutsideIn) {
							explainAcantreachB(r, 2, notInCycle, inCycle);
						} else {
							explainAcantreachB(r, 2, inCycle, notInCycle);
						}
					}
				}

				// set all vars not in circuit to have own index as value
				// if one or more cannot do so, we need to choose which one(s)
				// to add clauses for.
				// options are: 1-first, 2-last, 3-high level, 4-low level
				vec<int> failIndices;
				for (int i = 0; i < size; i++) {
					if (!inCircuit[i]) {
						if (x[i].setValNotR(i)) {
							if (!x[i].remValNotR(i)) {
								failIndices.push(i);
								// fprintf(stderr,"prune\n");
							} else if (!x[i].setVal(i, r)) {
								fprintf(stderr, "unexpected fail\n");
							}
						}
					}
				}
				// now do the failing one(s) if there are any
				if (failIndices.size() > 0) {
					int chosenIndex = chooseEvidenceVar(failIndices, so.checkevidence);
					if (x[chosenIndex].setVal(chosenIndex, r)) {
						fprintf(stderr, "unexpected success\n");
					}
					return false;
				}
			}

			// If we found a cycle stop here as all other fixed vars will be in the
			// same cycle (or we would have returned false already).
			if (foundCycle) {
				break;
			}
		}

		return true;
	}

	int chooseEvidenceVar(vec<int> options, int selectionMethod) {
		if (options.size() == 1 || selectionMethod == 1) {
			// fprintf(stderr, "option 2 chose %d\n", options[0]);
			//  1 is the first
			return options[0];
		}
		if (selectionMethod == 2) {
			// fprintf(stderr, "option 1 chose %d\n", options[1]);
			//  the last
			return options.last();
		}
		/*   else if(selectionMethod == 3)
			 {
					 // highest activity
					 double highestAct = 0;
					 int bestVar = options[0];
					 for(int i = 0; i < options.size(); i++)
					 {
								int v = options[i];
								Lit p = x[v].getLit(v,0);
								int satvar = var(p);
							if(sat.activity[satvar] > highestAct)
							{
									 highestAct = sat.activity[satvar];
									 bestVar = v;
							}
					 }
					 return bestVar;
			 }
			 else if(selectionMethod == 4)
			 {
					 // lowest activity
					 double lowestAct = sat.activity[var(x[options[0]].getLit(options[0],0))];
					 int bestVar = options[0];
					 for(int i = 1; i < options.size(); i++)
					 {
								int v = options[i];
								Lit p = x[v].getLit(v,0);
								int satvar = var(p);
							if(sat.activity[satvar] < lowestAct)
							{
									 lowestAct = sat.activity[satvar];
									 bestVar = v;
							}
					 }
					 return bestVar;
			 }*/
		if (selectionMethod == 3) {
			// highest level
			// XXX [AS] Replaced 'sat.level' by 'sat.trailpos', because it was replaced in rev. 441
			// Maybe it shoud be replaced by sat.getLevel(.)?
			int highestLevel = sat.trailpos[var(x[options[0]].getLit(options[0], 1))];
			// int highestLevel = sat.getLevel(var(x[options[0]].getLit(options[0],1)));
			int bestVar = options[0];
			for (int i = 0; i < options.size(); i++) {
				// XXX [AS] Replaced 'sat.level' by 'sat.trailpos', because it was replaced in rev. 441
				// Maybe it shoud be replaced by sat.getLevel(.)?
				if (sat.trailpos[var(x[options[0]].getLit(options[0], 1))] !=
						sat.trailpos[var(x[options[0]].getLit(options[0], 0))]) {
					// if(sat.getLevel(var(x[options[0]].getLit(options[0],1))) !=
					// sat.getLevel(var(x[options[0]].getLit(options[0],0))))
					fprintf(stderr, "not same\n");
				}
				int v = options[i];
				Lit p = x[v].getLit(v, 1);
				int satvar = var(p);
				// XXX [AS] Replaced 'sat.level' by 'sat.trailpos', because it was replaced in rev. 441
				// Maybe it shoud be replaced by sat.getLevel(.)?
				if (sat.trailpos[satvar] > highestLevel)
				// if(sat.getLevel(satvar) > highestLevel)
				{
					// XXX [AS] Replaced 'sat.level' by 'sat.trailpos', because it was replaced in rev. 441
					// Maybe it shoud be replaced by sat.getLevel(.)?
					highestLevel = sat.trailpos[satvar];
					// highestLevel = sat.getLevel(satvar);
					bestVar = v;
				}
			}
			return bestVar;
		}
		if (selectionMethod == 4) {
			// lowest level
			// XXX [AS] Replaced 'sat.level' by 'sat.trailpos', because it was replaced in rev. 441
			// Maybe it shoud be replaced by sat.getLevel(.)?
			int lowestLevel = sat.trailpos[var(x[options[0]].getLit(options[0], 1))];
			// int lowestLevel = sat.getLevel(var(x[options[0]].getLit(options[0],1)));
			int bestVar = options[0];
			for (int i = 0; i < options.size(); i++) {
				int v = options[i];
				Lit p = x[v].getLit(v, 1);
				int satvar = var(p);
				// XXX [AS] Replaced 'sat.level' by 'sat.trailpos', because it was replaced in rev. 441
				// Maybe it shoud be replaced by sat.getLevel(.)?
				if (sat.trailpos[satvar] < lowestLevel)
				// if(sat.getLevel(satvar) < lowestLevel)
				{
					// XXX [AS] Replaced 'sat.level' by 'sat.trailpos', because it was replaced in rev. 441
					// Maybe it shoud be replaced by sat.getLevel(.)?
					lowestLevel = sat.trailpos[satvar];
					// lowestLevel = sat.getLevel(satvar);
					if (lowestLevel == 0 && (sat.value(p) != l_False)) {
						fprintf(stderr, "level 0 not fixed\n");
					}
					bestVar = v;
				}
			}
			return bestVar;
		}
		if (selectionMethod == 6) {
			// fprintf(stderr, "random\n");
			int bestIndex = (int)(((double)options.size()) * rand() / (RAND_MAX + 1.0));
			return options[bestIndex];
		}
		return options[0];
		fprintf(stderr, "unexpected evidence type\n");
	}

	bool propagate() override {
		assert(check || scc);
		if (check && !propagateCheck()) {
			return false;
		}
		if (prevent && !propagatePrevent()) {
			return false;
		}
		if (scc) {
			if (so.rootSelection == 10) {
				// try all roots not fixed in self-cycles
				int numTried = 0;
				for (int root = 0; root < size; root++) {
					if (!x[root].isFixed() || x[root].getVal() != root) {
						numTried++;
						if (!propagateSCC(root)) {
							return false;
						}  // check if alldiff now broken
						bool alldiffbroken = false;
						vec<bool> valueTaken;
						for (int i = 0; i < size; i++) {
							valueTaken.push(false);
						}
						for (int i = 0; i < size; i++) {
							if (x[i].isFixed()) {
								int v = x[i].getVal();
								if (valueTaken[v]) {
									alldiffbroken = true;
								}
								valueTaken[v] = true;
							}
						}
						if (alldiffbroken) {
							break;
						}
					}
				}
				if (numTried == 0) {
					if (check) {
						return true;
					}
					return propagateCheck();
				}
			} else {
				int root = chooseRoot();
				if (root < 0)  // means all vars are fixed self-cycles
				{
					if (check) {
						return true;
					}
					return propagateCheck();
				}
				if (!propagateSCC(root)) {
					return false;
				}
			}
		}
		return true;
	}

	void clearPropState() override {
		in_queue = false;
		new_fixed.clear();
	}
};

void subcircuit(vec<IntVar*>& _x, int offset) {
	all_different(_x, CL_DOM);
	vec<IntView<> > x;
	for (int i = 0; i < _x.size(); i++) {
		_x[i]->specialiseToEL();
	}
	if (offset == 0) {
		for (int i = 0; i < _x.size(); i++) {
			x.push(IntView<>(_x[i]));
		}
	} else {
		for (int i = 0; i < _x.size(); i++) {
			x.push(IntView<4>(_x[i], 1, -offset));
		}
	}

	if (offset == 0) {
		new SubCircuit<0>(x);
	} else {
		new SubCircuit<4>(x);
	}
}

// mandatoryIndices does not need to include the start and end index
/*
void pathWithMandatoryNodes(vec<IntVar*>& _x, int _startIndex, int _endIndex, vec<int>&
_mandatoryIndices, bool _check, bool _prevent, bool _scc, bool _pruneRoot, bool _pruneSkip, bool
_fixReq, bool _generaliseScc) {
		// successors must all be different
		all_different(_x);
		// Successor of end node is start node
		if(_x[_endIndex]->setValNotR(_startIndex))
				_x[_endIndex]->setVal(_startIndex);
		// The start node and all mandatory nodes must be included (cannot have self as successor)
		if(_x[_startIndex]->remValNotR(_startIndex))
				_x[_startIndex]->remVal(_startIndex);
		for(int i = 0; i < _mandatoryIndices.size(); i++)
		{
				int index = _mandatoryIndices[i];
				if(_x[index]->remValNotR(index))
				_x[index]->remVal(index);
		}
		// nodes must form subcircuit
		vec<IntView<> > x;
		for (int i = 0; i < _x.size(); i++) _x[i]->specialiseToEL();
		for (int i = 0; i < _x.size(); i++) x.push(IntView<>(_x[i]));
		new SubCircuit(x, _startIndex, _check, _prevent, _scc, _pruneRoot,
		_pruneSkip, _fixReq, _generaliseScc);
}*/

// All nodes not in path will have own index as value
// Final node in path will have size of x as value
// Note there do not have to be any mandatory nodes, and by default
// the start and end nodes are not fixed.
// A node can be set as the start node by removing its index from the domains
// of all other nodes in x.
// A node can be set as the end node by setting its value to the size of x.
// Any node can be made mandatory by removing its own index from its domain.
void subpath(vec<IntVar*>& _x) {
	// add dummy node
	vec<IntVar*> x;
	_x.copyTo(x);
	IntVar* dummyVar;
	// note dummy node definitely in (can't have own index as value)
	createVar(dummyVar, 0, _x.size() - 1, true);
	x.push(dummyVar);

	// nodes including dummy node must form subcircuit
	subcircuit(x);
}
