#include "chuffed/core/engine.h"
#include "chuffed/core/options.h"
#include "chuffed/core/propagator.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/core/sat.h"
#include "chuffed/globals/EdExplFinder.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/bool-view.h"
#include "chuffed/vars/int-var.h"
#include "chuffed/vars/int-view.h"
#include "chuffed/vars/vars.h"

#include <algorithm>
#include <cassert>
#include <climits>
#include <cstdio>
#include <iostream>

class EditDistance : public Propagator {
public:
	enum ExplLevel {
		// generate naive explanation if all seq variables are fixed only
		E_NAIVE,
		// generate explanation on any domain change,
		E_FULL,
	};

	int max_char;

	// maximum cost of any insertion/deletion operation
	int max_id_cost;
	// minimum cost of any insertion/deletion operation
	int min_id_cost;

	vec<int> insertion_cost;
	vec<int> deletion_cost;
	vec<int> substitution_cost;

	const int seqSize;
	IntView<>* const seq1;
	IntView<>* const seq2;

	const IntView<> ed;

	const ExplLevel explLevel = E_FULL;

	Tint lastBound;
	// Persistent state

	//
	// Intermediate state
	//
	EditDistance(int _max_char, vec<int>& _insertion_cost, vec<int>& _deletion_cost,
							 vec<int>& _substitution_cost, vec<IntView<> > _seq1, vec<IntView<> > _seq2,
							 IntView<> _ed)
			: max_char(_max_char),
				insertion_cost(_insertion_cost),
				deletion_cost(_deletion_cost),
				substitution_cost(_substitution_cost),
				seqSize(_seq1.size()),
				seq1(_seq1.release()),
				seq2(_seq2.release()),
				ed(_ed),
				dpMatrix(vec<int>((seqSize + 1) * (seqSize + 1))),
				cellHasChanged(vec<int>(seqSize * 2)) {
		// get maximum costs over all insertions/deletions
		max_id_cost = 0;
		for (int i = 0; i < max_char; i++) {
			max_id_cost = std::max(max_id_cost, insertion_cost[i]);
			max_id_cost = std::max(max_id_cost, deletion_cost[i]);
		}
		min_id_cost = INT_MAX;
		for (int i = 0; i < max_char; i++) {
			min_id_cost = std::min(min_id_cost, insertion_cost[i]);
			min_id_cost = std::min(min_id_cost, deletion_cost[i]);
		}

		// set maximum possible upper bound in the beginning
		lastBound = seqSize * 2 * max_id_cost;

		cellChanges = 0;
		for (int i = 0; i < seqSize * 2; i++) {
			cellHasChanged[i] = 0;
		}

#ifndef NDEBUG
		std::cout << "insertion_cost: ";
		for (int i = 0; i < max_char; i++) {
			std::cout << insertion_cost[i] << " ";
		}
		std::cout << '\n';
		std::cout << "deletion_cost: ";
		for (int i = 0; i < max_char; i++) {
			std::cout << deletion_cost[i] << " ";
		}
		std::cout << '\n';
		std::cout << "substitution_cost: ";
		for (int i = 0; i < max_char * max_char; i++) {
			std::cout << substitution_cost[i] << " ";
		}
		std::cout << '\n';
#endif

		// we set this propagator to low priority
		priority = 3;

		// attach variable views
		int offset = 0;

		for (int i = 0; i < seqSize; i++) {
			seq1[i].attach(this, offset + i, EVENT_C);
		}

		offset += seqSize;

		for (int i = 0; i < seqSize; i++) {
			seq2[i].attach(this, offset + i, EVENT_C);
		}

		// in the future we could also wake the propagator on changes on the edit distance
		offset += seqSize;
		ed.attach(this, offset, EVENT_L);

		// insert 0 values into matrices
		for (int i = 0; i < (seqSize + 1) * (seqSize + 1); i++) {
			dpMatrix[i] = 0;
		}
	}

	void wakeup(int i, int c) override {
		if (i < seqSize * 2) {
			if (((unsigned)c & EVENT_C) != 0U) {
				if (cellHasChanged[i] == 0) {
					cellHasChanged[i] = 1;
					cellChanges++;
				}
			}
		}

		pushInQueue();
	}

	bool propagate() override {
		// Step 1:
		// Update dp matrix according to change
		//

#ifndef NDEBUG
		std::cout << "lastBound = " << lastBound << '\n';
		std::cout << "cellChanges = " << cellChanges << '\n';
		std::cout << "cellHasChanged = [";
		for (int i = 0; i < seqSize * 2; i++) {
			std::cout << cellHasChanged[i] << " ";
		}
		std::cout << "]" << '\n';
#endif

		const int ub = std::min(2 * seqSize * max_id_cost, lastBound + cellChanges * 2 * max_id_cost);

		updateDpMatrix(ub);
		cellChanges = 0;
		for (int i = 0; i < seqSize * 2; i++) {
			cellHasChanged[i] = 0;
		}

#ifndef NDEBUG
		printCurrentDpMatrix();
#endif

		// Step 2:
		// Propagate lower bound to edit distance, and add explanation
		//

		// calc edit distance
		const int editDistanceLB = getEditDistanceLB();

		lastBound = editDistanceLB;

		if (ed.getMin() < editDistanceLB) {
#ifndef NDEBUG
			std::cout << "ED " << editDistanceLB << '\n';
#endif

			if (explLevel == E_NAIVE) {
				// in case of naive explanation, check if all variables are fixed
				for (int i = 0; i < seqSize; i++) {
					if (!seq1[i].isFixed() || !seq2[i].isFixed()) {
						return true;
					}
				}
			}
			if (ed.setMinNotR(editDistanceLB)) {
				Clause* r = nullptr;
				if (so.lazy) {
					switch (explLevel) {
						case E_NAIVE:
							r = getNaiveExplanation();
							break;
						case E_FULL:
							EdExplFinder edExplFinder;
							// launch inequality finder for explanation
							r = edExplFinder.FindEdExplanation(max_char, &insertion_cost, &deletion_cost,
																								 &substitution_cost, seq1, seq2, &dpMatrix,
																								 editDistanceLB, seqSize, min_id_cost);
							break;
					}

					if (!ed.setMin(editDistanceLB, r)) {
						return false;
					}
				}
			}
		}

		return true;
	}

private:
	// The matrix will store the values for the dynamic programming matrix
	vec<int> dpMatrix;

	int cellChanges;
	vec<int> cellHasChanged;

	int getMinimumDeletionCosts(IntView<>* const iVar) {
		int min_deletion_costs = INT_MAX;
		// find minimum deletion costs
		for (const int it : *iVar) {
			if (it > 0) {
				min_deletion_costs = std::min(min_deletion_costs, deletion_cost[it - 1]);
			} else {
				return 0;
			}
		}
		assert(min_deletion_costs < INT_MAX);

		return min_deletion_costs;
	}

	int getMinimumInsertionCosts(IntView<>* const jVar) {
		int min_insertion_costs = INT_MAX;
		// find minimum insertion costs
		for (const int it : *jVar) {
			if (it > 0) {
				min_insertion_costs = std::min(min_insertion_costs, insertion_cost[it - 1]);
			} else {
				return 0;
			}
		}
		assert(min_insertion_costs < INT_MAX);

		return min_insertion_costs;
	}

	int getMinimumSubstitutionCost(IntView<>* const iVar, IntView<>* const jVar) {
		int min_substitution_costs = INT_MAX;

		// find minimum substitution costs
		for (const int i_val : *iVar) {
			for (const int j_val : *jVar) {
				if (i_val == 0 && j_val == 0) {
					return 0;
				}
				if (i_val == 0 && j_val != 0) {
					min_substitution_costs = std::min(min_substitution_costs, deletion_cost[j_val - 1]);
				}
				if (i_val != 0 && j_val == 0) {
					min_substitution_costs = std::min(min_substitution_costs, insertion_cost[i_val - 1]);
				}
				if (i_val != 0 && j_val != 0) {
					min_substitution_costs =
							std::min(min_substitution_costs, substitution_cost[substCoord(i_val, j_val)]);
				}
			}
		}

		assert(min_substitution_costs < INT_MAX);

		return min_substitution_costs;
	}

	void updateDpPosition(int i, int j, int d) {
		IntView<>* const iVar = &seq1[i - 1];
		IntView<>* const jVar = &seq2[j - 1];

		if (i == 0 && j == 0) {
			// top left position is always 0
		} else if (i == 0) {
			const int min_insertion_costs = getMinimumInsertionCosts(jVar);
			dpMatrix[matrixCoord(i, j)] = dpMatrix[matrixCoord(0, j - 1)] + min_insertion_costs;
		} else if (j == 0) {
			const int min_deletion_costs = getMinimumDeletionCosts(iVar);
			dpMatrix[matrixCoord(i, j)] = dpMatrix[matrixCoord(i - 1, 0)] + min_deletion_costs;
		} else {
			int minChange = seqSize * 2 * max_id_cost;

			if (j - 1 >= i - d) {
				const int min_insertion_costs = getMinimumInsertionCosts(jVar);
				minChange = std::min(minChange, dpMatrix[matrixCoord(i, j - 1)] + min_insertion_costs);
			}
			if (j < i + d) {
				const int min_deletion_costs = getMinimumDeletionCosts(iVar);
				minChange = std::min(minChange, dpMatrix[matrixCoord(i - 1, j)] + min_deletion_costs);
			}

			if (iVar->isFixed() && jVar->isFixed() && iVar->getVal() == jVar->getVal()) {
				// both values fixed and equal
				minChange = std::min(minChange, dpMatrix[matrixCoord(i - 1, j - 1)]);
			} else {
				const int minDiagonalCost = getMinimumSubstitutionCost(iVar, jVar);
				const int diagonalCost = dpMatrix[matrixCoord(i - 1, j - 1)] + minDiagonalCost;
				minChange = std::min(minChange, diagonalCost);
			}
			dpMatrix[matrixCoord(i, j)] = minChange;
		}
	}

	int matrixCoord(int i, int j) const { return i * (seqSize + 1) + j; }

	int substCoord(int c1, int c2) const { return (c1 - 1) * max_char + (c2 - 1); }

	void updateDpMatrix(int upperBound) {
		//
		// First update regular matrix
		//

		// count num possible 0 insertions
		int possible_0_inserts = 0;
		int possible_0_deletes = 0;
		for (int i = 0; i < seqSize; i++) {
			if (seq1[i].indomain(0)) {
				possible_0_inserts++;
			}
			if (seq2[i].indomain(0)) {
				possible_0_deletes++;
			}
		}

		// d = distance to diagonal that should be calculated in the matrix
		const int d = upperBound / min_id_cost + std::max(possible_0_inserts, possible_0_deletes);

#ifndef NDEBUG
		std::cout << "d = " << d << '\n';
#endif

		for (int i = 0; i < seqSize + 1; i++) {
			const int startCol = std::max(0, i - d);
			const int endCol = std::min(seqSize, i + d);
			for (int j = startCol; j < endCol + 1; j++) {
				updateDpPosition(i, j, d);
			}
		}
	}

	int getEditDistanceLB() {
		// retrieve LB from dp matrix
		return dpMatrix[matrixCoord(seqSize, seqSize)];
	}

	// the naive explanation will include current bounds for all variables
	Clause* getNaiveExplanation() const {
		// count number of possible values in total

		const int clauseSize = seqSize * 2 + 1;

		Clause* r = Reason_new(clauseSize);

		int offset = 1;

		// insert all clauses for each variable in sequence 1
		for (int i = 0; i < seqSize; i++) {
			// x != val
			(*r)[offset + i] = seq1[i].getLit(seq1[i].getVal(), LR_NE);
		}
		offset += seqSize;
		// insert all clauses for each variable in sequence 2
		for (int i = 0; i < seqSize; i++) {
			// x != val
			(*r)[offset + i] = seq2[i].getLit(seq2[i].getVal(), LR_NE);
		}

		return r;
	}

	void printCurrentDpMatrix() {
		std::cout << "+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++" << '\n';
		std::cout << " Sequence1: " << '\n';
		for (int i = 0; i < seqSize; i++) {
			std::cout << "{";
			for (const int it : seq1[i]) {
				std::cout << it << ",";
			}
			if (seq1[i].isFixed()) {
				std::cout << "!";
			}
			std::cout << "};";
		}
		std::cout << '\n';

		std::cout << " Sequence2: " << '\n';
		for (int i = 0; i < seqSize; i++) {
			std::cout << "{";
			for (const int it : seq2[i]) {
				std::cout << it << ",";
			}
			if (seq2[i].isFixed()) {
				std::cout << "!";
			}
			std::cout << "};";
		}
		std::cout << '\n';
		std::cout << '\n';

		std::cout << " Current dp matrix: " << '\n';

		std::cout << "   ";
		for (int i = 0; i < seqSize + 1; i++) {
			printf("%2d ", i);
		}
		std::cout << '\n';

		for (int i = 0; i < seqSize + 2; i++) {
			std::cout << "---";
		}
		std::cout << '\n';

		for (int i = 0; i < seqSize + 1; i++) {
			for (int j = -1; j < seqSize + 1; j++) {
				if (j == -1) {
					printf("%2d|", i);
				} else {
					printf("%2d ", dpMatrix[matrixCoord(i, j)]);
				}
			}
			std::cout << '\n';
		}
	}
};

void edit_distance(int max_char, vec<int>& insertion_cost, vec<int>& deletion_cost,
									 vec<int>& substitution_cost, vec<IntVar*>& seq1, vec<IntVar*>& seq2,
									 IntVar* ed) {
	vec<IntView<> > s1;
	for (int i = 0; i < seq1.size(); i++) {
		seq1[i]->specialiseToEL();
		s1.push(IntView<>(seq1[i]));
	}
	vec<IntView<> > s2;
	for (int i = 0; i < seq2.size(); i++) {
		seq2[i]->specialiseToEL();
		s2.push(IntView<>(seq2[i]));
	}

	// insert clauses to ensure 0 values appear only at the end of each sequence
	for (int i = 0; i < seq1.size() - 1; i++) {
		// x_i >= 1 v x_i+1 <= 0
		vec<Lit> cl;
		cl.push(seq1[i]->getLit(1, LR_GE));
		cl.push(seq1[i + 1]->getLit(0, LR_LE));
		sat.addClause(cl);
	}
	for (int i = 0; i < seq2.size() - 1; i++) {
		// x_i >= 1 v x_i+1 <= 0
		vec<Lit> cl;
		cl.push(seq2[i]->getLit(1, LR_GE));
		cl.push(seq2[i + 1]->getLit(0, LR_LE));
		sat.addClause(cl);
	}

	new EditDistance(max_char, insertion_cost, deletion_cost, substitution_cost, s1, s2,
									 IntView<>(ed));
}
