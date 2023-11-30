//
// Created by Felix Winter on 08.04.2019.
//
#include "chuffed/globals/EdExplFinder.h"

#include "chuffed/core/propagator.h"
#include "chuffed/core/sat-types.h"
#include "chuffed/support/vec.h"
#include "chuffed/vars/int-view.h"
#include "chuffed/vars/vars.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <queue>
#include <set>
#include <utility>
#include <vector>

EdExplFinder::EdExplFinder()

		= default;

Clause*

EdExplFinder::FindEdExplanation(int _max_char, const vec<int>* _insertion_cost,
																const vec<int>* _deletion_cost, const vec<int>* _substitution_cost,
																IntView<>* const _seq1, IntView<>* const _seq2,
																const vec<int>* _dpMatrix, int _lb, int _seqSize,
																int _min_id_cost) {
	max_char = _max_char;
	insertion_cost = _insertion_cost;
	deletion_cost = _deletion_cost;
	substitution_cost = _substitution_cost;
	seq1 = _seq1;
	seq2 = _seq2;
	seqSize = _seqSize;
	lb = _lb;
	min_id_cost = _min_id_cost;
	dpMatrix = _dpMatrix;

	seq1ExcludedCharacters =
			new std::vector<bool>(static_cast<size_t>(seqSize * (max_char + 1)), false);
	seq2ExcludedCharacters =
			new std::vector<bool>(static_cast<size_t>(seqSize * (max_char + 1)), false);

	// do breadth first search fill inequality vector
	bfs_shortest_path();

	std::vector<Lit> litVector;

	// create literals for seq1 restrictions
	for (int i = 0; i < seqSize; i++) {
		int l = 0;
		for (int c1 = 0; c1 <= max_char; c1++) {
			if (!(*seq1ExcludedCharacters)[excludedCharCoord(i, c1)]) {
				break;
			}
			l++;
		}
		int u = max_char;
		for (int c1 = max_char; c1 >= 0; c1--) {
			if (!(*seq1ExcludedCharacters)[excludedCharCoord(i, c1)]) {
				break;
			}
			u--;
		}
		// create x_i >= l
		if (l > 0) {
			// we insert x_i <= l-1, as we have to actually negate the inequality
#ifndef NDEBUG
			std::cout << "x_" << i << " >= " << l << '\n';
#endif
			litVector.push_back(seq1[i].getLit(l - 1, LR_LE));
		}

		// create x_i <= u
		if (u < max_char && l <= u) {
			// we insert x_i >= u+1, as we have to actually negate the inequality
#ifndef NDEBUG
			std::cout << "x_" << i << " <= " << u << '\n';
#endif
			litVector.push_back(seq1[i].getLit(u + 1, LR_GE));
		}

		// create remaining inequalities (x_i != c1)
		for (int c1 = l; c1 <= u; c1++) {
			if ((*seq1ExcludedCharacters)[excludedCharCoord(i, c1)]) {
#ifndef NDEBUG
				std::cout << "x_" << i << " != " << c1 << '\n';
#endif
				// we insert x_i = c1, as we have to actually negate the inequality
				litVector.push_back(seq1[i].getLit(c1, LR_EQ));
			}
		}
	}

	// create literals for seq2 restrictions
	for (int j = 0; j < seqSize; j++) {
		int l = 0;
		for (int c1 = 0; c1 <= max_char; c1++) {
			if (!(*seq2ExcludedCharacters)[excludedCharCoord(j, c1)]) {
				break;
			}
			l++;
		}
		int u = max_char;
		for (int c1 = max_char; c1 >= 0; c1--) {
			if (!(*seq2ExcludedCharacters)[excludedCharCoord(j, c1)]) {
				break;
			}
			u--;
		}
		// create y_i >= l
		if (l > 0) {
#ifndef NDEBUG
			std::cout << "y_" << j << " >= " << l << '\n';
#endif
			// we insert y_i <= l-1, as we have to actually negate the inequality
			litVector.push_back(seq2[j].getLit(l - 1, LR_LE));
		}
		// create y_i <= u
		if (u < max_char && l <= u) {
#ifndef NDEBUG
			std::cout << "y_" << j << " <= " << u << '\n';
#endif
			// we insert y_i >= u+1, as we have to actually negate the inequality
			litVector.push_back(seq2[j].getLit(u + 1, LR_GE));
		}

		// create remaining inequalities (y_i != c1)
		for (int c1 = l; c1 <= u; c1++) {
			if ((*seq2ExcludedCharacters)[excludedCharCoord(j, c1)]) {
#ifndef NDEBUG
				std::cout << "y_" << j << " != " << c1 << '\n';
#endif
				// we insert y_i = c1, as we have to actually negate the inequality
				litVector.push_back(seq2[j].getLit(c1, LR_EQ));
			}
		}
	}

	const int totalClauseLength = litVector.size();

	// generate full clause
	Clause* r = Reason_new(totalClauseLength + 1);

	int offset = 1;
	for (auto& it : litVector) {
		(*r)[offset] = it;
		offset++;
	}

	return r;
}

int EdExplFinder::matrixCoord(int i, int j) const { return i * (seqSize + 1) + j; }

int EdExplFinder::excludedCharCoord(int i, int c) const { return i * (max_char + 1) + c; }

int EdExplFinder::substCoord(int c1, int c2) const { return (c1 - 1) * max_char + (c2 - 1); }

void EdExplFinder::bfs_shortest_path() {
	auto* shortestPathMatrix =
			new std::vector<int>(static_cast<size_t>((seqSize + 1) * (seqSize + 1)), lb + 1);
	// set shortest path for bottom right position to 0 cost
	(*shortestPathMatrix)[matrixCoord(seqSize, seqSize)] = 0;

	auto* nodeQueue = new std::queue<std::pair<int, int> >();
	std::set<std::pair<int, int> > node_set;
	// start with bottom right position
	const std::pair<int, int> start_node = std::pair<int, int>(seqSize, seqSize);
	nodeQueue->push(start_node);
	node_set.insert(start_node);

	// d = distance to diagonal that should be calculated in the matrix
	const int d = lb / min_id_cost;

	while (!nodeQueue->empty()) {
		const std::pair<int, int> currentNode = nodeQueue->front();
		nodeQueue->pop();
		node_set.erase(currentNode);

		const int i = currentNode.first;
		const int j = currentNode.second;

		const int s_ij = (*shortestPathMatrix)[matrixCoord(i, j)];

		if (s_ij >= lb) {
			continue;
		}

		//
		// process move to the left
		//
		if (j - 1 >= 0 && j - 1 >= i - d) {
			// check if 0 is forbidden in any sequence position that is larger or equal than the current
			// position
			int cj_start = 0;
			for (int k = j - 1; k < seqSize; k++) {
				if ((*seq2ExcludedCharacters)[excludedCharCoord(k, 0)]) {
					// if 0 is forbidden, we do not need to include it in the explanation
					cj_start = 1;
					break;
				}
			}
			for (int c = cj_start; c <= max_char; c++) {
				const int ins_cost = c == 0 ? 0 : (*insertion_cost)[c - 1];
				const int d_ij_minus_1 = (*dpMatrix)[matrixCoord(i, j - 1)];
				if (d_ij_minus_1 + ins_cost + s_ij < lb) {
					// exclude character for position in explanation if a cheaper path could be established
					(*seq2ExcludedCharacters)[excludedCharCoord(j - 1, c)] = true;
				} else {
					// update costs and push node to queue
					const int s_ij_minus_1 = (*shortestPathMatrix)[matrixCoord(i, j - 1)];
					(*shortestPathMatrix)[matrixCoord(i, j - 1)] = std::min(s_ij_minus_1, s_ij + ins_cost);

					const std::pair<int, int> node = std::pair<int, int>(i, j - 1);
					if (node_set.count(node) == 0) {
						nodeQueue->push(node);
						node_set.insert(node);
					}
				}
			}
		}

		//
		// process upwards move
		//
		if (i - 1 >= 0 && j < i + d) {
			int ci_start = 0;
			// check if 0 is forbidden in any sequence position that is larger or equal than the current
			// position
			for (int k = i - 1; k < seqSize; k++) {
				if ((*seq1ExcludedCharacters)[excludedCharCoord(k, 0)]) {
					// if 0 is forbidden, we do not need to include it in the explanation
					ci_start = 1;
					break;
				}
			}
			for (int c = ci_start; c <= max_char; c++) {
				const int del_cost = c == 0 ? 0 : (*deletion_cost)[c - 1];
				const int d_i_minus_1_j = (*dpMatrix)[matrixCoord(i - 1, j)];
				if (d_i_minus_1_j + del_cost + s_ij < lb) {
					// exclude character for position in explanation if a cheaper path could be established
					(*seq1ExcludedCharacters)[excludedCharCoord(i - 1, c)] = true;
				} else {
					// update costs and push node to queue
					const int s_i_minus_1_j = (*shortestPathMatrix)[matrixCoord(i - 1, j)];
					(*shortestPathMatrix)[matrixCoord(i - 1, j)] = std::min(s_i_minus_1_j, s_ij + del_cost);

					const std::pair<int, int> node = std::pair<int, int>(i - 1, j);
					if (node_set.count(node) == 0) {
						nodeQueue->push(node);
						node_set.insert(node);
					}
				}
			}
		}

		//
		// process diagonal move
		//
		if (i - 1 >= 0 && j - 1 >= 0) {
			for (int c1 = 1; c1 <= max_char; c1++) {
				for (int c2 = 1; c2 <= max_char; c2++) {
					const int d_i_minus_1_j_minus_1 = (*dpMatrix)[matrixCoord(i - 1, j - 1)];
					const int subst_cost = (*substitution_cost)[substCoord(c1, c2)];

					if (d_i_minus_1_j_minus_1 + subst_cost + s_ij < lb) {
						// we can either exclude the character for seq1 or seq2
						if (seq1[i - 1].indomain(c1)) {
							// if seq1 contains c1, we exclude c2 from seq2
							(*seq2ExcludedCharacters)[excludedCharCoord(j - 1, c2)] = true;
						} else {
							// if seq2 contains c2, or neither seq1/seq2 contain c1/c2 we exclude c1 from seq1
							(*seq1ExcludedCharacters)[excludedCharCoord(i - 1, c1)] = true;
						}
					} else {
						const int s_i_minus_1_j_minus_1 = (*shortestPathMatrix)[matrixCoord(i - 1, j - 1)];
						(*shortestPathMatrix)[matrixCoord(i - 1, j - 1)] =
								std::min(s_i_minus_1_j_minus_1, s_ij + subst_cost);

						const std::pair<int, int> node = std::pair<int, int>(i - 1, j - 1);
						if (node_set.count(node) == 0) {
							nodeQueue->push(node);
							node_set.insert(node);
						}
					}
				}
			}
		}
	}

#ifndef NDEBUG
	debug_print(shortestPathMatrix);
#endif

	delete shortestPathMatrix;
	delete nodeQueue;
}

EdExplFinder::~EdExplFinder() { clean_data_structures(); }

void EdExplFinder::clean_data_structures() {
	delete seq1ExcludedCharacters;
	delete seq2ExcludedCharacters;
}

void EdExplFinder::debug_print(std::vector<int>* shortestPathMatrix) const {
	std::cout << "***************************************************************" << '\n';

	std::cout << "shortest path matrix:" << '\n';

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
				printf("%2d ", (*shortestPathMatrix)[matrixCoord(i, j)]);
			}
		}
		std::cout << '\n';
	}

	std::cout << "***************************************************************" << '\n';
}
