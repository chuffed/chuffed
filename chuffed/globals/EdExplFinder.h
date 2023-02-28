//
// Created by Felix Winter on 08.04.2019.
//

#ifndef CHUFFED_EDEXPLFINDER_H
#define CHUFFED_EDEXPLFINDER_H

#include <chuffed/core/propagator.h>
#include <chuffed/support/vec.h>

#include <queue>
#include <vector>

/**
 * Class that will help to find variable inequalities used to explain propagation of lcs bounds
 */
class EdExplFinder {
public:
	/**
	 *
	 * @param _max_char: maximum character of alphabet
	 * @param _insertion_cost: vector containing character insertion costs
	 * @param _deletion_cost: vector containing character deletion costs
	 * @param _substitution_cost: vector containing character substitution costs
	 * @param seq1: string sequence 1
	 * @param seq2: string sequence 2
	 * @param dpMatrix: a matrix including the shortest edit distance to each position of the dynamic
	 * programming matrix
	 * @param lb: a valid lowerbound for the edit distance of two sequences that have been used to
	 * build the dp matrices
	 * @param seqSize: the size of the sequences for which explanation inequalities should be
	 * determined
	 * @param min_id_cost: minimum insertion/deletion cost to determine which "diagonal" of the matrix
	 * should be calculated
	 * @return An explanation clause for a propagation on the edit distance lower bound
	 */
	Clause* FindEdExplanation(int _max_char, const vec<int>* _insertion_cost,
														const vec<int>* _deletion_cost, const vec<int>* _substitution_cost,
														IntView<>* _seq1, IntView<>* _seq2, const vec<int>* _dpMatrix, int _lb,
														int _seqSize, int _min_id_cost);
	~EdExplFinder();

	EdExplFinder();

private:
	IntView<>* seq1{};

	IntView<>* seq2;

	// maximum character of alphabet
	int max_char;

	// minimum insertion/deletion cost
	int min_id_cost;

	// vector of character insertion costs
	const vec<int>* insertion_cost;
	// vector of character deletion costs
	const vec<int>* deletion_cost;
	// vector of character substitution costs
	const vec<int>* substitution_cost;

	// structures to capture the characters that should be excluded for the sequence positions
	// flat 2d vectors (sequence positions * characters)
	std::vector<bool>* seq1ExcludedCharacters{};
	std::vector<bool>* seq2ExcludedCharacters{};

	// read only pointer to dpMatrix
	const vec<int>* dpMatrix;
	// size of the sequences that are compared
	int seqSize;
	// valid lower bound for the edit distance
	int lb;

	/**
	 * Do a breadth first search to fill shortest path matrix
	 */
	void bfs_shortest_path();

	int excludedCharCoord(int i, int c) const;
	int matrixCoord(int i, int j) const;
	int substCoord(int c1, int c2) const;

	void clean_data_structures();

	/**
	 * print final state of shortest path matrix and found inequalities
	 */
	void debug_print(std::vector<int>* shortestPathMatrix) const;
};

#endif  // CHUFFED_EDEXPLFINDER_H
