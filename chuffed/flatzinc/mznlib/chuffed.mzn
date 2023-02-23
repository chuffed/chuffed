%------------------------------------------------------------------------------%
% This file contains MiniZinc extension for Chuffed. Include this file to use
% them.
%------------------------------------------------------------------------------%

/***
 @groupdef chuffed Additional declarations for Chuffed
 
 These annotations and predicates are available for the Chuffed
 solver. In order to use them in a model, include the file "chuffed.mzn".
*/


%------------------------------------------------------------------------------%
% Range Size of an Integer variable

function var int: range_size(var int: x) = 
    let {
        var 1..ub(x) - lb(x) + 1: rs;
        constraint range_size_fzn(x, rs);
    } in rs;

predicate range_size_fzn(var int: x, var int: rs);


/** @group chuffed 
    Constrains the subgraph \a vs and \a es of a given directed graph to be a minimal spanning tree with weight \a K.

    @param N: the number of nodes in the given graph
    @param E: the number of edges in the given graph
    @param from: the leaving node 1..\a N for each edge
    @param to: the entering node 1..\a N for each edge
    @param w: the weight of each edge
    @param vs: a Boolean for each node whether it is in the subgraph
    @param es: a Boolean for each edge whether it is in the subgraph
    @param K: the cost of the edges in the minimal spanning tree
*/
predicate chuffed_minimal_spanning_tree(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    array[int] of int: w,
    array[int] of var bool: vs,
    array[int] of var bool: es,
    var int: K,
);

/***
 @groupdef chuffed.annotations Additional Chuffed search annotations
*/


%------------------------------------------------------------------------------%
% Following search annotation is a place holders until it is included in the
% MiniZinc distribution

/** @group chuffed.annotations Specify search on a group of searches \a search,
  for which variables \a x act as delegates for the search selection with 
  variable selection strategy \a select, and exploration strategy \a explore.
*/
annotation priority_search(
    array[int] of var int: x,
    array[int] of ann: search,
    ann: select,
    ann: explore,
);

%------------------------------------------------------------------------------%
% Following variable selection annotations are just place holders until they are
% included in the MiniZinc distributions.

/** @group chuffed.annotations Choose a random variable */
annotation random_order;

/** @group chuffed.annotations Choose the variable with the smallest largest value in its domain */
annotation smallest_largest;

/** @group chuffed.annotations Choose the variable with the largest smallest value in its domain */
annotation largest_smallest;

/** @group chuffed.annotations annotation for assumption handling. */
annotation assume(array [int] of var bool);
