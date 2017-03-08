%------------------------------------------------------------------------------%
% This file contains MiniZinc extension for Chuffed. Include this file to use
% them.
%------------------------------------------------------------------------------%

%------------------------------------------------------------------------------%
% Following search annotation is a place holders until it is includede in the
% MiniZinc distribution

/** @group annotations.search Specify search on a group of searches \a search,
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

/** @group annotations.search.varsel Choose the variable with the smallest largest value in its domain */
annotation smallest_largest;

/** @group annotations.search.varsel Choose the variable with the largest smallest value in its domain */
annotation largest_smallest;


