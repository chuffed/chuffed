predicate fzn_count_neq_par(array[int] of var int: x, int: y, int: c) =
    bool_sum_ne([x[i] == y | i in index_set(x)], c);
