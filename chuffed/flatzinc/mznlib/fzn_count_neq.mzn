predicate fzn_count_neq(array[int] of var int: x, var int: y, var int: c) =
    bool_sum_ne([x[i] == y | i in index_set(x)], c);
