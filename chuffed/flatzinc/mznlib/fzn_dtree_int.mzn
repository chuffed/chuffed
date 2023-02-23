predicate chuffed_dtree(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    var int: r,
    array[int] of var bool: ns,
    array[int] of var bool: es,
);
predicate fzn_dtree(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    var int: r,
    array[int] of var bool: ns,
    array[int] of var bool: es,
) = chuffed_dtree(N, E, from, to, r, ns, es);