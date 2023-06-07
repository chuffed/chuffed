predicate chuffed_tree(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    array[int] of var bool: ns,
    array[int] of var bool: es,
);

predicate fzn_tree(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    var int: r,
    array[int] of var bool: ns,
    array[int] of var bool: es,
) = ns[r] /\ chuffed_tree(N, E, from, to, ns, es);