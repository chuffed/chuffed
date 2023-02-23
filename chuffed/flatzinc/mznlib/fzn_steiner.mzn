predicate chuffed_steiner(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    array[int] of int: w,
    array[int] of var bool: ns,
    array[int] of var bool: es,
    var int: K,
);
predicate fzn_steiner(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    array[int] of int: w,
    array[int] of var bool: ns,
    array[int] of var bool: es,
    var int: K,
) = chuffed_steiner(N, E, from, to, w, ns, es, K);