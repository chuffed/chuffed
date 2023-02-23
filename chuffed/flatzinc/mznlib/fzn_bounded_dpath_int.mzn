predicate chuffed_bounded_dpath(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    array[int] of int: w,
    var int: s,
    var int: t,
    array[int] of var bool: ns,
    array[int] of var bool: es,
    var int: K,
);
predicate fzn_bounded_dpath(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    array[int] of int: w,
    var int: s,
    var int: t,
    array[int] of var bool: ns,
    array[int] of var bool: es,
    var int: K,
) = chuffed_bounded_dpath(N, E, from, to, w, s, t, ns, es, K);