predicate chuffed_dpath(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    var int: s,
    var int: t,
    array[int] of var bool: ns,
    array[int] of var bool: es,
);
predicate fzn_dpath(
    int: N,
    int: E,
    array[int] of int: from,
    array[int] of int: to,
    var int: s,
    var int: t,
    array[int] of var bool: ns,
    array[int] of var bool: es,
) = chuffed_dpath(N, E, from, to, s, t, ns, es);