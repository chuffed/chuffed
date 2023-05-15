predicate chuffed_connected(
    array[int] of int: from,
    array[int] of int: to,
    array[int] of var bool: ns,
    array[int] of var bool: es,
);

predicate fzn_connected(
    array[int] of int: from,
    array[int] of int: to,
    array[int] of var bool: ns,
    array[int] of var bool: es,
) = chuffed_connected(from, to, ns, es);
