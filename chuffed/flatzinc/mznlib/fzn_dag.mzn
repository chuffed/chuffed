predicate chuffed_dag(
    array[int] of int: from,
    array[int] of int: to,
    array[int] of var bool: ns,
    array[int] of var bool: es,
);

predicate fzn_dag(
    array[int] of int: from,
    array[int] of int: to,
    array[int] of var bool: ns,
    array[int] of var bool: es,
) = chuffed_dag(from, to, ns, es);
