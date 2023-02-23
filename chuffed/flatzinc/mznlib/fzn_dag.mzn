predicate chuffed_dag(
    array[int] of $$N: from,
    array[int] of $$N: to,
    array[$$N] of var bool: ns,
    array[int] of var bool: es,
);

predicate fzn_dag(
    array[int] of $$N: from,
    array[int] of $$N: to,
    array[$$N] of var bool: ns,
    array[int] of var bool: es,
) = chuffed_dag(from, to, ns, es);