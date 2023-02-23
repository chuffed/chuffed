predicate chuffed_connected(
    array[int] of $$N: from,
    array[int] of $$N: to,
    array[$$N] of var bool: ns,
    array[int] of var bool: es,
);

predicate fzn_connected(
    array[int] of $$N: from,
    array[int] of $$N: to,
    array[$$N] of var bool: ns,
    array[int] of var bool: es,
) = chuffed_connected(from, to, ns, es);