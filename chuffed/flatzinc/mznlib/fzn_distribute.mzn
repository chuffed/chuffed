%-----------------------------------------------------------------------------%
% Requires that 'card[i]' is the number of occurrences of 'value[i]' in 'base'.
%
% XXX: currently the values in 'value' need not be distinct.  Perhaps they
%      should be?
%-----------------------------------------------------------------------------%
predicate fzn_distribute(array[int] of var int: card,
                     array[int] of var int: value,
                     array[int] of var int: base) =
    assert(index_set(card) == index_set(value),
        "distribute: card and value arrays must have identical index sets",
        forall (i in index_set(card)) (
            bool_sum_eq([value[i] = base[j] | j in index_set(base)], card[i])
        )
    );

