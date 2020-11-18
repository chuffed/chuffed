% Longest common subsequence distance (insertion cost = deletion cost = 1, substitution cost = 2)
predicate edit_distance(int: max_char,
                        array[int] of var int: S1,
                        array[int] of var int: S2,
                        var int: ED) =
    edit_distance(max_char, 1, 1, 2, S1, S2, ED);

predicate edit_distance(int: max_char,
                        int: C_ins,
                        int: C_del,
                        int: C_sub,
                        array[int] of var int: S1,
                        array[int] of var int: S2,
                        var int: ED) =
    let { int: u1 = length(S1);
          int: u2 = length(S2);
        } in
    edit_distance(max_char, [C_ins | i in 1..max_char], [C_del | i in 1..max_char], array2d(1..max_char, 1..max_char, [if i == j then 0 else C_sub endif | i in 1..max_char, j in 1..max_char]), S1, S2, ED);

% Edit distance propagator implementation for chuffed.
% Based on the paper "Explaining Propagators for String Edit Distance Constraints", Winter et al., AAAI 2020.
predicate edit_distance(int: max_char,
                        array[int] of int: W_ins,
                        array[int] of int: W_del,
                        array[int, int] of int: W_sub,
                        array[int] of var int: S1,
                        array[int] of var int: S2,
                        var int: ED);