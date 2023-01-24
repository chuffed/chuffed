predicate chuffed_value_precede(int: s, int: t, array [int] of var int: x);

predicate fzn_value_precede_int(int: s, int: t, array[int] of var int: x) =
  chuffed_value_precede(s, t, x);
