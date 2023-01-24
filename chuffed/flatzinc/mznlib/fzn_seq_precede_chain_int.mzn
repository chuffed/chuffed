predicate chuffed_seq_precede(array [int] of var int: X);

predicate fzn_seq_precede_chain_int(array[int] of var int: X) =
  chuffed_seq_precede(X);
