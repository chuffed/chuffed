
predicate value_precede_seq(array [int] of var int: x);

predicate value_precede_chain_dec(array [int] of int: vs, array [int] of var int: xs) =
  forall (i in index_set(vs) diff {1}) (value_precede(vs[i-1], vs[i], xs));

predicate value_precede_chain(array [int] of int: vs, array [int] of var int: xs) =
  let { int: N = card(index_set(vs)) ;
        array [int] of int: vs_1d = array1d(1..N, vs);
        int: M = ub_array(xs); } in
  % Is this actually a sequence?
  if forall (i in 2..N) (vs_1d[i-1]+1 = vs_1d[i])
      /\ vs_1d[N] >= M then
    value_precede_seq(xs)
  else
    value_precede_chain_dec(vs_1d, xs)
  endif;
