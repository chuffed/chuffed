
function int: rank_of(array [int] of int: x, int: k) =
  let {
    int: n = length(x) ;
    array [int] of int: z = array1d(0..n, [k] ++ x) ;
  } in
  max (i in 0..n where z[i] = k) (i);
     
function var int: rank_of_pos(array [int] of int: vs, var int: x) =
    [ rank_of(vs, i) | i in 1..ub(x) ][x];
  
function array [int] of var int:
  rank_of_array(array [int] of int: vs, array [int] of var int: xs) =
  let {
    int: l = lb_array(xs) ;
    array [int] of var int: zs = [ xs[i] - (l-1) | i in index_set(xs) ] ;
    array [int] of int: ks = [ vs[i] - (l-1) | i in index_set(vs) ] ;
  } in
  [ rank_of_pos(ks, zs[i]) | i in index_set(zs) ];

predicate chuffed_seq_precede(array [int] of var int: x);

predicate value_precede_chain_dec(array [int] of int: vs, array [int] of var int: xs) =
  forall (i in index_set(vs) diff {1}) (value_precede(vs[i-1], vs[i], xs));

predicate value_precede_chain(array [int] of int: vs, array [int] of var int: xs) =
  let { int: N = card(index_set(vs)) ;
        array [int] of int: vs_1d = array1d(1..N, vs);
        int: M = ub_array(xs); } in
  % Is this actually a sequence?
  if N <= 1 then
    true
  else
    if N = 2 then
      value_precede(vs_1d[1], vs_1d[2], xs)
    else
      if forall (i in 2..N) (vs_1d[i-1]+1 = vs_1d[i])
          /\ vs_1d[N] >= M then
        chuffed_seq_precede([x - lb_array(vs) + 1 | x in xs])
      else
        % value_precede_chain_dec(vs_1d, xs)
        chuffed_seq_precede(rank_of_array(vs, xs))
      endif
    endif
  endif;
