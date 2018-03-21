predicate chuffed_value_precede(int: s, int: t, array [int] of var int: x);

predicate value_precede_int_dec(int: s, int: t, array[int] of var int: x) =
    let {
        int: imin = min(index_set(x)),
        int: imax = max(index_set(x)),
        array[imin..imax+1] of var bool: b
    } in (
        forall (i in imin..imax) (let {
            var bool: xis = (x[i] == s)
        } in
            (xis -> (b[i+1] == true))
        /\  ((not xis) -> (b[i] == b[i+1]))
        /\  ((not b[i]) -> (x[i] != t))
        )
    /\  b[imin] == false
    );

predicate value_precede_int(int: s, int: t, array [int] of var int: x) =
  chuffed_value_precede(s, t, x);
  %value_precede_int_dec(s, t, x);
