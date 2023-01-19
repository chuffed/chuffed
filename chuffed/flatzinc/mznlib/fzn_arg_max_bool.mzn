predicate chuffed_maximum_arg_bool(array[int] of var bool: x, int: offset, var int: y);

predicate fzn_maximum_arg_bool(array[int] of var bool: x, var int: i) =
  let { 
    set of int: ii = index_set(x);
    var min(ii)..max(ii)+1: idx;
    constraint if idx > max(ii) then i = min(ii) else i = idx endif;
  } in chuffed_maximum_arg_bool(x ++ [true], min(ii), idx);
