predicate chuffed_array_int_maximum(var int: m, array[int] of var int: x);
predicate array_int_maximum(var int: m, array[int] of var int: x)
= chuffed_array_int_maximum(m, x);

predicate array_float_maximum(var float: m, array[int] of var float: x)
= abort("float variables are not supported by chuffed");

predicate chuffed_array_int_minimum(var int: m, array[int] of var int: x);
predicate array_int_minimum(var int: m, array[int] of var int: x)
= chuffed_array_int_minimum(m, x);

predicate array_float_minimum(var float: m, array[int] of var float: x)
= abort("float variables are not supported by chuffed");
