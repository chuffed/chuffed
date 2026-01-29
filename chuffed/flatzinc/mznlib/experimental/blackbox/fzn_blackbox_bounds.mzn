predicate fzn_blackbox_bounds(
	array[int] of var int: int_input,
	array[int] of var float: float_input,
	array[int] of int: flat_reason,
) = assert(
	length(float_input) == 0,
	"Chuffed does not support floating-point black-box propagators.",
	chuffed_blackbox_bounds(int_input, flat_reason)
);

predicate chuffed_blackbox_bounds(
	array[int] of var int: int_input,
	array[int] of int: flat_reason,
);
