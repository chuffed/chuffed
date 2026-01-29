predicate fzn_blackbox(
	array[int] of var int: int_input,
	array[int] of var float: float_input,
	array[int] of var int: int_output,
	array[int] of var float: float_output
) = assert(
	length(float_input) == 0 /\ length(float_output) == 0,
	"Chuffed does not support floating-point black-box propagators.",
	chuffed_blackbox(int_input, int_output)
);

predicate chuffed_blackbox(
	array[int] of var int: int_input,
	array[int] of var int: int_output,
);
