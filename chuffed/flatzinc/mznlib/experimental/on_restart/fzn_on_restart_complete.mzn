/* Abandon and mark search as complete when argument variable is assigned `true'. */
predicate fzn_on_restart_complete(var bool: marker) = chuffed_on_restart_complete(marker);
predicate chuffed_on_restart_complete(var bool: marker);
