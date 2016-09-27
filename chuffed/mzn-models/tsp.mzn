include "globals.mzn";
include "flatzinc.mzn";

int: n; % number of cities

set of int: Cities = 1..n;

array [Cities,Cities] of int: d; % distance between cities

array [Cities] of var Cities: succ;
var int: total;

constraint circuit(succ);

constraint total >= sum (i in Cities) (d[i,succ[i]]);

solve minimize total;
