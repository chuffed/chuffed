include "val_sym.mzn";

int: n;    % number of offers
int: k;    % number of halls

set of int: Offers = 1..n;
array [Offers] of int: start;
array [Offers] of int: end;
array [Offers] of int: price;
array [Offers,Offers] of bool: o;

array [Offers] of var 1..k+1: x :: is_output;    % hall to take, 0 means reject offer
var 0..1000: total :: is_output;                % total money we can make

o = array2d(Offers, Offers,
    [start[i] <= end[j] /\ start[j] <= end[i] | i in Offers, j in Offers]);

constraint forall (i, j in Offers where i < j /\ o[i,j]) (x[i] = k+1 \/ x[j] = k+1 \/ x[i] != x[j]);

constraint sum (i in Offers) (bool2int(x[i] <= k) * price[i]) >= total;

constraint val_sym(x, 1, k);

%solve :: int_search(x, input_order, indomain_min, complete) :: int_search([total], input_order, indomain_max, complete) maximize total;
solve :: int_search([total], input_order, indomain_max, complete) :: int_search(x, input_order, indomain_min, complete) maximize total;
