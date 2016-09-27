include "globals.mzn";
include "flatzinc.mzn";

int: c; % number of customers
int: p; % number of products

set of int: Custs = 1..c;
set of int: Prods = 1..p;

array[Custs,Prods] of 0..1: orders; % which customer orders which product

array[1..c*c] of bool: graph = [
    sum (j in Prods) (bool2int(orders[(i div c)+1, j] = 1 /\ orders[(i mod c)+1, j] = 1)) >= 1
        | i in 0..c*c-1];

    % graph describing which pairs of customers share at least one product

array[Custs] of var Custs: s;                  % customer start time
array[Custs] of var Custs: e :: is_output;     % customer end time
var Custs: stacks :: is_output;                % number of stacks required

constraint all_different(e);

constraint forall (i, j in Custs where graph[(i-1)*c+j]) (s[i] <= e[j]);

constraint forall (t in Custs) (stacks >= sum (i in Custs) (
    bool2int(s[i] <= t /\ t <= e[i])));

% Dominance breaking constraints

array[Custs,Custs] of var bool: r;             % whether customer was ready to close at certain time

% if all customers sharing a product has already opened and we have not closed, we are ready to close now
constraint forall (i, t in Custs) (
    r[i,t] = forall ([s[j] <= t | j in Custs where graph[(i-1)*c+j]] ++ [e[i] >= t]));

% If none of the lex better customers are ready to close now but we are, we close now
constraint forall (i in Custs, t in 1..c-1) (
    bool_clause([r[j,t] | j in 1..i-1], [r[i,t], e[i] >= t+1]));

solve :: int_search(e, smallest, indomain_min, complete) minimize stacks;
