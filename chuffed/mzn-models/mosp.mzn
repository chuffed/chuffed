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

array[Custs,Custs] of var bool: so;            % whether customer started before certain time
array[Custs,Custs] of var bool: eo;            % whether customer ended after certain time
array[Custs,Custs] of var bool: o;             % whether customer was open at certain time

constraint all_different(e);

%constraint forall (i in Custs) (minimum(s[i], [e[j] | j in Custs where graph[(i-1)*c+j]]));

constraint forall (i, j in Custs where graph[(i-1)*c+j]) (s[i] <= e[j]);

constraint forall (i, t in Custs) (so[i,t] = (s[i] <= t));
constraint forall (i, t in Custs) (eo[i,t] = (e[i] >= t));
constraint forall (i, t in Custs) (o[i,t] = (so[i,t] /\ eo[i,t]));


constraint forall (t in Custs) (stacks >= sum (i in Custs) (bool2int(o[i,t])));

% Dominance breaking constraints

array[Custs,Custs] of var bool: r;             % whether customer was ready to close at certain time

% if all customers sharing a product has already opened and we have not closed, we are ready to close now
constraint forall (i, t in Custs) (
	r[i,t] = forall ([so[j,t] | j in Custs where graph[(i-1)*c+j]] ++ [eo[i,t]]));

% If none of the lex better customers are ready to close now but we are, we close now
constraint forall (i in Custs, t in 1..c-1) (
    bool_clause([r[j,t] | j in 1..i-1], [r[i,t], eo[i,t+1]]));
%	exists([r[j,t] | j in 1..i-1] ++ [r[i,t] != true, eo[i,t+1] != true]));


solve :: int_search(e, smallest, indomain_min, complete) minimize stacks;
