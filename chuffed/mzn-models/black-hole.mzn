include "globals.mzn";
include "flatzinc.mzn";

set of int: Piles = 1..17;
set of int: Layers = 1..3;
set of int: Cards = 1..52;

array[Piles, Layers] of int: layout;    % layout of cards by pile and layer
array[Cards] of int: ctop;              % get pile by card index
array[Cards] of int: ctol;              % get layer by card index

ctop = [-1] ++ [i | c in Cards, i in Piles, j in Layers where layout[i,j] = c];
ctol = [-1] ++ [j | c in Cards, i in Piles, j in Layers where layout[i,j] = c];

array[1..416, 1..2] of int: neighbours; % next card is +/- 1 of current card

neighbours = array2d(1..416, 1..2,
    [i+1 | n in 0..831, i in 0..51 where
        (n mod 2 = 0 /\ i = n div 16) \/
        (n mod 4 = 1 /\ i = (n div 16 + (n mod 16) div 4 * 13 + 51) mod 52) \/
        (n mod 4 = 3 /\ i = (n div 16 + (n mod 16) div 4 * 13 + 1) mod 52)]);

array[Cards] of var Cards: x;                 % Position of card
array[Cards] of var Cards: y :: is_output;    % Card at position

% Problem constraints

constraint y[1] == 1;     % Ace of spades in first pos

constraint inverse(x,y);

constraint
	forall(i in 1..17, j in 1..2) (x[layout[i,j]] < x[layout[i,j+1]]);

constraint forall(i in 1..51) (table([y[i], y[i+1]], neighbours));

% Symmetry breaking constraints

constraint forall (i in 1..13, s1 in 0..3, s2 in s1+1..3) (
    let { int: n1 = s1*13+i, int: n2 = s2*13+i } in 
    if (n1 != 1 /\ ctop[n1] != ctop[n2]) then
    let { int: o1 = if ctol[n2] < ctol[n1] then n2 else n1 endif,
          int: o2 = if ctol[n2] < ctol[n1] then n1 else n2 endif } in
    if ctol[o2] == 3 then
        if ctol[o1] == 1 then
            x[o1] < x[o2]
        else
            bool_clause([x[o2] < x[layout[ctop[o1],ctol[o1]-1]],
                x[o1] < x[o2]], [])
        endif
    else
        if ctol[o1] == 1 then
            bool_clause([x[layout[ctop[o2],ctol[o2]+1]] < x[o1],
                x[o1] < x[o2]], [])
        else
            bool_clause([x[layout[ctop[o2],ctol[o2]+1]] < x[o1],
                x[o2] < x[layout[ctop[o1],ctol[o1]-1]],
                x[o1] < x[o2]], [])
        endif
    endif
    else true endif
);

% Branching heuristic

array [1..51] of var int: pref_order =
    [x[i] | i in Cards where ctol[i] = 1] ++
    [x[i] | i in Cards where ctol[i] = 2] ++
    [x[i] | i in Cards where ctol[i] = 3];

solve :: int_search(pref_order, smallest, indomain_min, complete) satisfy;
