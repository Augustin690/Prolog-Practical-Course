/*---------------------------------------------------------------*/
/* Telecom Paris- J-L. Dessalles 2023                            */
/* LOGIC AND KNOWLEDGE REPRESENTATION                            */
/*            http://teaching.dessalles.fr/LKR                   */
/*---------------------------------------------------------------*/



:-op(140, fy, -).
:-op(160,xfy, [and, or, equiv, imp, impinv, nand, nor, nonimp, equiv, nonimpinv]).

is_true(V, X and Y) :- is_true(V,X), is_true(V,Y).
is_true(V, X or _) :- is_true(V,X).
is_true(V, _ or Y) :- is_true(V,Y).
is_true(V, -X) :-
	not(is_true(V, X)). % link with Prolog's negation
is_true(v0,a).	% this means that v0 sends a to True and everything else (here, b and c) to false

is_true(V, X imp Y) :-
    is_true(V, -X or Y).
is_true(V, X equiv Y) :-
    is_true(V, (X and Y) or (-X and -Y)).


is_true(V, X) :-
	member(X,V).	% only true elements are explicitly mentioned in V

valuation(V) :-
	% we keep all elements that V sends to true.
	% all other elements are supposed to be false.
	sub_set(V, [a,b,c]).

sub_set([], []).
sub_set([X|XL], [X|YL]) :-
    sub_set(XL, YL).
sub_set(XL, [_|YL]) :-
    sub_set(XL, YL).



*---------------------------------------------------------------*/
/* Telecom Paris- J-L. Dessalles 2023                            */
/* LOGIC AND KNOWLEDGE REPRESENTATION                            */
/*            http://teaching.dessalles.fr/LKR                   */
/*---------------------------------------------------------------*/



:-op(140, fy, -).
:-op(160,xfy, [and, or, imp, impinv, nand, nor, nonimp, equiv, nonimpinv]).

    %%%%%%%%%%%%%%%%%%%%%%%%%%%
    % Conjunctive normal form %
    %%%%%%%%%%%%%%%%%%%%%%%%%%%


/* table for unary, alpha and beta formulas */

components(- -X, X, _, unary).
components(X and Y, X, Y, alpha).
components(-(X or Y), -X, -Y, alpha).
components(X or Y, X, Y, beta).
components(-(X and Y), -X, -Y, beta).
components(X imp Y, -X, Y, beta).
components(-(X imp Y), X, -Y, alpha).
components(X impinv Y, X, -Y, beta).
components(-(X impinv Y), -X, Y, alpha).
components(X nand Y, -X, -Y, beta).
components(-(X nand Y), X, Y, alpha).
components(X nor Y, -X, -Y, alpha).
components(-(X nor Y), X, Y, beta).
components(X nonimp Y, X, -Y, alpha).
components(-(X nonimp Y), -X, Y, beta).
components(X nonimpinv Y, -X, Y, alpha).
components(-(X nonimpinv Y), X, -Y, beta).


% Predicate cnf puts more elementary processing together
cnf(Conjunction, NewConjunction) :-
	oneStep(Conjunction, C1),
	cnf(C1, NewConjunction).
cnf(C, C).


% Predicate oneStep performs one elementary processing
oneStep([Clause | Rest_Conjonction], [ [F1, F2 | Rest_Clause] | Rest_Conjonction]) :-
	% looking for a beta formula in the clause
	remove(F1 or F2, Clause, Rest_Clause).
oneStep([ F | Rest], [ F | New_Rest ]) :-
	% nothing left to do on F
	oneStep(Rest, New_Rest).



/*------------------------------------------------*/
/* Auxiliary predicates                           */
/*------------------------------------------------*/

/* remove does as select, but removes all occurrences of X */
remove(X, L, NL) :-
    member(X,L),	% so that remove fails if X absent from L
    remove1(X, L, NL).
remove1(X, L, L) :-
    not(member(X,L)).
remove1(X, L, NL) :-
	select(X, L, L1),   % available in SWI-Prolog
	remove1(X, L1, NL).


prove(F) :-
    cnf([[ -F ]], CNF),
    write('CNF of -'), write(F), write(' = '),
    write(CNF), nl,
    resolve(CNF).

resolve(CNF) :-
    member([ ], CNF),
    write('This is a true formula'), nl.
resolve(CNF) :-
    write('Examining '), write(CNF), nl,
    get0(_),    % waits for user action
    select(C1, CNF, _),            % forgetting this parent clause
    select(C2, CNF, RCNF),    % keeping this parent clause
    remove(P, C1, RC1),
    remove(-P, C2, RC2),
    append(RC1, RC2, RC),
    resolve([RC|RCNF]).






