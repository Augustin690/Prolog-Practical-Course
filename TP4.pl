/*---------------------------------------------------------------*/
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


%Predicate cnf puts more elementary processing together
cnf(Conjunction, Newconjunction) :-
    oneStep(Conjunction, C1),
    cnf(C1, Newconjunction).
cnf(C, C).

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

/* TEST */
go :-
    prove( ((a imp (b imp c)) imp ((a imp b) imp (a imp c))) ).
