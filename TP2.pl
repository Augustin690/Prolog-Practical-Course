/*---------------------------------------------------------------*/
/* Telecom Paris- J-L. Dessalles 2023                            */
/* LOGIC AND KNOWLEDGE REPRESENTATION                            */
/*            http://teaching.dessalles.fr/LKR                   */
/*---------------------------------------------------------------*/


% adapted from I. Bratko - "Prolog - Programming for Artificial Intelligence"
%              Addison Wesley 1990

% An ape is expected to form a plan to grasp a hanging banana using a box.
% Possible actions are 'walk', 'climb (on the box)', 'push (the box)',
% 'grasp (the banana)'

% description of actions - The current state is stored using a functor 'state'
% with 4 arguments:
%	- horizontal position of the ape
%	- vertical position of the ape
%	- position of the box
%	- status of the banana
% 'action' has three arguments:
%	- Initial state
%	- Final state
%	- act

action(state(middle,on_box,X,not_holding), grasp, state(middle,on_box,X,holding)).
action(state(X,floor,X,Y), climb, state(X,on_box,X,Y)).
action(state(X,floor,X,Z), push(X,Y), state(Y,floor,Y,Z)).
action(state(X,floor,T,Z), walk(X,Y), state(Y,floor,T,Z)).

extract(X, [X|L], L).
extract(X, [Y|L], [Y|L1]) :-
    extract(X, L, L1).


% Definition of the success conditions in the problem of the monkey
success(state(_, _, _, holding), []).
success(State1, [Act|Plan]) :-
    action(State1, Act, State2),
   % write('Action : '), write(A), nl, write(' --> '), write(State2), nl,
    success(State2,Plan).


ape :-
	success(state(door, floor, window, not_holding), Plan),
        write(Plan).

% better solution with accumulator:
mirror2(Left, Right) :-
    invert(Left, [ ], Right).
invert([X|L1], L2, L3) :-    % the list is 'poured'
    invert(L1, [X|L2], L3).    % into the second argument
invert([ ], L, L).        % at the deepest level, the result L is merely copied



palindrome(L,L).
palindrome(List):-
   mirror2(List,Reverse),
   palindrome(List,Reverse).



%-------------------
% palindrome
%-------------------

palindrome_1(L) :-
    mirror(L, L).


% palindrome with accumulator (more efficient as it explores only half of the list)
palindrome_2(L) :-
    palindrome_accu(L,[]).

palindrome_accu(L,L) :- !.    % stops when half of the list is reversed
palindrome_accu(L,[_|L]) :- !.    % idem, odd case
palindrome_accu([T | Q],L) :-
    palindrome_accu(Q, [T|L]).    % reverses the list

% You may test: palindrome([X,Y,Z]).

:- dynamic(sunshine/0). % necessary with SWI-Prolog.
:- dynamic(raining/0). % necessary with SWI-Prolog.
:- dynamic(fog/0). % necessary with SWI-Prolog.

nice :-
    sunshine, not(raining).

funny :-
    sunshine, raining.
disgusting :-
    raining,fog.
raining.
fog.

myprint :-
    retract(item(X)), % reussit tant qu'il y a des items
    write(X),nl,
    fail.
myprint.

myprint1 :-
    retract(item(X)),
    !, % avoids unwanted behahaviour if some predicate fails after a call to myprint1
    myprint1,
    write(X),nl,
    asserta(item(X)). % asserta = version of assert that adds item on top of the memory stack
myprint1.

%empty(pred(_)) :-
%    pred(X),
%    retract(item(X)).


empty(P) :-
    retract(P),
    write(P), write(' has been forgotten'), nl,
    fail.    % this will force backtracking
empty(_).    % terminate with success


findany(Var,Pred,_) :-
    Pred,
    asserta(found(Var)),
    fail.

findany(_,_,L):-
    collect_found(L).

collect_found([X|L]):-
    retract(found(X)),
    !,
    collect_found(L).

collect_found([]).


% Atlernative solution
findany1(Var, Pred, _) :-
    assert(found([ ])),
    Pred,     % the execution of Pred instantiates Var
    retract(found(R)),     % always only one instance of �found�
                % in memory, no alternative to backtrack onto
    assert(found([Var | R])),
    fail.
findany1(_, _,L) :-
    retract(found(L)).


%--------------------------------
%       semantic networks
%--------------------------------

isa(bird, animal).
isa(albert, albatross).
isa(albatross, bird).
isa(kiwi, bird).
isa(willy, kiwi).
isa(crow, bird).
isa(ostrich, bird).

:- dynamic(locomotion/2).	% for tests

locomotion(bird, fly).
locomotion(kiwi, walk).
locomotion(X, Loc) :-
	isa(X, SuperX),
	locomotion(SuperX, Loc).

food(albatross,fish).
food(bird,grain).

/*habitat(X, continent) :-
    known(locomotion(X, M)),
    M \== fly,
    !.*/

habitat(Animal, continent):-
    known(locomotion(Animal,M)),
    M \== fly,
    !.

habitat(_, unknown).

/* drawback : n particular inheritance rules */
/* solution: one general predicate : "known" */

known(Fact) :-
	Fact,
	!.
known(Fact) :-
	Fact =.. [Rel, Arg1, Arg2],
	isa(Arg1, SuperArg1),
	SuperFact =.. [Rel, SuperArg1, Arg2],
	known(SuperFact).
