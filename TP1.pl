parent(marge, lisa).
parent(marge, bart).
parent(marge, maggie).
parent(homer, lisa).
parent(homer, bart).
parent(homer, maggie).
parent(abraham, homer).
parent(abraham, herb).
parent(mona, homer).
parent(jackie, marge).
parent(clancy, marge).
parent(jackie, patty).
parent(clancy, patty).
parent(jackie, selma).
parent(clancy, selma).
parent(selma, ling).

female(mona).
female(jackie).
female(marge).
female(ann).
female(patty).
female(selma).
female(ling).
female(lisa).
female(maggie).
male(abraham).
male(herb).
male(homer).
male(bart).
male(clancy).



child(X,Y) :-
    parent(Y,X).

mother(X,Y) :-
    parent(X,Y),
    female(X).

grandparent(X,Y) :-
    parent(X,Z), % note that the a variable's scope is the clause
    parent(Z,Y). % variable Z keeps its value within the clause

sister(X,Y) :-
    parent(Z,X), % if X gets instantiated, Z gets instantiated as well
    parent(Z,Y),
    female(X),
    X \== Y. % can also be noted: not(X = Y).


ancestor(X,Y) :-
    parent(X,Y).
ancestor(X,Y) :-
    parent(X,Z),
    ancestor(Z,Y).

         % recursive call

descendant(X,Y) :- ancestor(Y,X).

aunt(X,Y) :-

    sister(X,Z),
    parent(Z,Y).

extract(X, [X|L], L).
extract(X, [Y|L], [Y|L1]) :-
    extract(X, L, L1).

permute([],[]).
permute([First|Rest],PermutedList) :-
    permute(Rest,List),
    extract(First, PermutedList,List).

last_elt([_|L], E) :-
    last_elt(L, E).
last_elt([E], E).

%attach(L1,L2,L3) :-

attach([], List, List).
attach([Head|Tail], List, [Head|Rest]) :-
    attach(Tail, List, Rest).


a(X,Y) :-
    b(X),
    c(X,Y).
b(1).
b(&).
c(&,"A").


membership(Member, [_|O]) :-
    membership(Member,O).

membership(Member, [Member|_]).

assemble(L1,L2,L3, Result):-
    attach(L1,L2,L),
    attach(L,L3,Result).

sub_list_1(IncludedList, IncludingList) :-
        attach(L,_,IncludingList),
        attach(_,IncludedList,L).


sub_list(L1, L2) :-
    attach(_, L, L2),
    attach(L1, _, L).

remove_1(X,List,L):-
    extract(X,List,L),
    remove_1(X,L,L),
    !.

remove(X, [X|L], L1) :-
    !,
    remove(X, L, L1).
remove(X, [Y|L], [Y|L1]) :-
    remove(X, L, L1).
remove(_, [ ], [ ]).



duplicate([X|L], [X,X|M]) :-
    duplicate(L, M).
duplicate([], []).




















