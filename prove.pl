:- op(200, fx, ~).
:- op(500, xfy, v).

appn([], Acc, [], Acc).
appn([H|T], Acc, End, Res) :-
	append(H, Hole, End),
	appn(T, Acc, Hole, Res). 
appn(L, Res) :-
	appn(L, Hole, Hole, Res).

normaliseClause(~X, [~X]) :-
	atom(X), !.
normaliseClause(X, [X]) :-
	atom(X).
normaliseClause(~X v Y, [~X|T]) :-
	!, normaliseClause(Y, T).
normaliseClause(X v Y, [X|T]) :-
	normaliseClause(Y, T).

neg(~X, X).
neg(X, ~X).

eliminateRepetitions([], Acc, Acc).
eliminateRepetitions([H|T], Acc, Res) :-
	member(H, Acc), !,
	eliminateRepetitions(T, Acc, Res).
eliminateRepetitions([H|T], Acc, Res) :-
	eliminateRepetitions(T, [H|Acc], Res).
eliminateRepetitions(L, Res) :-
	eliminateRepetitions(L, [], Res).

findResolvents([], _, _, Acc, Acc).
findResolvents([H|T], Clause2, CurrAcc, Acc, Res) :-
	neg(H, NegH),	
	member(NegH, Clause2), !,
	select(NegH, Clause2, Tmp),
	appn([CurrAcc, T, Tmp], Tmp2),
	eliminateRepetitions(Tmp2, Tmp3),
	findResolvents(T, Clause2, [H | CurrAcc], [Tmp3|Acc], Res).
findResolvents([H|T], Clause2, CurrAcc, Acc, Res) :-
	findResolvents(T, Clause2, [H|CurrAcc], Acc, Res).	
findResolvents(Clause1, Clause2, Res) :-
	findResolvnets(Clause1, Clause2, [], [], Res).
	
	


	
