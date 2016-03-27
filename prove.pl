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

del(H, [H|T], T) :- !.
del(X, [H|T], [H|Res]) :-
	del(X, T, Res).

eliminateRepetitions([], Acc, Acc).
eliminateRepetitions([H|T], Acc, Res) :-
	member(H, Acc), !,
	eliminateRepetitions(T, Acc, Res).
eliminateRepetitions([H|T], Acc, Res) :-
	eliminateRepetitions(T, [H|Acc], Res).
eliminateRepetitions(L, Res) :-
	eliminateRepetitions(L, [], Res).

findResolvents([], _, _, Acc, Acc, Index1, Index2).
findResolvents([H|T], Clause2, CurrAcc, Acc, Res, Index1, Index2) :-
	neg(H, NegH),	
	member(NegH, Clause2), !,
	del(NegH, Clause2, Tmp),
	appn([CurrAcc, T, Tmp], Tmp2),
	eliminateRepetitions(Tmp2, Tmp3),
	findResolvents(T, Clause2, [H | CurrAcc], [(Tmp3, (Index1, Index2)) | Acc], Res, Index1, Index2).
findResolvents([H|T], Clause2, CurrAcc, Acc, Res, Index1, Index2) :-
	findResolvents(T, Clause2, [H|CurrAcc], Acc, Res, Index1, Index2).	
findResolvents(Clause1, Clause2, Res, Index1, Index2) :-
	findResolvents(Clause1, Clause2, [], [], Res, Index1, Index2).

findResolventsOfList([], _, _, _, Acc, Acc).
findResolventsOfList([H|Clauses], Index2, Clause1, Index1, Acc, Res) :-
	findResolvents(Clause1, H, Tmp, Index1, Index2),
	NewIndex2 is Index2 + 1,
	appn(Tmp, Tmp2),
	appn([Tmp2, Acc], NewAcc),
	findResolventsOfList(Clauses, NewIndex2, Clause1, Index1, NewAcc, Res). 

	


	
