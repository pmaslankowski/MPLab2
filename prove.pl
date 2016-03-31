:- op(200, fx, ~).
:- op(500, xfy, v).

normClause_(~X v T, [~X | Res]) :-
	normClause_(T, Res).
normClause_(X v T, [X | Res]) :-
	normClause_(T, Res).
normClause_(X, [X]).
normClause(Clause, NormalisedClause) :-
	normClause_(Clause, Tmp),
	list_to_ord_set(Tmp, NormalisedClause).

not(~X, X) :- !.
not(X, ~X).

isNotTrue([], _).
isNotTrue([H|Clause],Acc) :-
	not(H, NH),	
	\+member(NH, Acc),
	isNotTrue(Clause, [H|Acc]).	
isNotTrue(Clause) :-
	isNotTrue(Clause, []).

order(<, L1, L2) :-
	length(L1, X),
	length(L2, Y),
	X < Y.
order(>, L1, L2) :-
	length(L1, X),
	length(L2, Y),
	X >= Y.

resolve(C1, C2, R) :-
	select(V, C1, C1V),
	not(V, NV),
	select(NV, C2, C2NV),
	ord_union([C1V, C2NV], R).
resolve(Clauses, R) :-
	member(C1, Clauses),
	member(C2, Clauses),
	C1 \= C2,
	resolve(C1, C2, R),
	\+member(R, Clauses),
	isNotTrue(R), !.

prove(Clauses) :- 
	resolve(Clauses, []), !.
prove(Clauses) :-
	print(Clauses), nl,
	resolve(Clauses, R),
	predsort(order, [R|Clauses], NewClauses),
	prove(NewClauses).
