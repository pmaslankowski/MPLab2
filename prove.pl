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

init([], MapAcc, _, [], MapAcc, []).
init([H|T], MapAcc, CurrentNumber, [HR|TR], Map, [(H,axiom)|Proof]) :-
	normClause(H, HR), !,
	put_assoc(HR, MapAcc, CurrentNumber, NewMapAcc),
	NewNumber is CurrentNumber + 1,
	init(T, NewMapAcc, NewNumber, TR, Map, Proof).
init(Clauses, NormalisedClauses, Map, Proof) :-
	empty_assoc(MapAcc),
	init(Clauses, MapAcc, 1, NormalisedClauses, Map, Proof).

resolve(C1, C2, R) :-
	select(V, C1, C1V),
	not(V, NV),
	select(NV, C2, C2NV),
	ord_union([C1V, C2NV], R).
resolve(Clauses, Map, I1, I2, R) :-
	member(C1, Clauses),
	member(C2, Clauses),
	C1 \= C2,
	resolve(C1, C2, R),
	\+member(R, Clauses),
	isNotTrue(R), !, 
	get_assoc(C1, Map, I1),
	get_assoc(C2, Map, I2).

prove(Clauses, _, Map, ProofAcc, Proof) :- 
	resolve(Clauses, Map, I1, I2, []), !,
	append(ProofAcc, [([], I1, I2)], Proof).
prove(Clauses, CurrentNumber, Map, ProofAcc, Proof) :-
	resolve(Clauses, Map, I1, I2, R),
	predsort(order, [R|Clauses], NewClauses),
	put_assoc(R, Map, CurrentNumber, NewMap),
	NewNumber is CurrentNumber+1,
	normClause_(Normalised, R),
	append(ProofAcc, [(Normalised, I1, I2)], NewProofAcc),
	prove(NewClauses, NewNumber, NewMap, NewProofAcc, Proof).
prove(Clauses, Proof) :-
	init(Clauses, NormalisedClauses, Map, StartProof),
	length(Clauses, CurrNumber),
	StartNumber is CurrNumber+1,
	prove(NormalisedClauses, StartNumber, Map, StartProof, Proof).
