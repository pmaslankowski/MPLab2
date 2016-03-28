:- op(200, fx, ~).
:- op(500, xfy, v).

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

rem([], Acc, Acc).
rem([H|T], Acc, Res) :-
	member(H, Acc), !,
	rem(T, Acc, Res).
rem([H|T], Acc, Res) :-
	rem(T, [H|Acc], Res).
rem(L, Res) :-
	rem(L, [], Res).

resolvent1(Clause1, Clause2, Res) :-
	select(Var, Clause1, Clause1R),
	neg(Var, NegVar),
	select(NegVar, Clause2, Clause2R),
	append(Clause1R, Clause2R, Tmp),
	rem(Tmp, Res).

resolvent(Clauses,(TmpRes, (Index1, Index2))) :-
	nth1(Index1, Clauses, (Clause1,_,_)),
	nth1(Index2, Clauses, (Clause2,_,_)),
	Index1 < Index2,
	resolvent1(Clause1, Clause2, TmpRes).

proof1(Clauses, [([],(Index1,Index2))|[]]) :-
	resolvent(Clauses, ([], (Index1,Index2))), !.
proof1(Clauses, [(X,I1,I2)|ProofTmp]) :-
	resolvent(Clauses, (X,I1,I2)),
	\+member((X,_,_), Clauses),
	append(Clauses, [(X,I1,I2)], NewClauses),
	proof1(NewClauses, ProofTmp).

normalise(([],0,0), ([],axiom)).
normalise(([],I1,I2), ([],I1,I2)).
normalise((Clause,0,0), (Res, axiom)) :-
	!,normaliseClause(Res, Clause).
normalise((Clause, I1, I2), (Res, I1, I2)) :-
	normaliseClause(Res, Clause).

normaliseProof([],[]).
normaliseProof([H|T], [Normalised1|NormalisedOthers]) :-
	normalise(H, Normalised1),
	normaliseProof(T, NormalisedOthers).

normaliseInput([],[]).
normaliseInput([H|T], [(HR,0,0)|TR]) :-
	normaliseClause(H, HR),
	normaliseInput(T, TR).

prove(Clauses, Res) :-
	normaliseInput(Clauses, NormalisedClauses),
	proof1(NormalisedClauses, Proof),
	append(NormalisedClauses, Proof, Tmp),
	normaliseProof(Tmp, Res).

	

	 

	


	
