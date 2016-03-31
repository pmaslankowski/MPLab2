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

equal([],[]).
equal([H|T], L2) :-
	select(H, L2, Tmp),
	equal(T, Tmp).

mem([(H,_,_)|_], El) :-
	equal(H, El),!.
mem([_|T], El) :-
	mem(T, El).

subset1([], _).
subset1([H|T], L) :-
	member(H, L),
	subset1(T, L).

subset([H|T], Clause) :-
	subset1(Clause, H),!.
subset([_|T], Clause) :-
	subset(T, Clause).

eliminate([], [], _) :- !,fail.
eliminate([], Acc, Acc).
eliminate([H|T], Acc, Res) :-
	neg(H, NegH),
	select(NegH, Acc, NewAcc), !,
	eliminate(T, NewAcc, Res).
eliminate([H|T], Acc, Res) :-
	eliminate(T, [H|Acc], Res).

eliminate([], []).
eliminate(Clause, Res) :-
	eliminate(Clause, [], Res).

resolvent1(Clause1, Clause2, Res) :-
	select(Var, Clause1, Clause1R),
	neg(Var, NegVar),
	select(NegVar, Clause2, Clause2R),
	append(Clause1R, Clause2R, Tmp),
	list_to_set(Tmp, Tmp2),
	eliminate(Tmp2, Res).

resolvent(Clauses,(TmpRes, (Index1, Index2))) :-
	nth1(Index1, Clauses, (Clause1,_,_)),
	nth1(Index2, Clauses, (Clause2,_,_)),
	Index1 < Index2,
	resolvent1(Clause1, Clause2, TmpRes).

proof(Clauses, [([],(Index1,Index2))|[]]) :-
	resolvent(Clauses, ([], (Index1,Index2))), !.
proof(Clauses, [(X,I1,I2)|ProofTmp]) :-
	resolvent(Clauses, (X,I1,I2)),
	\+mem(Clauses,X),
	\+subset(Clauses, X),
	append(Clauses, [(X,I1,I2)], NewClauses),
	proof(NewClauses, ProofTmp).

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
	proof(NormalisedClauses, Proof),
	append(NormalisedClauses, Proof, Tmp),
	normaliseProof(Tmp, Res).
