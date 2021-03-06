:- op(200, fx, ~).
:- op(500, xfy, v).

normClause([], ([], [])).
normClause(~X, ([], [X])) :- !.
normClause(X, ([X],[])) :-
	atom(X),!.
normClause(~H v T, (Pos, [H|Neg])) :-
	!,normClause(T, (Pos, Neg)).
normClause(H v T, ([H|Pos],Neg)) :-
	atom(H),
	normClause(T, (Pos, Neg)).
normClause_(C, (Pos, Neg)) :-
	normClause(C, (PosTmp, NegTmp)),
	list_to_ord_set(PosTmp, Pos),
	list_to_ord_set(NegTmp, Neg).


%Stary kod:
isNotSuperset([], Clause).
isNotSuperset([H|T], Clause) :-
	\+ord_subset(H, Clause),
	isNotSuperset(T, Clause).

rem_super_sets([], []).
rem_super_sets([L|Ls], R) :-
    (   select(T, Ls, L1), % get any T in Ls
        ord_subset(L, T)   % is T a superset of L ?
    ->  rem_super_sets([L|L1], R) % discard T, keep L for further tests
    ;   R = [L|L2],
        rem_super_sets(Ls, L2)
    ).

start([], []).
start([H|T], [HR|Res]) :-
	normClause_(H, HR),
	start(T, Res).

init([], MapAcc, _, MapAcc, []).
init([H|T], MapAcc, CurrentNumber, Map, [(NH,axiom)|Proof]) :-
	normClause(NH, H),
	put_assoc(H, MapAcc, CurrentNumber, NewMapAcc),
	NewNumber is CurrentNumber + 1,
	init(T, NewMapAcc, NewNumber, Map, Proof).
init(Clauses, NormalisedClauses, Map, Proof) :-
	empty_assoc(MapAcc),
	start(Clauses, TmpClauses),
	list_to_ord_set(TmpClauses, NormalisedClauses),
	init(NormalisedClauses, MapAcc, 1, Map, Proof).


resolve((P1,N1),(P2,N2),(PR,NR)) :-
	select(V, P1, P1R),
	select(V, N2, N2R),
	ord_union([P1R, P2], PR),
	ord_union([N1, N2R], NR),
	ord_disjoint(NR, PR).
resolve((P2,N2),(P1,N1),(PR,NR)) :-
	select(V, P1, P1R),
	select(V, N2, N2R),
	ord_union([P1R, P2], PR),
	ord_union([N1, N2R], NR),
	ord_disjoint(NR, PR).
resolve(Clauses, Map, I1, I2, R) :-
	member(C1, Clauses),
	member(C2, Clauses),
	get_assoc(C1, Map, I1),
	get_assoc(C2, Map, I2),
	I1 < I2,
	resolve(C1, C2, R),
	\+member(R, Clauses),
	isNotSuperset(Clauses, R), !.

prove(Clauses, _, Map, ProofAcc, Proof) :- 
	resolve(Clauses, Map, I1, I2, ([],[])), !,
	append(ProofAcc, [([], I1, I2)], Proof).
prove(Clauses, CurrentNumber, Map, ProofAcc, Proof) :-
	resolve(Clauses, Map, I1, I2, R),
	ord_add_element(Clauses, R, TmpClauses),
	rem_super_sets(TmpClauses, NewClauses),
	put_assoc(R, Map, CurrentNumber, NewMap),
	NewNumber is CurrentNumber+1,
	normClause(Normalised, R),
	append(ProofAcc, [(Normalised, I1, I2)], NewProofAcc),
	prove(NewClauses, NewNumber, NewMap, NewProofAcc, Proof).
prove(Clauses, Proof) :-
	init(Clauses, NormalisedClauses, Map, StartProof),
	length(Clauses, CurrNumber),
	StartNumber is CurrNumber+1,
	prove(NormalisedClauses, StartNumber, Map, StartProof, Proof), !.

