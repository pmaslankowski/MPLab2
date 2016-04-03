/* Funktory do budowania klauzul */

:- op(200, fx, ~).
:- op(500, xfy, v).

/* Główny program: main/1. Argumentem jest atom będący nazwą pliku
 * z zadaniem. Przykład uruchomienia:
 *    ?- main('zad125.txt').
 * Plik z zadaniem powinien być plikiem tekstowym, na którego
 * początku znajduje się lista klauzul zbudowanych za pomocą funktorów
 * v/2 i ~/1 (szczegóły znajdują się w opisie zadania). Listę zapisujemy
 * w notacji prologowej, tj. rozdzielając elementy przecinkami
 * i otaczając listę nawiasami [ i ]. Za nawiasem ] należy postawić
 * kropkę. Wszelkie inne znaki umieszczone w pliku są pomijane przez
 * program (można tam umieścić np. komentarz do zadania).
 */

main(FileName) :-
   readClauses(FileName, Clauses),
   prove(Clauses, Proof),
   writeProof(Proof).

/* Silnik programu: predykat prove/2 — do napisania w ramach zadania.
 * Predykat umieszczony poniżej nie rozwiązuje zadania. Najpierw
 * wypisuje klauzule wczytane z pliku, a po nawrocie przykładowy dowód
 * jednego z zadań. Dziewięć wierszy następujących po tym komentarzu
 * należy zastąpić własnym rozwiązaniem. */

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

addOrigin(Clause, (Clause, axiom)).

/* Pozostała część pliku zawiera definicje predykatów wczytujących listę
 * klauzul i wypisujących rozwiązanie. Wykorzystane predykaty
 * biblioteczne SWI-Prologu (wersja kompilatora: 6.6.6):
 *
 *    close/1
 *    format/2
 *    length/2
 *    maplist/3
 *    max_list/2
 *    nl/0
 *    open/3
 *    read/2
 *    write_length/3
 *
 * Dokumentację tych predykatów można uzyskać wpisując powyższe napisy
 * na końcu następującego URL-a w przeglądarce WWW:
 *    http://www.swi-prolog.org/pldoc/doc_for?object=
 * np.
 *    http://www.swi-prolog.org/pldoc/doc_for?object=write_length/3
 * lub jako argument predykatu help/1 w konsoli interpretera SWI
 * Prologu, np.
 *    ?- help(write_length/3).
 */

readClauses(FileName, Clauses) :-
   open(FileName, read, Fd),
   read(Fd, Clauses),
   close(Fd).

/* Wypisywanie dowodu */

writeProof(Proof) :-
   maplist(clause_width, Proof, Sizes),
   max_list(Sizes, ClauseWidth),
   length(Proof, MaxNum),
   write_length(MaxNum, NumWidth, []),
   nl,
   writeClauses(Proof, 1, NumWidth, ClauseWidth),
   nl.

clause_width((Clause, _), Size) :-
   write_length(Clause, Size, []).

writeClauses([], _, _, _).
writeClauses([(Clause,Origin) | Clauses], Num, NumWidth, ClauseWidth) :-
   format('~t~d~*|.  ~|~w~t~*+  (~w)~n',
          [Num, NumWidth, Clause, ClauseWidth, Origin]),
   Num1 is Num + 1,
   writeClauses(Clauses, Num1, NumWidth, ClauseWidth).

/* twi 2016/03/13 vim: set filetype=prolog fileencoding=utf-8 : */
