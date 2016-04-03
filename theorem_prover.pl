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

/*Piotr Maślankowski
  nr indeksu: 280354
  Metody programowania: Pracownia nr 2
  Dowodzenie sprzeczności zbioru klauzul metodą rezolucji
  Zaiplementowane optymalizacje: usuwanie powtórzeń zmiennych, usuwanie
  nadzbiorów z listy klauzul oraz niedodawanie par zawierających p v ~p
  Rozwiązanie wykorzystuje biblioteki ordsets oraz assoc.*/

%predykat zamieniający formułę na zbiór literałów.
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

%predykat sprawdzający czy klauzula zawiera parę postaci p v ~p
isNotTrue([], _).
isNotTrue([H|Clause],Acc) :-
	not(H, NH),	
	\+member(NH, Acc),
	isNotTrue(Clause, [H|Acc]).	
isNotTrue(Clause) :-
	isNotTrue(Clause, []).

%predykat sprawdzający czy coś nie jest nadzbiorem
isNotSuperset([], _).
isNotSuperset([H|T], Clause) :-
	\+ord_subset(H, Clause),
	isNotSuperset(T, Clause).

%usuwanie nadzbiorów
removeSupersets([], []).
removeSupersets([H|Clauses], R) :-
    (   select(X, Clauses, Clauses1),
        ord_subset(H, X) ->  removeSupersets([H|Clauses1], R); R = [H|Clauses2],
        removeSupersets(Clauses, Clauses2)
    ).

order(<, L1, L2) :-
	length(L1, X),
	length(L2, Y),
	X < Y.
order(>, L1, L2) :-
	length(L1, X),
	length(L2, Y),
	X >= Y.

%zamiana danych wejściowych na postać wykorzystywaną w programie - numerowanie klauzul, początek dowodu
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
	get_assoc(C1, Map, I1),
	get_assoc(C2, Map, I2),
	I1 < I2,
	resolve(C1, C2, R),
	\+member(R, Clauses),
	isNotTrue(R),
	isNotSuperset(Clauses, R), !.

prove(Clauses, _, Map, ProofAcc, Proof) :- 
	resolve(Clauses, Map, I1, I2, []), !,
	append(ProofAcc, [([], I1, I2)], Proof).
prove(Clauses, CurrentNumber, Map, ProofAcc, Proof) :-
	resolve(Clauses, Map, I1, I2, R),
	removeSupersets([R|Clauses], UnsortedClauses),
	predsort(order, UnsortedClauses, NewClauses),
	put_assoc(R, Map, CurrentNumber, NewMap),
	NewNumber is CurrentNumber+1,
	normClause_(Normalised, R),
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
