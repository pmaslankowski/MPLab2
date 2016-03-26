:- op(200, fx, ~).
:- op(500, xfy, v).

appn([], Acc, [], Acc).
appn([H|T], Acc, End, Res) :-
	append(H, Hole, End),
	appn(T, Acc, Hole, Res). 
appn(L, Res) :-
	appn(L, Hole, Hole, Res).

normaliseClause(~X, ([], [X])) :-
	atom(X), !.
normaliseClause(X, ([X], [])) :-
	atom(X).
normaliseClause(~X v Y, (Pos, [X|Neg])) :-
	!, normaliseClause(Y, (Pos, Neg)).
normaliseClause(X v Y, ([X|Pos], Neg)) :-
	normaliseClause(Y, (Pos, Neg)).


findResolvent(([H|Pos1], Neg1), (Pos2, Neg2), (AccPos, AccNeg), (ResPos, ResNeg) ) :-
	member(H, Neg2),
	appn([Pos1, Pos2, AccPos], ResPos), 
	select(H, Neg2, Tmp),	
	appn([Neg1, Tmp, AccNeg], ResNeg),
	
	


	
