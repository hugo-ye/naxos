queens(N, Board) :-

	length(Board, N),
	Board :: 1..N,

	( fromto(Board, [Q1|Cols], Cols, []) do
	    ( foreach(Q2, Cols), param(Q1), count(Dist,1,_) do
		Q2 #\= Q1,
		Q2 - Q1 #\= Dist,
		Q1 - Q2 #\= Dist
	    )
	),

	labeling(Board).
