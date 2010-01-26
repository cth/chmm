mk_seq(0,[]).

mk_seq(Len,[a|Seq]) :-
	Len1 is Len - 1,
	mk_seq(Len1,Seq).
