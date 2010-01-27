
mk_seq(0,[]).
mk_seq(Len,[a|Seq]) :-
	Len1 is Len - 1,
	mk_seq(Len1,Seq).

ms(G,T) :-
 statistics(runtime,_),
 call(G),
 statistics(runtime,[_,T]),
 statistics(table,[TableInUse,_TableTotal]),
 statistics(heap,[HeapInUse,_HeapTotal]),
 write('running time:'), write(T),nl,
 write('heapspace used:'), write(HeapInUse),nl,
 write('tablespace used:'), write(TableInUse),nl.

align(Size) :-
	mk_seq(Size,S1),mk_seq(Size,S2),viterbi(cpairhmm(S1,S2)).

