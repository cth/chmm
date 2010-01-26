
mk_seq(0,[]).
mk_seq(Len,[a|Seq]) :-
	Len1 is Len - 1,
	mk_seq(Len1,Seq).

ms(G,T) :-
 statistics(runtime,_),
 call(G),
 write('here'),
 statistics(runtime,[_,T]),
 write('here'),
 statistics(table,[TableInUse,_TableTotal]),
 write('here'),
 statistics(heap,[HeapInUse,_HeapTotal]),
 write('here'),
 write('running time:'), write(T),nl,
 write('here'),
 write('heapspace used:'), write(HeapInUse),nl,
 write('here'),
 write('tablespace used:'), write(TableInUse),nl.

align(Size) :-
	mk_seq(Size,S1),mk_seq(Size,S2),viterbi(cpairhmm(S1,S2)).

