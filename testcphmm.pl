
mk_seq(0,[]).
mk_seq(Len,[a|Seq]) :-
	Len1 is Len - 1,
	mk_seq(Len1,Seq).

diff_seqs(50,A,B) :-
B = [a,c,g,t,a,  c,g,t,a,g, c,g,t,a,g],
A = [a,a,a,a,c, c,c,c,g,a, c,c,c,g,a].


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

align_diff_seqs(Size) :-
	diff_seqs(Size,S1,S2),viterbi(cpairhmm(S1,S2)).


