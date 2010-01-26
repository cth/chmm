%--------------------------------------------
% Constrained Pair HMM
% Christian Theil Have, Jan. 2010.
%--------------------------------------------

% Use for debugging:
%cmsw(A,B) :- values(A,AVals), member(B,AVals).

cmsw(A,B) :- msw(A,B).

% List of symbols which may be used in sequences aligned.
alphabet([a,c,g,t]).
%alphabet([a]).

match_permutations(A,P) :-
	findall([X,Y], (member(X,A),member(Y,A)), P).

% MSW declarations

values(emit(insert), ABList) :-
	findall(AB,(alphabet(A),member(E,A),emit(insert,E,-,AB)),ABList).

values(emit(delete), ABList) :-
	findall(AB,(alphabet(B),member(E,B),emit(delete,-,E,AB)),ABList).

values(emit(match), AB) :-
	alphabet(A),
	match_permutations(A,AB).

values(trans(begin),[match,delete,insert]).
values(trans(match), [match,delete,insert]).
values(trans(insert), [match,insert]).
values(trans(delete), [match,delete]).

emit(match, A, B, [A,B]).
emit(delete, _, B, [-,B]).
emit(insert, A, _, [A,-]).

cpairhmm(InputA,InputB) :-
	init_constraint_store,
	cpairhmm(begin,InputA,InputB).

cpairhmm(PreviousState,[],[B|BRest]) :-
	cmsw(trans(PreviousState), delete),
	cmsw(emit(delete), Emit),
	emit(delete,-,B,Emit),
	check_constraints([delete,Emit]),
	cpairhmm(delete,[],BRest).

cpairhmm(PreviousState,[A|ARest],[]) :-
	cmsw(trans(PreviousState), insert),
	cmsw(emit(insert), Emit),
	emit(insert,A,-,Emit),
	check_constraints([insert,Emit]),
	cpairhmm(insert,ARest,[]).

cpairhmm(PreviousState,[A|ARest],[B|BRest]) :-
	cmsw(trans(PreviousState), NextState),
	cmsw(emit(NextState),Emit),
	emit(NextState,A,B,Emit),
	check_constraints([NextState,Emit]),
	((NextState==match,
	  cpairhmm(NextState,ARest,BRest))
	;
	 ((NextState==insert,
	  cpairhmm(NextState,ARest,[B|BRest])))
	;
	 ((NextState==delete,
	  cpairhmm(NextState,[A|ARest],BRest)))).

cpairhmm(_,[],[]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Some basic machinery/glue for linking together constraint checks

init_constraint_store :-
	constraint_checks(Checks),
	init_constraint_stores(Checks,IndvStores),
	init_global_constraint_store,
	update_global_constraint_store(IndvStores).

init_global_constraint_store :-
	retractall(constraint_store(_)),
	assert(constraint_store([[],nil])).

update_global_constraint_store(NewStore) :-
	retract(constraint_store([PrevStore,Rest])),
	assert(constraint_store([NewStore,[PrevStore,Rest]])).

update_global_constraint_store(NewStore) :- 
	retract(constraint_store([NewStore,PrevStore])),
	assert(constraint_store(PrevStore)).

init_constraint_stores([],[]).
init_constraint_stores([Check|CheckRest],[Store|StoreRest]) :-
	init_constraint_store(Check,Store),
	init_constraint_stores(CheckRest,StoreRest).

% Constraint check is called for each change of state in the model, which
% could possible lead to a constraint-violation.
check_constraints(StateUpdate) :-
	!,
	constraint_checks(Checks),
	constraint_store([StoreBefore,_]),
	constraint_store(S),
	%write('constraint store: '), write(S), nl,
	check_each_constraint(StateUpdate,Checks,StoreBefore,StoreAfter),
	update_global_constraint_store(StoreAfter).

check_each_constraint(_,[],[],[]).

check_each_constraint(StateUpdate,[Check|ChecksRest],
		      [StoreBefore|StoreBeforeRest],
		      [StoreAfter|StoreAfterRest]) :-
	constraint_check(Check,StateUpdate,StoreBefore,StoreAfter),
	!,
	check_each_constraint(StateUpdate,ChecksRest,StoreBeforeRest,StoreAfterRest).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Queue implementation. Possibly replace with
% something more sophisticated/efficient later on..

empty_queue(q(0, Ys, Ys)).
enqueue(X, q(N, Ys, [X|Zs]), q(N1, Ys, Zs)) :- N1 is N+1.
dequeue(X, q(N, [X|Ys], Zs), q(N1, Ys, Zs)) :- N1 is N-1.
queue_size(q(Size,_,_),Size).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraint implementations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

init_constraint_store(max_visits(_,_),[0]).
init_constraint_store(max_visits_relative(_,_,_),[Queue,0]) :- empty_queue(Queue).
init_constraint_store(fix_alignment(_,_,Alignment),[1,1,Alignment]).

% Non-backtrackable hash table version
% init_constraint_store(alldifferent, Store) :- new_hashtable(Store).

init_constraint_store(alldifferent,[]).

%%% Constraint: max_visits(State,MaxVisits)
% Enforce an absolute bound on the number of visits
% to a particular state.

constraint_check(max_visits(State,Max), [State,_], [VisitsBefore], [VisitsAfter]) :-
	VisitsAfter is VisitsBefore + 1,
	VisitsAfter =< Max.

constraint_check(max_visits(ConstraintState,_), [VisitState,_], BeforeAndAfter,BeforeAndAfter) :-
	ConstraintState \= VisitState.

%%% Constraint: max_visit_relative(State,MaxVisits,WindowSize)
% This constraint enforces that a particular state is visited
% at most MaxVisits in any state sequence of WindowSize length


constraint_check(max_visits_relative(ConstrainedStates,MaxVisits,WindowSize),
		 [State,_],
		 [QueueBefore,VisitsBefore], [QueueAfter,VisitsAfter]) :-
	enqueue(State,QueueBefore,TmpQueue),
	queue_size(TmpQueue,QueueSize),
	((QueueSize > WindowSize) ->
	 dequeue(ForgetState,TmpQueue,QueueAfter),
	 (member(ForgetState,ConstrainedStates) -> ForgottenVisits = 1 ; ForgottenVisits = 0)
	;
	 QueueAfter = TmpQueue, ForgottenVisits = 0),
	(member(State,ConstrainedStates) -> NewVisits = 1 ; NewVisits = 0),
	VisitsAfter is VisitsBefore + NewVisits - ForgottenVisits,
	VisitsAfter =< MaxVisits.

%%% Constraint: min_visit_relative(State,MinVisits,WindowSize)
% This constraint enforces that a particular state is visited
% at least MinVisits in any state sequence of WindowSize length
% FIXME: Implement


%%% Fix alignment constraint %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constrains the alignment of position m_1..m_x of sequence 1
% to be aligned to position n_1..n_y of sequence 2 in the way
% given by StateSequence


% As long as alignment positions in sequences have not yet been reached,
% do appropriate increment and :-)
constraint_check(fix_alignment(S1From,S2From,_),[State,_], [S1Pos,S2Pos,Align],[S1PosNext,S2PosNext,Align]) :-
	S1Pos < S1From,
	S2Pos < S2From,
	(member(State,[delete,match]) -> S1PosNext is S1Pos + 1 ; S1PosNext=S1Pos),
	(member(State,[insert,match]) -> S2PosNext is S2Pos + 1 ; S2PosNext=S2Pos).

% If both sequence position has been incremented to the alignment start position,
% then we compare with the sequence alignment.
% (if one sequences is incremented beyond the alignment start position then
% the constraint will fail!)
% Note that the constraint may be expressed as sequence of states of or as a
% sequence of emissions (a "ground" alignment) or a combination thereof
constraint_check(fix_alignment(S1From,S2From,_),[State,Emit],
		 [S1Pos,S2Pos,[CurPosAlign|AlignRest]],[S1Pos,S2Pos,AlignRest]) :-
	S1Pos == S1From,
	S2Pos == S2From,
	(Emit==CurPosAlign ; State==CurPosAlign).

% If the list for the alignment becomes empty then it has succesfully been checked:
constraint_check(fix_alignment(_,_,_),_,[S1,S2,[]],[S1,S2,[]]).

%%% Alldifferent constraint %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Make sure that all states in are different
% Uses a hashtable as constraint store.
% Does work under prism semantics :-(

/* Not backtrackable
constraint_check(alldifferent, [State,_],HashTable,HashTable) :-
	hash_code(State,HashCode),
	not(hashtable_get(HashTable,HashCode,_)),
	hashtable_register(HashTable,HashCode,visited).
*/


constraint_check(alldifferent,[State,_],StoreIn,[State|StoreIn]) :-
	not(member(State,StoreIn)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Tests
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint_checks([		   max_visits_relative([delete,insert],1,10),
	   max_visits([delete,insert],20)		  ]).
%constraint_checks([]).

ms(G,T) :-
 statistics(runtime,_),
 call(G),
 statistics(runtime,[_,T]),
 statistics(table,[TableInUse,TableTotal]),
 statistics(heap,[HeapInUse,HeapTotal]),
 write('running time:'), write(T),nl,
 write('heapspace used:'), write(HeapInUse),nl,
 write('tablespace used:'), write(TableInUse),nl.

align(Size) :-
	[seqdata], mk_seq(Size,S1),mk_seq(Size,S2),viterbi(cpairhmm(S1,S2)).

