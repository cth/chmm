%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraint checker implementations
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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Queue implementation. Possibly replace with
% something more sophisticated/efficient later on..

empty_queue(q(0, Ys, Ys)).
enqueue(X, q(N, Ys, [X|Zs]), q(N1, Ys, Zs)) :- N1 is N+1.
dequeue(X, q(N, [X|Ys], Zs), q(N1, Ys, Zs)) :- N1 is N-1.
queue_size(q(Size,_,_),Size).

