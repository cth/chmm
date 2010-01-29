%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constraint checker implementations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Initialization of constraint stores for different types of constraints

init_constraint_store(state_specific(Constraint),Store) :-
    init_constraint_store(Constraint,Store).
init_constraint_store(emissions_specific(Constraint),Store) :-
    init_constraint_store(Constraint,Store).

init_constraint_store(for_range(_,_,Constraint), [0,ConstraintSpecificStore]) :-
	init_constraint_store(Constraint,ConstraintSpecificStore).

init_constraint_store(lock_to_sequence(Sequence),Sequence).

init_constraint_store(lock_to_set(_Set),[]).

init_constraint_store(global_cardinality(_,_),0).
init_constraint_store(local_cardinality(_,_,_),[Queue,0]) :- empty_queue(Queue).
init_constraint_store(fix_alignment(_,_,Alignment),[1,1,Alignment]).

% Non-backtrackable hash table version
% init_constraint_store(alldifferent, Store) :- new_hashtable(Store).

init_constraint_store(global_alldifferent,[]).
init_constraint_store(local_alldifferent(_WindowSize),Q) :- empty_queue(Q).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Implementation of constraint checker rules 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


%%% Constraint operator: state_specific(Constraint)
% When this operator is aplied to a constraint, then constraint only 
% applies to the state part of the update pattern

constraint_check(state_specific(Constraint), [State,_],StoreIn,StoreOut) :-
    constraint_check(Constraint,State,StoreIn,StoreOut).


%%% Constraint operator: emission_specific(Constraint)
% When this operator is aplied to a constraint, then constraint only 
% applies to the emission part of the update pattern

constraint_check(emission_specific(Constraint), [_,Emit],StoreIn,StoreOut) :-
    constraint_check(Constraint,Emit,StoreIn,StoreOut).


%%% The for_range operator %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Enforces a given constraint for a particular range:

% Succeed before range:
constraint_check(for_range(From,_,_),_,
		 [PositionBefore, ConstraintSpecificStore],
		 [PositionAfter, ConstraintSpecificStore]) :-
	PositionAfter is PositionBefore + 1,
	PositionAfter < From.

% Check in range
constraint_check(for_range(From,To,Constraint),Update,
		 [PositionBefore, ConstraintSpecificStoreBefore],
		 [PositionAfter, ConstraintSpecificStoreAfter]) :-
	PositionAfter is PositionBefore + 1,
	PositionAfter >= From,
	PositionAfter =< To,
	constraint_check(Constraint,Update,
			ConstraintSpecificStoreBefore,
			  ConstraintSpecificStoreAfter).

% Succeed after range:
constraint_check(for_range(_,To,_),_,
		 [PositionBefore, ConstraintSpecificStore],
		 [PositionAfter, ConstraintSpecificStore]) :-
	PositionAfter is PositionBefore + 1,
	PositionAfter > To.


%%% Constraint: global_cardinality(UpdatePatternList,MaxVisits)
% Enforce an absolute bound on the number of times a certain update pattern
% is seen a long a particular derivation path
constraint_check(global_cardinality(UpdatePatternList,Max), Update, VisitsBefore, VisitsAfter) :-
        member(Update,UpdatePatternList),
	VisitsAfter is VisitsBefore + 1,
	VisitsAfter =< Max.
constraint_check(global_cardinality(UpdatePatternList,_), Update, Same,Same) :-
        not(member(Update,UpdatePatternList)).

%%% Constraint: local_cardinality(UpdatePattern,MaxVisits,WindowSize)
% This constraint enforces that a update patern is seen 
% at most MaxVisits in any state sequence of WindowSize length
constraint_check(local_cardinality(UpdatePatternList,MaxVisits,WindowSize),
		 Update,
		 [QueueBefore,VisitsBefore], [QueueAfter,VisitsAfter]) :-
	enqueue(Update,QueueBefore,TmpQueue),
	queue_size(TmpQueue,QueueSize),
	((QueueSize > WindowSize) ->
	 dequeue(Forget,TmpQueue,QueueAfter),
	 (member(Forget,UpdatePatternList) -> ForgottenVisits = 1 ; ForgottenVisits = 0)
	;
	 QueueAfter = TmpQueue, ForgottenVisits = 0),
        (member(Update,UpdatePatternList) -> NewVisits = 1 ; NewVisits = 0),
	VisitsAfter is VisitsBefore + NewVisits - ForgottenVisits,
	VisitsAfter =< MaxVisits.

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

constraint_check(local_alldifferent(WindowSize),Update,QueueBefore,QueueAfter) :-
	queue_size(QueueBefore,QueueSize),
	((QueueSize >= WindowSize) -> dequeue(_,QueueBefore,TmpQueue) ; TmpQueue = QueueBefore),
        not(queue_member(Update,TmpQueue)),
        enqueue(Update,TmpQueue,QueueAfter).
        
%%% lock_to_set locks all states to a particular one
% May be applied in conjunction with various operatorrs (e.g. for_range,
% and state_specific...)
constraint_check(lock_to_set(Set),Update,Store,Store) :-
	member(Update,Set).

%%% lock_to_sequence locks all states in the sequence to a specified one
% May be applied in conjunction with various operatorrs (e.g. for_range,
% and state_specific...)
constraint_check(lock_to_sequence(_),_,[],[]).
constraint_check(lock_to_sequence(_),Update,[Update|UpdateRest],UpdateRest).

% SPECIFIC for the pairhmm: 
%%% Fix alignment constraint %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Constrains the alignment of position m_1..m_x of sequence 1
% to be aligned to position n_1..n_y of sequence 2 in the way
% given by StateSequence
% Note: This is specific for the pairhmm.

% As long as alignment positions in sequences have not yet been reached, do appropriate increment and :-)
constraint_check(fix_alignment(S1From,S2From,_),[State,_], [S1Pos,S2Pos,Align],[S1PosNext,S2PosNext,Align]) :-
	S1Pos < S1From,
	S2Pos < S2From,
	(member(State,[delete,match]) -> S1PosNext is S1Pos + 1 ; S1PosNext=S1Pos),
	(member(State,[insert,match]) -> S2PosNext is S2Pos + 1 ; S2PosNext=S2Pos).

% If both sequence position has been incremented to the alignment start position, then we compare with the sequence alignment.
% (if one sequences is incremented beyond the alignment start position then the constraint will fail!)
% Note that the constraint may be expressed as sequence of states of or as a sequence of emissions (a "ground" alignment) or a combination thereof
constraint_check(fix_alignment(S1From,S2From,_),[State,Emit],
		 [S1Pos,S2Pos,[CurPosAlign|AlignRest]],[S1Pos,S2Pos,AlignRest]) :-
	S1Pos == S1From,
	S2Pos == S2From,
	(Emit==CurPosAlign ; State==CurPosAlign).

% If the list for the alignment becomes empty then it has succesfully been checked:
constraint_check(fix_alignment(_,_,_),_,[S1,S2,[]],[S1,S2,[]]).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Queue implementation. Possibly replace with
% something more sophisticated/efficient later on..

empty_queue(q(0, Ys, Ys)).
enqueue(X, q(N, Ys, [X|Zs]), q(N1, Ys, Zs)) :- N1 is N+1.
dequeue(X, q(N, [X|Ys], Zs), q(N1, Ys, Zs)) :- N1 is N-1, N1 >= 0.
queue_size(q(Size,_,_),Size).

queue_member(Elem,Queue) :-
        dequeue(Elem,Queue,_).
queue_member(Elem,Queue) :-
        dequeue(OtherElem,Queue,RestQueue),
        Elem \= OtherElem,
        queue_member(Elem,RestQueue).




