%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Some basic machinery/glue for linking together constraint checks
% supports using either local and global constraint stores 


init_local_constraint_store(Store) :-
	constraint_checks(Checks),
	init_constraint_stores(Checks,Store).

init_global_constraint_store :-
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

% Global store version: check_constraints
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



% Local store version: check_constraints
% Constraint check is called for each change of state in the model, which
% could possible lead to a constraint-violation.
check_constraints(StateUpdate,ConstraintsBefore,ConstraintsAfter) :-
	constraint_checks(Checks),
	check_each_constraint(StateUpdate,Checks,ConstraintsBefore,ConstraintsAfter).

check_each_constraint(_,[],[],[]).

check_each_constraint(StateUpdate,[Check|ChecksRest],
		      [StoreBefore|StoreBeforeRest],
		      [StoreAfter|StoreAfterRest]) :-
	constraint_check(Check,StateUpdate,StoreBefore,StoreAfter),
	!,
	check_each_constraint(StateUpdate,ChecksRest,StoreBeforeRest,StoreAfterRest).

