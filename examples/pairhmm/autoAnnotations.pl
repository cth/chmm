% cl(autoAnnotations).  or [autoAnnotations].  % cl for compile
%
% Version 2.1 for PRISM 1.12 and higher. January 2009
% Changes:
%  - PRISM has a viterbit that produces a proper tree (so the code gets cleaner).
%  - PRISMs target declaration is obsolete - which is fine as previous version of
%           autoAnnotations did not treat it correctly.
%
% This file defines a preprocessor for PRISM programs that include
% annotations, which are redundant arguments intended to present
% abstract descriptions from the data being modelled.
%
% Such annotations can be extracted from the proof trees generated
% by PRISM's viterbi predicates, but this is quite tedious to program
%
% Such annotations in a model tend to make PRISM's viterbi calculations run very slow
% (in many cases, prohibitively slow).
% On the other hand, annotations are
% 1. essential for doing supervised learning
% 2. convenient when presenting predictions (most probably analyses) for the user.
%
% The autoAnnotations snystem takes a PRISM program that includes annotations;
% the user must indicate which arguments that are annotations by a special syntax
% illustrated in the supplied sample file.
% It can produce automatically, the following programs
% (1) a version of the PRISM program without annotations
%     - useful for viterbi analyses
% (2) an executable version of the PRISM program with annotations
%     - useful for initial testing of the model, for sampling and for supervised learning
%       Probabilities found by learning with program (2) can be used with program (1)
% (3) a translator from the proof trees produced by program (1) under viterbi prediction
%
% The main advantage of using autoAnnotations is that you need only maintain
% a single program containing the 'logic' of your model.

% %%Written by Henning Christiansen, henning@ruc.dk, (c) 2008
% %%Beta version, December 2008; testing still very limited
%  %% Beta was tested extensively by students - no bugs were found
%
% Version 2 is developed Jan 2009 - based on new facilities of PRISM 1.12 
%% 
% Bug fixed 30 mar 2009 -> v 2.1
% - nb: fix is based on undocumented prism predicate '$is_prob_pred'(Pname,Parity)
%
% Fixed to use $pd_is_prob_pred instead of deprecated $is_prob_pred (works with PRISM ver. 2.x)
%
% STILL NEEDS TO BE TRIMMED FOR OPTIMAL STORAGE UTILIZATION

:- write(user,'autoAnnotations in PRISM, version 2.1, (c) Henning Christiansen 2009'),
   nl(user),
   write(user,'  to be used with PRISM 1.12 or higher.'),
   nl(user), nl(user).

:- op(901, fy, --).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%  Top level predicates

prismAnnot(File):- prismAnnot(File,separate).

prismAnnot(File,separate):-
   annotModelToAbstract(File,ExecFile),
   prism(ExecFile),
   annotModelToProofTree2AnnotMapping(File,NewProgramFile),
   cl(NewProgramFile).

prismAnnot(File,direct):-
   annotModelToExcutableAnnot(File,ExecFile),
   prism(ExecFile).

viterbiAnnot(Call,P):-
    remove_annot_args_from_actual_call(Call,CallNoAtt,_AnnList),
    viterbit(CallNoAtt, P, T),
    addProofTreeArgument(Call,T,CallWithTree),
    call(CallWithTree).

% Use PRISM's tools for executing the direct version of the program
% Thus viterbig/2 is analogous to viterbiAnnot.

% For learning you need to work with the 'direct' program, and then
% put probabilities into a file - and then load them in when you have compiler
% the separate program.

% Using both prismAnnot(File,separate) and prismAnnot(File,direct) at the same
% time is not possible; only the most recent one counts.

% After the testing period, we will revise the set of available top-level predicates.

%
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Helpers for viterbifAnnot

remove_annot_args_from_actual_call(Call,CallNoAtt,AnnList):-
    Call=..[P|ArgList],
    functor(Call,P,N), length(L,N),
    Pattern=..[P|L],
    (predicate_annotation_pattern(Pattern) ->
       Pattern=..[_|PatternList],
       remove_annot_args_from_arglist(ArgList,PatternList,ObsList,AnnList)
     ;
     write(user,'Could not find predicate definition with annotations,'), nl(user),
     write(Call),  nl(user),
     write(user,'I give up.') ),
    CallNoAtt=..[P|ObsList].

remove_annot_args_from_arglist([],[],[],[]).

remove_annot_args_from_arglist([A|As],[annott|Ps],As1,[A|Obs1]):-
    remove_annot_args_from_arglist(As,Ps,As1,Obs1).

remove_annot_args_from_arglist([A|As],[observ|Ps],[A|As1],Obs1):-
    remove_annot_args_from_arglist(As,Ps,As1,Obs1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Removing annotation arguments and auxiliary calls %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

 % no extension on input file name; .psm assumed
 
annotModelToAbstract(FileName, FileNameNO_ANNOTsDotPsm):- 
     retractall(predicate_annotation_pattern(_)),
     retractall(predicate_annotation_count_args(_,_,_)),
   name(FileName,FileNameChars),
   append(FileNameChars,".psm", FileNameDotPsmChars),
   name(FileNameDotPsm,FileNameDotPsmChars),
   append(FileNameChars,"NO_ANNOTs.psm", FileNameNO_ANNOTsDotPsmChars),
   name(FileNameNO_ANNOTsDotPsm,FileNameNO_ANNOTsDotPsmChars),
   see(FileNameDotPsm),
   tell(FileNameNO_ANNOTsDotPsm),
   annotModelToAbstractOneClauseAtATime,
   seen,
   told,
   write(user,'Written file '), write(user,FileNameNO_ANNOTsDotPsm), nl(user).
   %% WE KEEP THOSE
     %%%retractall(predicate_annotation_pattern(_)),
     %%%retractall(predicate_annotation_count_args(_,_,_)).

annotModelToAbstractOneClauseAtATime:-
   read(C),
   (var(C) -> write(user,'Variable seen where clause is expected.'),nl,
               write(user,'I give up.'),nl, seen, told, abort
     ;
     C= end_of_file -> nl
     ;
     C = (:- Z) -> portray_directive((:- Z)),nl,
     annotModelToAbstractOneClauseAtATime
     ;
     removeAnnotationsClause(C,C1),
     portray_clause(C1),nl,
     annotModelToAbstractOneClauseAtATime).
     


%% removeAnnotations<type>(Term,TermNoAnnots)

removeAnnotationsClause((H:-B), C1):-
    !,
    removeAnnotationsHeadAtom(H,H1),
    removeAnnotationsGoals(B,B1),
    (nonvar(B1), B1 = true -> C1=H1
       ;
       C1 = (H1:-B1)).

removeAnnotationsClause(H,C1):-
    removeAnnotationsClause((H:-true),C1).

removeAnnotationsHeadAtom(X,X1):-
    nonvar(X), X = (--_) ->
      write(user,'Annotation code as head of clause; I give up'),
      nl(user), seen, told, abort
    ;
    removeAnnotationsAtom(X,X1).

removeAnnotationsAtom(X,X):- var(X), !.

removeAnnotationsAtom(T,T1):-
   check_annotation_pattern(T),
   T =.. [F|Ts],
   removeAnnotationsArgsList(Ts,Ts1),
   T1 =.. [F|Ts1].

removeAnnotationsGoals(X,X):- var(X), !.

removeAnnotationsGoals((X, Y), Y1):-
   nonvar(X), X = (--_),
   !,
   removeAnnotationsGoals(Y,Y1).

removeAnnotationsGoals((X, Y), X1):-
   nonvar(Y), Y = (--_),
   !,
   removeAnnotationsGoals(X,X1).

removeAnnotationsGoals((X;Y), (X1;Y1)):-
   !,
   removeAnnotationsGoals(X,X1),
   removeAnnotationsGoals(Y,Y1).

removeAnnotationsGoals((X,Y), (X1,Y1)):-
   !,
   removeAnnotationsGoals(X,X1),
   removeAnnotationsGoals(Y,Y1).

removeAnnotationsGoals((X->Y), (X1->Y1)):-
   !,
   removeAnnotationsGoalsNO_ANNOTS_ALLOWED(X,X1),
   removeAnnotationsGoals(Y,Y1).

removeAnnotationsGoals((\+ G),(\+ G1)):-
   !,
   removeAnnotationsGoals(G,G1).

removeAnnotationsGoals((--_),true):- !.

removeAnnotationsGoals(A,A1):- removeAnnotationsAtom(A,A1).

removeAnnotationsGoalsNO_ANNOTS_ALLOWED(G, _):-
   nonvar(G), G = (--_), !,
   write(user,'Annotation code found as condition: (--HERE -> ...); I give up.'),
   nl(user),
   seen, told, abort.

removeAnnotationsGoalsNO_ANNOTS_ALLOWED((X,Y),(X1,Y1)):-
    !,
    removeAnnotationsGoalsNO_ANNOTS_ALLOWED(X,X1),
    removeAnnotationsGoalsNO_ANNOTS_ALLOWED(Y,Y1).

removeAnnotationsGoalsNO_ANNOTS_ALLOWED((X;Y),(X1;Y1)):-
    !,
    removeAnnotationsGoalsNO_ANNOTS_ALLOWED(X,X1),
    removeAnnotationsGoalsNO_ANNOTS_ALLOWED(Y,Y1).


removeAnnotationsGoalsNO_ANNOTS_ALLOWED((X->Y), (X1->Y1)):-
   !,
   removeAnnotationsGoalsNO_ANNOTS_ALLOWED(X,X1),
   removeAnnotationsGoalsNO_ANNOTS_ALLOWED(Y,Y1).

removeAnnotationsGoalsNO_ANNOTS_ALLOWED((\+ G),(\+ G1)):-
   !,
   removeAnnotationsGoalsNO_ANNOTS_ALLOWED(G,G1).
   
removeAnnotationsGoalsNO_ANNOTS_ALLOWED(A,A1):- removeAnnotationsAtom(A,A1).

removeAnnotationsArgsList([],[]).

removeAnnotationsArgsList([T|Ts],Ts1):-
   nonvar(T), T = (--_),
   !,
   removeAnnotationsArgsList(Ts,Ts1).

removeAnnotationsArgsList([T|Ts],[T|Ts1]):-
   removeAnnotationsArgsList(Ts,Ts1).

%% bookkeeping to check that --args are used in a consistent way
%% and that the removal of them does not introduce inconsistencies

:- dynamic predicate_annotation_pattern/1.
     % for checking inconsistent use
     % e.g. p(--a, b) --> predicate_annotation_pattern(p(annott,observ))
:- dynamic predicate_annotation_count_args/3.
     % for checking that different predicates are not mixed up by
     % argument removal
     % e.g. p(--a, b, --c) --> predicate_annotation_count_args(p,3,1))
     % i.e., p/3 is translated into p/1

check_annotation_pattern(Atom):-
    Atom=.. [P|Ts],
    classify_arg_annot_or_not_annot(Ts,TsClass,NewArity),
    Pattern=.. [P|TsClass],
    length(Ts,L), length(Vars,L),
    Matcher=..[P|Vars],
    (predicate_annotation_pattern(Matcher)
       ->  (Matcher == Pattern -> true
              ;
              write(user,'Predicate used with inconsistent annotations arguments.'),
              nl(user),
              write(user,Matcher),nl(user),
              write(user,Pattern),nl(user),
              write(user,'I give up.'), nl(user), seen, told, abort )
        ;
      assert(predicate_annotation_pattern(Pattern))),
    (predicate_annotation_count_args(P,L,_) -> true
       ; assert(predicate_annotation_count_args(P,L,NewArity)) ),
    % now, check others
    (predicate_annotation_count_args(P,L1,NewArity), L\= L1
       -> write(user,'Predicates coinside when annotations are removed,'),
          nl(user),
          write(user,P/L1), write(user,' and '), write(user,P/L),
            write(user,' (arity shown with possible annotations)'),
           %% PERHAPS SHOW PATTERNS INSTEAD?
          nl(user),
          write(user,'I give up.'), nl(user), seen, told, abort
        ; true).

classify_arg_annot_or_not_annot([],[],0).

classify_arg_annot_or_not_annot([V|Ts],[observ|Cs],Aplus1):-
    var(V), !,
    classify_arg_annot_or_not_annot(Ts,Cs,A),
    Aplus1 is A+1.

classify_arg_annot_or_not_annot([--_|Ts],[annott|Cs],A):-
    !,
    classify_arg_annot_or_not_annot(Ts,Cs,A).

classify_arg_annot_or_not_annot([_|Ts],[observ|Cs],Aplus1):-
    !,
    classify_arg_annot_or_not_annot(Ts,Cs,A),
    Aplus1 is A+1.




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Make programs in the special syntax executable    %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


annotModelToExcutableAnnot(FileName,FileNameEXDotPsm):- % no extension
   name(FileName,FileNameChars),
   append(FileNameChars,".psm", FileNameDotPsmChars),
   name(FileNameDotPsm,FileNameDotPsmChars),
   append(FileNameChars,"EX.psm", FileNameEXDotPsmChars),
   name(FileNameEXDotPsm,FileNameEXDotPsmChars),
   see(FileNameDotPsm),
   tell(FileNameEXDotPsm),
   annotModelToExcutableAnnotOneClauseAtATime,
   seen,
   told,
   write(user,'Written file '), write(user,FileNameEXDotPsm), nl(user).

annotModelToExcutableAnnotOneClauseAtATime:-
   read(C),
   (C= end_of_file -> nl
     ;
     var(C) -> write(user,'Variable seen where clause is expected.'),nl,
               write(user,'I give up.'),nl, seen, told, abort
     ;
     C = (:- Z) -> portray_directive((:- Z)), nl,nl,
     annotModelToExcutableAnnotOneClauseAtATime
     ;
     removeAnnotationIndicator(C,C1),
     portray_clause(C1),nl,
     annotModelToExcutableAnnotOneClauseAtATime).

removeAnnotationIndicator(X,X):- var(X), !.

removeAnnotationIndicator(--X,X):- !.

removeAnnotationIndicator(T,T1):-
    T=..[F|Ts],
    removeAnnotationIndicatorList(Ts,T1s),
    T1=..[F|T1s].

removeAnnotationIndicatorList([],[]).

removeAnnotationIndicatorList([T|Ts],[T1|Ts1]):-
    removeAnnotationIndicator(T,T1),
    removeAnnotationIndicatorList(Ts,Ts1).



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Producing the proof tree --> annotation mapping   %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% This is basically a version of the original program with annotation
%% which extended with a control argument (the proof tree produced by
%% PRISMs viterbit)
%%
%% 


annotModelToProofTree2AnnotMapping(FileName,NewProgramFile):-
   list_of_preds_defined_in_file(FileName,PredList),
   annotModelToProofTree2AnnotMapping(FileName,PredList,NewProgramFile).



annotModelToProofTree2AnnotMapping(FileName,PredList,FileNameTREE2ANN_DotPL):-
   name(FileName,FileNameChars),
   append(FileNameChars,".psm", FileNameDotPsmChars),
   name(FileNameDotPsm,FileNameDotPsmChars),
   append(FileNameChars,"TREE2ANN.pl", FileNameTREE2ANN_DotPLChars),
   name(FileNameTREE2ANN_DotPL,FileNameTREE2ANN_DotPLChars),
   see(FileNameDotPsm),
   tell(FileNameTREE2ANN_DotPL),
   annotModelToProofTree2AnnotMappingOneClauseAtATime(PredList),
   seen,
   told,
   write(user,'Written file '), write(user,FileNameTREE2ANN_DotPL), nl(user).

annotModelToProofTree2AnnotMappingOneClauseAtATime(PredList):-
   read(C),
   (C= end_of_file -> nl
     ;
     (C = (H:-B) -> true ; H=C, B=true),
     functor(H,P,N),
     (member(P/N,PredList) ->
        (removeAnnotationIndicator(H,H1),
         addProofTreeArgument(H1,ProofTreeVar,NewHead),
         % at runtime, ProofTreeVar will hold a tree for this particular call
         (B=true -> portray_clause(NewHead), nl
          ;
             removeAnnotationsAtom(H,H_NoAnn),
             B=B1, % Done after translate instead: removeAnnotationIndicator(B,B1),
             addProofTreeStuffToBody(B1,B2,PredList,RecCallTreesStoreRef,MswsStoreRef),
             removeAnnotationIndicator(B2,B3),
             (abstract_version_of_pred_probabilistic(H) ->
                 NewBody = ( split_viterbit_tree_into_parts(ProofTreeVar,TopVar,RecCallsVar,MswsVar),
                             TopVar = H_NoAnn,
                             global_store_for_list_of_calls(RecCallTreesStoreRef, RecCallsVar),
                             global_store_for_list_of_calls(MswsStoreRef, MswsVar),
                             B3,
                             clean_global_store_for_list_of_calls(RecCallTreesStoreRef),
                            clean_global_store_for_list_of_calls(MswsStoreRef) )
               ;
             
                 NewBody = B3),
             
             portray_clause((NewHead:-NewBody)), nl
         )
        )
      ; true),
     
     annotModelToProofTree2AnnotMappingOneClauseAtATime(PredList)
    ).


list_of_preds_defined_in_file(FileName,PredList):-  % no file extension; '.psm' expected
   name(FileName,FileNameChars),
   append(FileNameChars,".psm", FileNameDotPsmChars),
   name(FileNameDotPsm,FileNameDotPsmChars),
   see(FileNameDotPsm),
   list_of_preds_defined_in_fileOneClauseAtATime([],PredList), % given each as P/N
   seen.

list_of_preds_defined_in_fileOneClauseAtATime(OldList,EndList):-
   read(C),
   (C = end_of_file -> OldList=EndList
    ;
    ( (C = (H:-_) -> true ; H=C),
      functor(H,P,N),
      (predicate_to_ignore_in_tree2annot_translation(H) ->
         OldList = NextList
       ; member(P/N, OldList) -> OldList = NextList
       ;
         NextList = [P/N | OldList]),
      list_of_preds_defined_in_fileOneClauseAtATime(NextList,EndList))).


%%% addProofTreeStuffToBody(B,B1,PredList,StoreRef,ProofTreeVar):-
%%%%addProofTreeStuffToBody(B1,B2,PredList,RecCallTreesStoreRef,MswsStoreRef)    

addProofTreeStuffToBody( call(_), _,_,_):-
   !,
   write(user,'Meta-calls not supported by proof tree -> annotation system.'),
   nl(user),
   write(user,'I give up.'),
   nl(user),
   seen, told, abort.

addProofTreeStuffToBody((A,B),(A1,B1),PredList,RecCallTreesStoreRef,MswsStoreRef):-
   !,
   addProofTreeStuffToBody(A,A1,PredList,RecCallTreesStoreRef,MswsStoreRef),
   addProofTreeStuffToBody(B,B1,PredList,RecCallTreesStoreRef,MswsStoreRef).

addProofTreeStuffToBody((A;B),(A1;B1),PredList,RecCallTreesStoreRef,MswsStoreRef):-
   !,
   addProofTreeStuffToBody(A,A1,PredList,RecCallTreesStoreRef,MswsStoreRef),
   addProofTreeStuffToBody(B,B1,PredList,RecCallTreesStoreRef,MswsStoreRef).

addProofTreeStuffToBody((A->B),(A1->B1),PredList,RecCallTreesStoreRef,MswsStoreRef):-
   !,
   addProofTreeStuffToBody(A,A1,PredList,RecCallTreesStoreRef,MswsStoreRef),
   addProofTreeStuffToBody(B,B1,PredList,RecCallTreesStoreRef,MswsStoreRef).


addProofTreeStuffToBody((\+ A),(\+ A1),PredList,RecCallTreesStoreRef,MswsStoreRef):-
   !,
   addProofTreeStuffToBody(A,A1,PredList,RecCallTreesStoreRef,MswsStoreRef).

addProofTreeStuffToBody( msw(Sw,Val),
               next_call_from_global_store(MswsStoreRef, msw(Sw,Val)),
               _,_,MswsStoreRef):-
   !.
    


addProofTreeStuffToBody(A,NewCall,
                        PredList,RecCallTreesStoreRef,_):-
   functor(A,P,N),
   member(P/N,PredList),
   !,
   addProofTreeArgument(A,Subtree,A1),
   (abstract_version_of_pred_probabilistic(A) ->
      NewCall = (next_call_from_global_store(RecCallTreesStoreRef,Subtree),A1)
    ;
      NewCall = A1).

   

addProofTreeStuffToBody(A,A,_,_,_).

%%%%%%%%%%

%%% predicate_to_ignore_in_tree2annot_translation(target(_,_)). % not relevant
predicate_to_ignore_in_tree2annot_translation(values(_,_)).
predicate_to_ignore_in_tree2annot_translation((:- _)).
% If the user defines non-probabilistic aux pred's they will
% be compiled as well; useless but makes no harm...
% we should in principle make an analysis of which predicates are probabilistic



%%%%%%%%%%%%%%%%%%%%
%
% Helpers to be used during compilation

tree2annotPredName(PredName,ExtendedPredName):-
    name(PredName,PredNameChars),
    append(PredNameChars,"TREE2ANNOT",ExtendedPredNameChars),
    name(ExtendedPredName,ExtendedPredNameChars).
    
addProofTreeArgument(Atom,TreeArg,Atom1):-
   Atom=..[P|As],
   append(As,[TreeArg],As1),
   tree2annotPredName(P,PXX),
   Atom1=..[PXX|As1].

%%%%
% 
% Helpers to be used when the trees->annot programs are executed
%
%
% The following used within one rule activation;
% apply one "global_store" for msw's and one for recursive calls to prob. preds.
%
% It uses an att. var as a global variable since it is otherwise difficult to
% to pass the msw and subtree lists since it is determined during execution where in the code
% the next msw/rec-call instance is taken from the list
% One rule activation uses its own 'SomeVar' below.

global_store_for_list_of_calls(SomeVar, MswList):-
   put_attr_no_hook(SomeVar, msw_list, MswList).

next_call_from_global_store(SomeVar, Pattern):-
   get_attr(SomeVar, msw_list, MswList),
   (MswList = [Pattern | RestMswList]
      -> put_attr_no_hook(SomeVar, msw_list, RestMswList)
    ;
         write(user,'Expected to match '),
         write(user,Pattern),
         write(user,' as head of '),
         write(user,MswList), write(user,'.'),
         nl(user),
         write(user,'I give up.'),
         nl(user)).

clean_global_store_for_list_of_calls(SomeVar):-
   get_attr(SomeVar, msw_list, MswList),
   del_attr(SomeVar, msw_list),
   (MswList = []
      -> true
    ;
         write(user,'Expected call-list list to be empty but found '),
         write(user,MswList),
         write(user,'.'),
         nl(user),
         write(user,'I give up.'),
         nl(user)).

split_viterbit_tree_into_parts([Top| Rest],Top,RecCalls, Msws):-
   !,
   filter_recCalls_and_msws(Rest,RecCalls, Msws).
   
split_viterbit_tree_into_parts(Top,Top,[],[]).

filter_recCalls_and_msws([],[],[]).

filter_recCalls_and_msws([msw(Sw,Val)|More],RecCalls,[msw(Sw,Val)|Msws]):-
   !,
   filter_recCalls_and_msws(More,RecCalls,Msws).

filter_recCalls_and_msws([RecCall|More],[RecCall|RecCalls],Msws):-
   filter_recCalls_and_msws(More,RecCalls,Msws).

%%%%%%%%%%
%%
%% a little Aux:

portray_directive((:- BLABLA)):-
    write(':- '),
    portray_directive_single_goals(BLABLA),
    write('.'),nl.

portray_directive_single_goals((A,B)):-
   !,
   portray_directive_single_goals(A), write(','), nl, write('   '),
   portray_directive_single_goals(B).

portray_directive_single_goals(A):- writeq(A).


%%%% ANother little helper that uses undocumented PRISM feature and expects
%%%% that the program has been compiled with annotModelToAbstract already
%%%% used by the part that produces the TREE2ANN code.

abstract_version_of_pred_probabilistic(Atom):-
    removeAnnotationsHeadAtom(Atom,Atom1),
    functor(Atom1,P,N),
    '$pd_is_prob_pred'(P,N).
