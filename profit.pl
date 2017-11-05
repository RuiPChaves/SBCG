/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:      profit.pl
% purpose:   ProFIT is Prolog with Features, Inheritance, and Templates
% created:   15 Feb 94 by Gregor Erbach, Universitaet des Saarlandes
% modified:  23 Mar 94, 12 Jun 94 
% note:      this version for Sicstus Prolog (updated by Mats Carlson; 2017)


:- module(profit,[
          portray/1,
          portray_message/2,		  
          term_expansion/2,
          (fit)/1,
          (reload)/1,
          load_profit/2,
          ('?')/1,
	  pp/1,
          hide_feature/1,
          show_hid_features/0,
          discover_feature/1,
          discover_all_features/0
          % member/2,
          % append/3,
          % nth/3 
          ]).
:- multifile portray/1.
:- op(900,fy,fit).
:- prolog_flag(syntax_errors,_,dec10).

compile_library(File) :- ensure_loaded(library(File)).
:- compile_library(lists).

% to keep the corresponding QP predicates from failing
style_check(single_var) :- 
	prolog_flag(single_var_warnings,_,on).

no_style_check(single_var) :- 
	prolog_flag(single_var_warnings,_,off).

%file_exists(Filename) :-  unix(access(Filename,0)).
:- use_module(library(system3), [
	file_exists/1
	]).

save_program2(A,_) :- save_program(A).

install :- 
   save_program(profits), halt.

% :- version('').
% :- version('ProFIT 1.54  -  03 Dec 1995  ').
% :- version(
% '(c) G. Erbach - DFKI and Universitaet des Saarlandes').
% :- version('').

:- nl, write('ProFIT 1.54  -  03 Dec 1995  '), nl, write(
   '(c) G. Erbach - DFKI and Universitaet des Saarlandes'),
   nl, nl.


/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:     fit_op.pl
% purpose:  operators for profit
% created:  20.12.92 by GE
% modified: 11.01.94 to avoid conflicts with QP module system
%           17.01.94 for profit
%           05.09.94 added fin_dom
% notes:
% to do:    

:- op(1180,fx,'?').
:- op(900,fy,[load,reload]).
:- op(850,xfx,bool).
:- op(850,xfx,fin_dom).
:- op(700,xfx,':=').     % template definition
:- op(695,xfx,intro).
:- op(690,fx,^^).
:- op(690,fx,^).
:- op(600,xfy,':').      % Quintus module system
:- op(590,xfy,or).     % connective for feature values
:- op(580,xfy,&).      % connective for feature values 
:- op(570,xfy,'!').      % feature 
:- op(560,fx,'>>>').     % find path
:- op(560,xfx,'>>>').    % find path at type
:- op(555,fy,'~').       % atomic negation
:- op(550,fx,'@').       % template
:- op(550,xfx,'@').      % Atom@Booltype
:- op(550,fx,'<').       % type

/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:     tools.pl
% purpose:  some general tools
% created:  1 March 93 by GE
% modified: 21 March 94 

% gensym2(Name,Gensym) 
% called gensym2 to avoid name conflict with gensym from lib. strings
% example: gensym(bla,bla_1), the underscore is added to distinguish
%                             bla_31 from bla3_1 etc.
gensym2(Name,Gensym) :-
	recorded(gensym,'$gensym_counter'(Name,N),Ref), !,
	erase(Ref),
	X is N + 1,
	recorda(gensym,'$gensym_counter'(Name,X),_),
	atom_chars(Name,ASCII),
	number_chars(X,XA),
	append(ASCII,[95|XA],GS),
	atom_chars(Gensym,GS).
gensym2(Name,Gensym) :-
	X is 1,
	recorda(gensym,'$gensym_counter'(Name,X),_),
	atom_chars(Name,ASCII),
	number_chars(X,XA),
	append(ASCII,[95|XA],GS),
	atom_chars(Gensym,GS).

% write_list/1: writing recursively the elements of a list

write_list([X]) :-
        write(X).
write_list([X|T]) :-
        write(X),
        write_list(T).

ebagof(Template,Goal,Bag) :-
	bagof(Template,Goal,Bag),
	!.
ebagof(_,_,[]).

esetof(Template,Goal,Bag) :-
	setof(Template,Goal,Bag),
	!.
esetof(_,_,[]).

fact_listing(Goal) :-
	call(Goal),
	writeq(Goal), write(.), nl,
	fail.
fact_listing(_).

nth_member(1,X,[X|_]).
nth_member(N,X,[_|R]) :-
	nth_member(N1,X,R),
	N is N1+1.

% strict_member(X,L)
% X is a strict member of L if L has an element Y such that X == Y.
strict_member(X,[XX|_]) :- X == XX, !.
strict_member(X,[_|R]) :- nonvar(R), strict_member(X,R).

rev_member(X,[_|R]) :-
	rev_member(X,R).
rev_member(X,[X|_]).

increment_counter(Name,X) :-
	recorded(gen_num,counter(Name,N),Ref), !,
	erase(Ref),
	X is N + 1,
	recorda(gen_num,counter(Name,X),_).
increment_counter(Name,1) :-
	recorda(gen_num,counter(Name,1),_).

% plus(X,Y,Z)
% addition of positive integers
% at least two arguments must be instantiated with a positive integer
plus(X,Y,Z) :-
	integer(X), X >= 0,
	integer(Y), Y >= 0,
	!,
        Z is X + Y.
plus(X,Y,Z) :-
        integer(Y), Y >= 0,
	integer(Z), Z >= 0,
	!,
	X is Z - Y.
plus(X,Y,Z) :-
	integer(X), X >= 0,
	integer(Z), Z >= 0,
	!,
	Y is Z - X.
% plus(_,_,_) :-
%	nl, write('plus/3: instantiation error.'), nl, fail.

% clear_database(Key)
%   erases all entries that are recorded under Key

clear_database(Key) :-
	recorded(Key,_,Ref),
	erase(Ref),
	fail.
clear_database(_).

clear_database(Key,Term) :-
	recorded(Key,Term,Ref),
	erase(Ref),
	fail.
clear_database(_,_).

all(Goal) :- call(Goal), fail.
all(_).

% once(Goal) :- call(Goal), !.

del(X,[X|T],T).
del(X,[H|T],[H|R]) :-
        del(X,T,R).

for(Start,Start,End) :-
     Start =< End.
for(X,Start,End) :-
     Start < End,
     Start1 is Start + 1,
     for(X,Start1,End).

% replace(?Old,?New,?OldList,?NewList)
% to replace each Old element by New in OldList resulting in NewList
replace(_,_,[],[]).
replace(X,Y,[X|T],[Y|T2]):-
    replace(X,Y,T,T2).
replace(X,Y,[H|T],[H|T2]):-
    replace(X,Y,T,T2).
    
% structure_to_list(+Functor,?ListlikeStructure,?List)
% this version is bidirectional
structure_to_list(_,Var,[X]) :-
	var(Var),
	!,
	X = Var.
structure_to_list(Functor,Structure,[First|Rest]) :-
	functor(Structure,Functor,2),
	!,
	arg(1,Structure,First),
        arg(2,Structure,RestStruct),
	structure_to_list(Functor,RestStruct,Rest).
structure_to_list(_,X,[X]).

% like numbervars, but instantiates ONLY variables, not terms like '$VAR'(_)
% [?? above comment does not make sense --matsc]
numbervars_according_to_the_fine_manual(Term,First,Last) :-
    numbervars(Term,First,Last).

% write_message/0
% printing out the ProFIT messages saved in the database 'messages'

write_messages :-
    all((recorded(messages,message(Type,Term,Mes),_),
	 nl,
         (Type = nf
          -> write(Mes),nl
          ; (write_type(Type),
             format(Mes,[]),nl,
	     (\+ Term = '#'
	         ->  format('        here:   ',[]),write(Term),nl))))).







/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:     write_term.pl
% purpose:  writing of ProFIT terms to file
% created:  Nov 93 by GE
% modified: Mar 94 for set constraints
%           Jul 94 changed arity of write_constraint
%           Apr 95 c_terms are only asserted, not written to file


% write_c_term/2
write_c_term(_,term_constraint(Term,Constraint)) :-
	% constraints(on),
	cl1:write_constraint(Constraint,SetDescriptions,Call),
        cl1:term_in_out(Term,TermOut,SetDescriptions),
%	write_prolog_clause(Stream,(TermOut :- Call)).
        call(Call),
%       record(cl1,TermOut,_).
        assertz(cl1:TermOut).
	
	
% write_prolog_clause/2
write_prolog_clause(S,TermIn) :-
        preprocess_term(TermIn,TermOut),
	write_clause(S,TermOut).
preprocess_term(TermIn,TermOut) :-
        cycles(on),
        !,
        copy_term(TermIn,Term1),
        trans_prolog_term(Term1,Term2,Cycles,[]),
        build_clause(Term2,Cycles,TermOut),
        numbervars_according_to_the_fine_manual(TermOut,0,_).

preprocess_term(TermIn,TermOut) :-
        cycles(off),
        copy_term(TermIn,TermOut),
        numbervars_according_to_the_fine_manual(TermOut,0,_).

write_clause(S,(H :- B)) :-
        !,
        writeq(S,H),
        write_body(S,B).
write_clause(S,Fact) :-
        writeq(S,Fact), write(S,'.'), nl(S).

write_body(S,true) :-
        write(S,'.'), nl(S),
        !.
write_body(S,Goals) :-
        write(S,' :-'), nl(S),
        write_goals(S,Goals,5),
        write(S,'.'), nl(S).

write_goals(S,(G,Gs),Tab) :-
        !,
        write_goal(S,G,Tab), write(S,','), nl(S),
        write_goals(S,Gs,Tab).
write_goals(S,G,Tab) :-
        !,
        write_goal(S,G,Tab).

write_goal(S,(X;Y),Tab) :-
        !,
        tab(S,Tab), write(S,'('), nl(S),
        Tab2 is Tab+2,
        write_goals(S,X,Tab2), nl(S),
        tab(S,Tab), write(S,';'), nl(S),
        write_goals(S,Y,Tab2), nl(S),
        tab(S,Tab), write(S,')').
write_goal(S,G,Tab) :-
        tab(S,Tab), writeq(S,G).

build_clause(Term,[],Term) :- !.
build_clause((Head :- Goals),Cycles,(Head :- NewGoals)) :- 
	add_cycles(Cycles,Goals,NewGoals), !.
build_clause((Head --> Goals),Cycles,(Head --> {CycGoals},Goals)) :- 
	add_cycles(Cycles,true,CycGoals), !.
build_clause(Fact,Cycles,(Fact :- Goals)) :-
	add_cycles(Cycles,true,Goals).

add_cycles([Goal],true,Goal) :- !.
add_cycles([Goal],Goals,(Goal,Goals)).
add_cycles([Goal|Goals],G,(Goal,NewGoals)) :-
        add_cycles(Goals,G,NewGoals).

	
/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:     sugar*.pl
% purpose:  syn. sugar for writing of principles, types etc.
% created:  27 Feb 93 by GE
% modified: 09 Apr 93 by GE, to allow feature terms
%           05 Nov 93 by GE, feature terms at arg. positions: tt
%           18 Jan 94 by GE, type checking
%           15 Sep 94 by JCB converting terms with sets to PROFIT terms
%           20 Oct 94 GE, allowed variables for feature and sort names

% provides the following surface syntax for ProFIT terms (FT)
%                  <Type
%                  Attribute!FT
%                  {Elements} (Elements is a list of set elements)
%                  FT &  FT
%                  Type>>>Attribute!FT
%                  >>>Attribute!FT
%                  @Template
%                  <Prolog term>
%                  <Boolean combination of atoms>
%                  ^^ FT
%                  ^ FT
%                  FT or FT

% IMPORTS:
% attval/5 from .sig file
% subtype/3
% search_feature/5
% template/2

% EXPORTS:
% trans_term/2

% trans_term(+GeldTerm,-PrologTerm)
% trans_term is expected to be called in a failure-driven loop, because
%   it returns several solutions
trans_term(Geld,Prolog) :-
	prolog_flag(unknown,Old,fail),
        trans_term(Geld,Prolog,Old).
trans_term(Geld,Prolog,_) :-
	tt(Geld,Prolog,[],_,_).
trans_term(_,_,OldFlag) :-
        prolog_flag(unknown,_,OldFlag),
        fail.

% trans_c_term(ProfitTerm,PrologTerm/ConstraintList)
% ProfitTerm may contain constraints
trans_c_term(Geld,term_constraint(Prolog,Constraints-RestConstraints)) :-
	prolog_flag(unknown,Old,fail),
        trans_c_term(Geld,Prolog,Constraints,RestConstraints,Old).
trans_c_term(Geld,Prolog,Constraints,RestConstraints,_) :-
	tt(Geld,Prolog,[],Constraints,RestConstraints).
trans_c_term(_,_,_,_,OldFlag) :-
        prolog_flag(unknown,_,OldFlag),
        fail.

% tt(ProfitTerm,PrologTerm,ListofTerms) + Difflist for Constraints
% ListofTerms serves to detect cycles
tt(X,Y,_) -->
	{ var(X), !,
	  X = Y
        }.
tt(Constraint,X,_) -->
	{ constraints(on),
	  cl1:constraint_term(Constraint)
        },
	!,
        cl1:trans_constraint(Constraint,X,FitTerm,PrologTerm),
	tt(FitTerm,PrologTerm,_).
tt(X,Y,_) -->
	{ atomic(X), !,
	  X = Y
        }.
tt(^(X),X,_) -->
        !.
tt(^^(X),Y,TermList) -->
        !,                     % but its arguments are translated
        { functor(X,F,A),        
          functor(Y,F,A)
        },
        trans_arguments(A,X,Y,TermList).
tt(FD,X,_) -->
	{ fd(FD), 
          !,
          sort_checking_option(TypChk)
	},
        trans_typed_term(FD,X,top,TypChk).

tt(X,Y,TermList) -->
	{ functor(X,F,A),
	  functor(Y,F,A)
	},
	trans_arguments(A,X,Y,TermList).

trans_arguments(0,_,_,_) --> !.
trans_arguments(N,X,Y,TermList) -->
	{ arg(N,X,AX) },
	(  { strict_member(X,TermList) }
	-> { X=Y }
	;  tt(AX,AY,[X|TermList])
        ),
	{ N1 is N-1 
	},
	trans_arguments(N1,X,Y,TermList),
	{ arg(N,Y,AY) }.
		
fd(_P & _Q).
fd(_P or _Q).
fd(_Att!_FT).
fd(_Sort >>> _Feat!_FT).
fd(>>>_Feat!_F).
fd(< _FT).
fd(_B@_T).
fd(@_T).
fd(~_T).  % for boolean types only

trans_typed_term(X,Y,TypeRestr,TypChk) -->
	{ var(X),
	  !,
          (  TypChk == on
          -> types_term(TypeRestr,Y,Constraints) 
	  ;  true
          ),
	  X = Y
	},
	Constraints.

trans_typed_term(X,X,TypeRestr,TypChk) -->   % nonvar(X)
	{ \+ \+ (subtype(_,_,X)),    % in case X is part of a coreference
          !,                         % and already instantiated
	  opt_types_term(TypChk,TypeRestr,X,Constraints)
	},
	Constraints.
trans_typed_term(X,X,TypeRestr,TypChk) -->   % nonvar(X)
	{ \+ \+ (btype(_,_,X)),    % in case X is part of a coreference
          !,                         % and already instantiated
	  opt_types_term(TypChk,TypeRestr,X,Constraints)
	},
	Constraints.
trans_typed_term(Term,Trans,TypeRestr,TypChk) -->
        { ( TypChk = off
          ; TypeRestr == top
          ; btype(TypeRestr,_,Trans)
          ; cl1:constraint_term(Term)
          ),
          bool_type(Term,BoolTerm,Type),
          !,
          eval_b_type(BoolTerm,Trans,Type)
        }.
trans_typed_term((FT1 & FT2),X,Type,TypChk) -->
	!,
	trans_typed_term(FT1,X,Type,TypChk),
	trans_typed_term(FT2,X,Type,TypChk).
trans_typed_term(or(FT1,FT2),X,Type,TypChk) -->
	!,
	( trans_typed_term(FT1,X,Type,TypChk)
	; trans_typed_term(FT2,X,Type,TypChk) 
        ).

trans_typed_term(Attribute!FT,X,TypeRestr,TypChk) -->
	{ (atom(Attribute); var(Attribute)),
          !,
	  error_proc(def_attr,Attribute),
	  opt_types_term(TypChk,TypeRestr,X,Constraints),
	  attval(Attribute,_,X,Val,AttType)
	},
	Constraints,
	trans_typed_term(FT,Val,AttType,TypChk).
trans_typed_term(Type>>>Attribute!_FT,X,TypeRestr,TypChk) -->
	{ opt_types_term(TypChk,TypeRestr,X,_Constraints),
          subtype(Type,_,X),
	  (\+ search_feature(X,_,Attribute,_Y,_ValType)
	  ->  error_msg(wrong_searchpath(Type>>>Attribute))
          ),
          !,
          fail
	}.
trans_typed_term(Type>>>Attribute!FT,X,TypeRestr,TypChk) -->
	{ !,
	  opt_types_term(TypChk,TypeRestr,X,Constraints),
          subtype(Type,_,X),
	  search_feature(X,_,Attribute,Y,ValType)
	},
	Constraints,
	trans_typed_term(FT,Y,ValType,TypChk).
trans_typed_term(>>>Attribute!_FT,X,TypeRestr,_TypChk) -->
	% type checking needed in this case!
        { types_term(TypeRestr,X,_Constraints),
	  (\+ search_feature(X,_,Attribute,_Y,_ValType) 
	  -> error_msg(wrong_searchpath(>>>Attribute))
           ),
           !
        }.
trans_typed_term(>>>Attribute!FT,X,TypeRestr,TypChk) -->
	{ !,                       % type checking needed in this case!
          types_term(TypeRestr,X,Constraints),
	  search_feature(X,_,Attribute,Y,ValType)
	},
	Constraints,
	trans_typed_term(FT,Y,ValType,TypChk).

trans_typed_term(<Typ,X,TypeRestr,TypChk) -->
        !,
        {error_proc(undefined_sort,Typ),
	 opt_types_term(TypChk,TypeRestr,X,Constraints),
          subtype(Typ,_,X)
	},
	Constraints.
trans_typed_term(@Tpl,X,TypeRestr,TypChk) -->
	!,
	trans_name(Tpl,Tpl1),
        get_template(Tpl1,Expansion),
%	{ Expansion = X },
        trans_typed_term(Expansion,X,TypeRestr,TypChk).
trans_typed_term(Term,X,TypeRestr,TypChk) -->  
        { ( TypeRestr == term   
	  ; TypeRestr == top
	  ; TypeRestr == lp_set
	  ; TypeRestr == set
          ; TypChk == off
          ),
          \+ Term = (~_),
          \+ Term = _@_,
          !
	},
        tt(Term,X,[]).

opt_types_term(off,_,_,[]).
opt_types_term(on,Types,Term,List) :-
	types_term(Types,Term,List).

% types_term(+TypeRestriction,-Term)
% translates a possibly conjunctive type restriction to the corresponding
%   prolog term
types_term(Type&Types,Term,List) :-
	!,
	subtype(Type,_,Term),
	types_term(Types,Term,List).
types_term(top,_,[]) :- 
	!.
types_term(set,'$$set'(Var),[Var-CTerm]) :-
        !,
	cl1:set_term(CTerm, SetTerm),
        cl1:set_sort(SetTerm,set),
        cl1:set_list(SetTerm,_).
types_term(lp_set,'$$set'(Var),[Var-CTerm]) :-
        !,
        cl1:set_term(CTerm, SetTerm),
        cl1:set_sort(SetTerm,lp_set),
        cl1:set_list(SetTerm,_).

types_term(Type,Term,[]) :-
	subtype(Type,_,Term).
types_term(Type,Term,[]) :-
	btype(Type,_,Term).







/*
get_template(Name,Term) -->     % for expansion at compile time
      { \+ \+ recorded(tpl,template(Name,_),_),   % if there is a matching
                                                  % template definition in 
                                                  % the recorded database,
                                                  % then don't try clause 2
	!,
	recorded(tpl,template(Name,Expansion),_)
      },
      tt(Expansion,Term,[]).
*/

get_template(Name,Term) -->     % for expansion at compile time
      { functor(Name,Functor,Arity),              % Construct a term with same functor
        functor(Name2,Functor,Arity),             % and arguments to match against the
                                                  % template database
        \+ \+ recorded(tpl,template(Name2,_),_),  % If there is a matching
                                                  % template definition in 
                                                  % the recorded database,
                                                  % then don't try clause 2
	!,
	recorded(tpl,template(Name2,Expansion),_)
      },
      trans_name(Name2,Name),                     % Translate name looked up from
                                                  % template database from ProFIT
                                                  % term into Prolog term
      tt(Expansion,Term,[]).

get_template(Name,Term) -->     % for expansion at runtime
	(  { constraints(on) }
        -> template(Name,Term)
        ;  { template(Name,Term) }
        ).

% untrans_term(+PrologTerm,-FitTerm)
untrans_term(Prolog,Fit) :-
	untrans_term(Prolog,[],Fit).

% untrans_term(+PrologTerm,+SetDescriptions,-FitTerm)
% converts a Prolog Term to a ProFIT Term
% a list of set descriptions is passed on to ensure that the
% Variables which correspond to the set are present in the ProFIT term.
% The set descriptions do not show up in the ProFIT term
untrans_term(Prolog,Sets,Fit) :-
        prolog_flag(unknown,Old,fail),
	trans_prolog_term(Prolog,NonCyclic,Cycles,[]),
	term_list(Cycles,TermList,Cycs),
	find_coreferent_variables(NonCyclic/TermList,CoreferentVars),
	untrans_term(NonCyclic,Fit,1,CoreferentVars,Cycs,Sets),
        prolog_flag(unknown,_,Old).

untrans_cycle(Var,Cycles,Coref,Var&FitTerm,Sets) :-
	member(cyc(Var,Cycle,Mark),Cycles),
	var(Mark), Mark = done,
	!,
	untrans_term(Cycle,FitTerm,1,Coref,Cycles,Sets).
untrans_cycle(Var,_,_,Var,_).

untrans_term(T,FitTerm,_Counter,Coref,Cycles,Sets) :-
        T = '$VAR'(_),       % var(T)
        untrans_cycle(T,Cycles,Coref,FitTerm,Sets),
        !.
	
untrans_term(T,FitTerm,Counter,Coref,Cycles,Sets) :-
	T = '$$set'(T2),       % var(T)
	T2 = '$VAR'(_),
        (member(T2-cterm(_,[set(_,_,Element_List)|_]),Sets) ->
            untrans_set(Element_List,ZwErg,Counter,Coref,Cycles,Sets),
            FitTerm = {}(ZwErg)
        ),
        !.

untrans_term(Term,FitTerm,Counter,Coref,Cycles,Sets) :-
	subtype(_,_,Term),
	!,
	untrans_typed_term(Term,FitTerm,Counter,Coref,Cycles,Sets).
untrans_term(Term,FitTerm,_,_,_,_) :-
	btype(Type,_,Term),
	!,
        (  give_boolean_type(Term,BoolExpr)
	-> FitTerm = BoolExpr@Type
	;  FitTerm = <Type
        ).
untrans_term(Term,FitTerm,Counter,Coref,Cycles,Sets) :-
        functor(Term,F,A),
        functor(Untrans,F,A),
        untrans_arguments(A,Term,Untrans,Counter,Coref,Cycles,Sets),
        (  fd(Term)
	-> FitTerm = ^^(Untrans)
	;  FitTerm = Untrans
        ).

untrans_set('$VAR'(X),.('...','$VAR'(X)),_,_,_,_).
untrans_set([],'{}',_,_,_,_).
untrans_set([X|Rest],.(Fit,[]),Counter,Coref,Cycles,Sets) :-
        Rest == [],
	!,
        untrans_term(X,Fit,Counter,Coref,Cycles,Sets).
untrans_set([Head|Tail],.(Fit,ZwErg),Counter,Coref,Cycles,Sets) :-
        untrans_term(Head,Fit,Counter,Coref,Cycles,Sets),
        untrans_set(Tail,ZwErg,Counter,Coref,Cycles,Sets).

untrans_arguments(0,_,_,_,_,_,_) :- !.
untrans_arguments(N,X,Y,Counter,Coref,Cycles,Sets) :-
        arg(N,X,AX),
        arg(N,Y,AY),
        untrans_term(AX,AY,Counter,Coref,Cycles,Sets),
        N1 is N-1,
        untrans_arguments(N1,X,Y,Counter,Coref,Cycles,Sets).

untrans_typed_term(Term,FitTerm,Counter0,Coref,Cycles,Sets) :-
        extract_variable(Term,Coref,Var,Counter,Flag),
        (  Flag == done
        -> FitTerm = Var
        ;  (  Counter =< Counter0     % Counter == 1
           -> TermList = Bag 
           ;  Counter > Counter0,
              TermList = [Var|Bag],
              Flag = done
           ),
           bagof(<Type,find_most_specific_subtype(Term,Type),TypeBag),
           find_attributes(Term,Atts),
           trans_attributes(Term,Counter,Atts,[],AttBag,Coref,Cycles,Sets),
           append(TypeBag,AttBag,Bag),
           list_to_conj(TermList,FitTerm)
        ).

trans_attributes(_,_,[],Atts,Atts,_,_,_).
trans_attributes(Term,Counter,[Att|Atts],Acc,ATTS,Coref,Cycles,Sets) :-
	attval(Att,_,Term,AttVal,_),
	trans_attribute(AttVal,Counter,Att,Acc,Acc2,Coref,Cycles,Sets),
	!,  
	trans_attributes(Term,Counter,Atts,Acc2,ATTS,Coref,Cycles,Sets).

% trans_attribute(AttVal,Num,Att,Acc,Atts,CorefIn)
trans_attribute(AttVal,Num,Att,Acc,Atts,Coref,Cycles,Sets) :-
	AttVal = '$VAR'(_),
	!,
	extract_variable(AttVal,Coref,AttVal,Counter,_Flag),
	(  ( Counter > Num
	   ; member(cyc(AttVal,_,_),Cycles)
           ; member(AttVal-_SetDesc,Sets)
	   )
	-> untrans_term(AttVal,UT,Counter,Coref,Cycles,Sets),
	   Atts = [(Att!UT)|Acc]
	;  Atts = Acc
	).
trans_attribute(AttVal,Counter,Att,Acc,[(Att!UT)|Acc],Coref,Cycles,Sets) :-
	untrans_term(AttVal,UT,Counter,Coref,Cycles,Sets).

find_attributes(Term,Atts) :-
	ebagof(Att,A^B^C^attval(Att,A,Term,B,C),Atts).

find_coreferent_variables(Term,CoreferentVars) :-
	numbervars(Term,0,_),
	(  bagof(Var,coreferent_variable(Term,Var),CoreferentVars)
	-> true
	;  CoreferentVars = []
        ).
coreferent_variable(Term,var(Var,Length,_)) :-
	bagof(Sub,(Sub = '$VAR'(_), subterm(Term,Sub)),Vars),
	Vars = [Var|_],
	length(Vars,Length),
	Length > 1.

extract_variable(Term,Coref,Var,Counter,Flag) :-
        Var = '$VAR'(_),
	relevant_subterm(Term,Var),
        member(var(Var,Counter,Flag),Coref),
	!.
extract_variable(_,_,_,1,_).

% subterm(Subterm,Term)
subterm(X,X).
subterm(T,X) :-
	nonvar(T),
	functor(T,_,N),
	for(I,1,N),
	arg(I,T,Arg),
	subterm(Arg,X).

% relevant_subterm(+FitTerm,Subterm)
% finds a subterm that can be used to establish coreferences
% in case of an intensional type, it is the first arg., for extensional
% types, all variables occuring in the subtype arguments can occur.
relevant_subterm('$VAR'(X),'$VAR'(X)) :- !.
relevant_subterm(Term,Sub) :-
	coref_pos(Term,Pos),
	for(I,1,Pos),
	arg(I,Term,Arg),
	subterm(Arg,Sub),
	\+ \+ Sub = '$VAR'(_).  % either a variable or '$VAR'(N)

term_list([Var=Term|Cycles],[Term|TermList],[cyc(Var,Term,_Mark)|Cycs]) :-
        term_list(Cycles,TermList,Cycs).
term_list([],[],[]).

% this assumes that the Term has been numbervar'ed
find_most_specific_subtype(Term,Type) :-
	subtype(Type,_,Term),
	\+ ( subtype(_Sub,TypeSet,Term),
             and_member(Type,TypeSet)
	   ).	

and_member(A,A&_).
and_member(X,_&B) :-
        !,
        and_member(X,B).
and_member(X,X).

% list_to_conj(+List,-Conjunction)
list_to_conj([A|B],A&B_Conj) :-
	list_to_conj(B,B_Conj).
list_to_conj([A],A).

/***********************************************************************/

compile_search_feature(Stream) :-
	bagof(T-V-T2,search_feat(T,Type,Feature,V,T2),[X-Value-ValType]),
	write_clause(Stream,
                            search_feature(X,Type,Feature,Value,ValType)),
	fail.
compile_search_feature(_).

search_feat(X,Type,Feature,Val,ValType) :-
	search_feat(X,Type,Feature,Val,ValType,[],[Type]).

search_feat(X,Type,Feature,Val,ValType,_,_) :-
	recorded(sig,attval(Feature,Type,X,Val,ValType),_).

search_feat(X,Type,Feat,Val,ValType,PAcc,TAcc) :-
    recorded(sig,attval(AnyFeat,Type,X,FeatVal,ResType),_),
    nonmember(AnyFeat,PAcc),   % don't go through the same feature twice
    nonmember(ResType,TAcc),   % don't go through the same type twice
    search_feat(FeatVal,ResType,Feat,Val,ValType,[AnyFeat|PAcc],[ResType|TAcc]).

sort_checking(New) :-          % to do: error msg if New is illegal
         ( New == off
         ; New == on
         ),
 	(  recorded(fit,sort_checking(_Old),Ref)
         -> erase(Ref)
         ;  true
 	),
         recorda(fit,sort_checking(New),_).
cl1_mode(New) :-          % to do: error msg if New is illegal
         ( New == off
         ; New == on
         ),
 	(  recorded(fit,cl1_mode(_Old),Ref)
         -> erase(Ref)
         ;  true
 	),
         recorda(fit,cl1_mode(New),_).
occur_check(New) :-          % to do: error msg if New is illegal
         ( New == off
         ; New == on
         ),
 	(  recorded(fit,occur_check(_Old),Ref)
         -> erase(Ref)
         ;  true
 	),
         recorda(fit,occur_check(New),_).

constraints(X) :- recorded(fit,cl1_mode(X),_).
cycles(X) :- recorded(fit,occur_check(X),_).

sort_checking_option(Option) :-
	recorded(fit,sort_checking(Option),_),
        !.

trans_test :-
	repeat,
	nl, write('Enter a term: '), read(Term),
	( Term == x
	; trans_term(Term,PTerm), 
	  write('Prolog Term: '), write(PTerm), nl,
	  prolog_flag(unknown,_,error),
	  untrans_term(PTerm,Untrans), 
	  write('Fit Term:    '), write(Untrans), nl,
          fail
        ).


/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
:- multifile(record_term/1).
% file:     load.pl
% purpose:  load signature, plp, and relations
% created:  11 Apr 93 by GE
% modified: 05 Nov 93 read files instead of consulting
%           18 Mar 94 added file translation without consulting           
%           05 Sep 94 changed syntax for finite domains
% to do:    
%          
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% HOW TO ADD NEW SYNTAX                                                     %
% - add a clause to record_term to put the new syntax into the database DB  %
% - add a clear_database(DB) call to load/1                                 %
% - add a call to the appropriate compiler to load/1, and change variables  %
%   for the filelist that is passed between different compilers             % 
% - create the appropriate compiler for the new syntax                      %
% - if needed, modify trans_term to accept terms with new surface syntax    %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% IMPORTS:
% clear_database/1 from tools.pl

% EXPORTS
% load_profit/1  loads a file or a list of files, and translates

% load_profit(Files)
% loads the File or Files given as a list
% creates the files X.sig (signature)
%                   X.boo (boolean types)
%                   X.tpl (templates)
%                   X.pl  (Prolog clauses)
%                   X.mas  (master file)

/* commented out
fit(List_of_files) :-
        List_of_files = [_|_],
        member(File,List_of_files),
        atom_concat('******************  ','Messages while compiling ',M1),
        atom_concat(M1,File,M2),
        atom_concat(M2,'  *************************',M3),
        recordz(messages,message(nf,_,M3),_),
        compile_profit(File),
        fail.
*/
fit(File) :-
	load_profit(File,PlFile),
	no_style_check(single_var),
	(  PlFile == '$$nil'	% there is no .pl file
	-> true
	;  compile(user:PlFile)
        ),
	style_check(single_var).

load_profit(FileName,PlFile) :-
	clear_database(messages),
        is_filename_or_list(FileName),
        clear_database(sig),
        clear_database(bool),
        clear_database(tpl),
	clear_database(pl),
	clear_database(rel),
        recorda(sig,sort_list([top]),_),
	load_fit_files(FileName,FitFile),
        (  atom_concat(File,'.fit',FitFile)
        -> true
        ;  File = FitFile
        ),
	compile_sig_file(File,[],F1),
        compile_boo_file(File,F1,F2),
        compile_tpl_file(File,F2,FileList),
	compile_plp_file(File,PlFile),
	compile_master_file(File,FileList,PlFile),
        write_messages.

reload(Filename) :-
        is_filename(Filename),
        Filename = library(File),
        !,
        reload_library_file(File).

reload(FileSpec) :-
	atom_concat(FileSpec, '.mas', MasFileSpec),
	atom_concat(FileSpec, '.fit.mas', MasFitFileSpec),
        (  file_exists(MasFitFileSpec) ->
           compile(MasFitFileSpec)
        ;  file_exists(MasFileSpec) ->
           compile(MasFileSpec)
        ).

reload_library_file(File) :-
        user:library_directory(Path),
	atom_concat(Path, /, PathSlash),
	atom_concat(PathSlash, File, PathSlashFileSpec),
	atom_concat(PathSlashFileSpec, '.mas', MasFileSpec),
	atom_concat(PathSlashFileSpec, '.fit.mas', MasFitFileSpec),
        (  file_exists(MasFitFileSpec) ->
           compile(MasFitFileSpec)
        ;  file_exists(MasFileSpec) ->
           compile(MasFileSpec)
        ),
	!.

% load_fit_file(File,Filename)
% arguments: Files: a file to be loaded
%            Filename: the filename to which the result of the
%                      compilation is written (w/ extensions: .sig, .plp, .rel)

% clause1: non-empty list of files
load_fit_files([File|Files],FileName) :-
	!,
	load_fit_file(File,FileName),
	load_fit_files(Files,_).
% clause2: empty list of files
load_fit_files([],_) :- 
	!.
% clause3: simple filename
load_fit_files(File,FileName) :-
	load_fit_file(File,FileName).

load_fit_file(File, FileName) :-
        ( find_file(File, FileName) ->
          open(FileName,read,Stream),
          read_fit_file(Stream)
        ; error_msg(file_not_exist(File)),fail
        ).

find_file(library(File), FileName) :-
        !,
        find_library_file(File, FileName).

find_file(FileSpec, FileName) :-
	atom_concat(FileSpec,'.fit',FitFileSpec),
        (  file_exists(FitFileSpec) ->
           FileName = FitFileSpec
        ;  file_exists(FileSpec) ->
              FileName = FileSpec
        ).

find_library_file(File, FileName) :-
        user:library_directory(Path),
	atom_concat(Path,'/',Path2),
	atom_concat(Path2,File,FileSpec),
	atom_concat(FileSpec,'.fit',FitFileSpec),
        (  file_exists(FitFileSpec) ->
           FileName = FitFileSpec
        ;  file_exists(FileSpec) ->
                FileName = FileSpec
        ),
        !. % first solution only


read_fit_file(Stream) :-
        read(Stream,Term),
	process_term(Term,Stream).

process_term(end_of_file,Stream) :-
	!,
	close(Stream),
	\+ recorded(sig,error_flag(yes),_).
process_term(Term,Stream) :-
	record_term(Term),      % if a special treatment for the term type
                                % has been defined in any file
	!,
	read_fit_file(Stream).
process_term(Fact,Stream) :-            % catch-all: Prolog fact
	recordz(pl,clause(Fact),_),     % record as Prolog fact
	!,
        read_fit_file(Stream).

record_term((:-(Goal))) :-
	process_directive(Goal),
	!.
record_term((?-(Goal))) :-
	process_directive(Goal),
	!.
record_term(>(A,B)) :-                  % A > B
        !,
        (A \== top
        ->  ( recorded(sig,sort_list(Liste),_),
              recorda(sig,sort_list([A|Liste]),_)
            )
        ;   true),
	(syntax_check(>(A,B)) ->     
        	recordz(sig,sub(A,B),_)
	  ;     true).
record_term(intro(A,B)) :-              % A intro B
	!,
	recorded(sig,sort_list(Liste),_),
        recorda(sig,sort_list([A|Liste]),_),
	(syntax_check(intro(A,B)) ->
	      recordz(sig,sub(A,intro([],B)),_)
	  ;   true).
% record_term(bool(A,B)) :-               % old name for finite domains
% 	!,
% 	(syntax_check(bool(A,B)) ->
% 		product_to_list(B,BList),
% 	  	recordz(bool,bool(A,BList),_)
% 	  ;     true).
record_term(fin_dom(A,B)) :-            % finite domains
	!,
	(syntax_check(fin_dom(A,B)) ->
              product_to_list(B,BList),
	      recordz(bool,bool(A,BList),_)
	  ;   true).
record_term((A := B)) :-		% template
        !,
        recordz(tpl,template(A,B),_).

record_term((H :- B)) :-		% prolog rule
	recordz(pl,clause((H :- B)),_),
	!.

record_term(hidden_features(List)) :-   % hidden features
        !,
	(syntax_check(hidden_features(List)) ->
        	process_hidden_features(List)
	  ;     true).

process_directive(feature_search(X)) :-
	!,
        recorda(sig,feature_search(X),_).
process_directive(constraints(X)) :-
	!,
	recorda(sig,constraints(X),_).
process_directive(cycles(X)) :-
	!,
	recorda(sig,cycles(X),_).
process_directive(sort_checking(Option)) :-
        ( Option == off
	; Option == on
        ),
        !,
	recorda(sig,sort_checking(Option),_).
process_directive(multifile(PredSpec)) :-
        ( (PredSpec == '>'/2,  DB = sig)
	; (PredSpec == ':='/2, DB = tpl)
	; (PredSpec == bool/2, DB = bool)
	; (PredSpec == fin_dom/2, DB = bool)
	),
	!,
	recorda(DB,multifile(PredSpec),_).
process_directive(Goal) :- 
        (  Goal = op(_,_,_)
        -> call(Goal)
        ;  true
        ),
	recordz(pl,clause((:- Goal)),_).

process_hidden_features([]).
process_hidden_features([A|Rest]) :-
        recordz(fit,hidden_feature(A),_),
        process_hidden_features(Rest).

is_filename(FileName) :-
        atom(FileName),
        !.
is_filename(FileName) :-
        functor(FileName, library, 1),
        arg(1, FileName, LibFileName),
        atom(LibFileName),
        !.

is_filename_or_list(Filename) :- is_filename(Filename), !.
is_filename_or_list([Filename|List]) :-
        is_filename(Filename),
        !,
        is_filename_or_list(List).
is_filename_or_list(EList) :-
        nonvar(EList),
        EList == [],
        !.
is_filename_or_list(_) :-
    error_msg(impossible_filename(#)),
    error_msg(comp_abort(#)),
    fail.


compile_master_file(File,Files,PlFile) :-
	atom_concat(File,'.mas',FileName),
	open(FileName,write,Stream),
	write_clause(Stream,(:- no_style_check(single_var))),
	reverse(Files,RevFiles),
	all((member(FileX,RevFiles),
	     write_clause(Stream,(:- compile(FileX)))
           )),
	(  PlFile == '$$nil'
	-> true
	;  write_clause(Stream,(:- compile(user:PlFile)))
        ),
	write_clause(Stream,(:- style_check(single_var))),
	close(Stream).

product_to_list(X,[B|AList]) :-
        nonvar(X),
        X = A*B,
        !,
        product_to_list(A,AList).
product_to_list(A,[A]).


/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:       mellish2.pl
% purpose:    boolean values a la Mellish
% created:    by Gertjan van Noord
% modified:   12 Jan 94 by GE for integration with ProFIT
% to do:	
% notes:	

% IMPORTS

% EXPORTS
% eval_b_types/3
% give_boolean_type/2

% syntax: Path => val
%                 (val & val)
%                 ~val
%                 ( val  or  val )
%
eval_b_type(Exp,Sign,Type) :-
	var(Exp),
	!,
        btype(Type,_,Sign).

eval_b_type(Exp,Sign,Type):-
%	bool_type(Exp,Type),
        !, %unique
	btype(Type,List,Sign),
	dnf(Type,Exp,Exp2),
	disj_to_list(Exp2,[],Exp3),
	eval_expr(Exp3,List,Sign,1,2).

% bool_type
% checks whether an expression should be translated as boolean type
% atoms are only translated in the form X@Type to allow use of the same
%   atom elsewhere, where Type == bool or Type == a defined boolean type
% All other boolean expressions are translated if they are well-formed,
%   but bool_type does not catch any inconsistencies
% bool_type(X&(@T),X,Type) :-
%         !,
% 	atom(T),
%         ( btype(T,_,_) 
%         ; T == bool
%         ),
%         boolean_type(X,Type).
% bool_type(@T&X,X,Type) :-
% 	!,
% 	atom(T),
%         ( btype(T,_,_) 
%         ; T == bool
%         ),
%         boolean_type(X,Type).
bool_type(X&Y,X&Y,Type) :-
        boolean_type(X&Y,Type).
bool_type(~X,~X,Type) :-         
        (boolean_type(X,Type) ->
	     true
	 ;   error_msg(wrong_bool(~X)),!,fail).
bool_type(X or Y,X or Y,Type) :-
        boolean_type(X or Y,Type).
bool_type(X@T,X,Type) :-
        atomic(X),
        atom(T),
        (boolean_atom(X,Type) ->
	     true
	 ;   error_msg(wrong_bool_atom(X@T)),!,fail),
        ((T == bool ; T == Type) ->
	     true
	 ;   error_msg(wrong_bool_type(X@T)),!,fail).
bool_type(X,X,Type) :-
        atomic(X),
        atom(Type),
        boolean_atom(X,Type).

boolean_type(X&Y,Type) :-
        nonvar(X),
        boolean_type(X,Type),
        nonvar(Y),
        boolean_type(Y,Type).
boolean_type(X or Y,Type) :-
        nonvar(X),
        boolean_type(X,Type),
        nonvar(Y),
        boolean_type(Y,Type).
boolean_type(~X,Type) :-
        nonvar(X),
        boolean_type(X,Type).
boolean_type(Atom,Type) :-
        boolean_atom(Atom,Type).

eval_expr(_,[],_,_,_).
eval_expr(Exp,[H|T],Sign,_,I2):-
	possible(Exp,H),!,
	I3 is I2 + 1,
	eval_expr(Exp,T,Sign,I2,I3).
eval_expr(Exp,[_|T],Sign,I,I2):-
	arg(I,Sign,X),
	arg(I2,Sign,X),
	I3 is I2 + 1,
	eval_expr(Exp,T,Sign,I2,I3).

possible(Disj,Pos):-
	member(Pos1,Disj),
	dela(Pos1,Pos),!.

% dela = del-all
dela([],_).            
dela([H|T],X):-
	del(H,X,X2),
	dela(T,X2).

dnf(Type,Exp0,Exp):-
	bool(Type,Sets),
	remove_negs(Exp0,Exp1,Sets),
	conj_down(Exp1,Exp).

% atomic, conj, disj, neg
remove_negs(Atom,Atom,_):-
	atomic(Atom),!.
remove_negs(~ (A or B),X&Y,Sets):-!,
	remove_negs(~A,X,Sets),
	remove_negs(~B,Y,Sets).
remove_negs(~(A&B),(X or Y),Sets):-!,
	remove_negs(~A,X,Sets),
	remove_negs(~B,Y,Sets).
remove_negs(~(~A),X,Sets):-!,
	remove_negs(A,X,Sets).
remove_negs(~A,R,Sets):-!,
	atomic(A),!,
	member(J,Sets),
	del(A,J,Rest),
	disjun(Rest,R).
remove_negs(A&B,X&Y,Sets):-!,
	remove_negs(A,X,Sets),
	remove_negs(B,Y,Sets).
remove_negs((A or B),(X or Y),Sets):-!,
	remove_negs(A,X,Sets),
	remove_negs(B,Y,Sets).

conj_down(A,B):-
	find_a_pattern(A,A2),!,
	conj_down(A2,B).

conj_down(A,B):-	
	conjuncts_as_list(A,B).

conjuncts_as_list((A or B),(A2 or B2)):-
	!,
	conjuncts_as_list(A,A2),
	conjuncts_as_list(B,B2).

conjuncts_as_list(A,B):-
	cal(A,B,[]).

cal(A,[A|In],In):-
	atomic(A).
cal(A&B,In,Out):-
	cal(A,In,I2),
	cal(B,I2,Out).

find_a_pattern(A&(B or C),(A&B or A&C)).
find_a_pattern((B or C)&A,(A&B or A&C)).
find_a_pattern(A&B,C&B):-
	find_a_pattern(A,C).
find_a_pattern(A&B,A&C):-
	find_a_pattern(B,C).
find_a_pattern((A or B),(A or C)):-
	find_a_pattern(B,C).
find_a_pattern((A or B),(C or B)):-
	find_a_pattern(A,C).

disjun([R],R).
disjun([H|T],(H or R)):-
	disjun(T,R).

disj_to_list((A or B),In,Out):-
	!,
	disj_to_list(A,In,In2),
	disj_to_list(B,In2,Out).

disj_to_list(A,In,[A|In]).

give_boolean_type(Obj,Exp2):-
	btype(Type,List,Obj),
	compall(List,Obj,fail,Exp,1,2),
	rewrite_disj(Type,Exp,Exp2).

compall([],_,E,E,_,_).
compall([_|T],Obj,In,Out,I1,I2):-
	arg(I1,Obj,X),
	arg(I2,Obj,Y),
	X==Y,!,
	I3 is I2 + 1,
	compall(T,Obj,In,Out,I2,I3).
compall([H|T],Obj,fail,Out,_I1,I2):-!,
	I3 is I2 + 1,
	compall(T,Obj,[H],Out,I2,I3).
compall([H|T],Obj,In,Out,_I1,I2):-
	I3 is I2 + 1,
	compall(T,Obj,[H|In],Out,I2,I3).

conj([H],H).
conj([H|T],H&R):-
	conj(T,R).

rewrite_disj(Type,P0,P):-
	bool(Type,Set),  
	remove_unspecified_values(Set,P0,P1),
	write_as_disj(P1,P).

remove_doubles(X,Y):-
	del(V,X,X2),
	member(V,X2),!,
	remove_doubles(X2,Y).
remove_doubles(X,X).

%% 
%% if for some value each possibility is multiplied because
%% it is simply not known

% [[a,b,c],[x,y]]
% instead a&x  or b&x  or c&x yields x
remove_unspecified_values(Tuples,I,Out):-
	del(F,I,In),
	find_candidate(Tuples,F,In,In2),!,
	remove_unspecified_values(Tuples,In2,Out).
remove_unspecified_values(_Tuples,I,I).

find_candidate(Tuples,F,In,[F2|Out]):-
	del(L,F,F2),
	find_tuple(L,Tuples,Others),
	remove_others(F,L,Others,In,Out).

find_tuple(L,Tuples,Others):-
	member(Tuple,Tuples),
	del(L,Tuple,Others).

remove_others(_,_,[],In,In).
remove_others(F,L,[H|T],In,Out):-
	replace(L,H,F,L2),!,
	del(L2,In,In2),
	remove_others(F,L,T,In2,Out).

write_as_disj([H],H2):-
	write_as_conj(H,H2).
write_as_disj([H|T],(H2 or T2)):-
	write_as_conj(H,H2),
	write_as_disj(T,T2).

write_as_conj([H],H).
write_as_conj([H|T],H&T2):-
	write_as_conj(T,T2).



/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:      compile_sig.pl
% purpose:   compiles subtype and approp. specification to Prolog terms
% created:   March 93, by GE
% modified:  10 Apr 93 by GE / accepts ALE signature specifications (almost)!
%            23 Jan 94, extensional and intensional types
%            17 Mar 94, feature search can be turned off
% to do:     
% notes:     A .sig file is always created because it contains the directives

% EXPORTS (in .sig file)
% attval(Attribute,SuperType,SuperTerm,FeatureVal,FeatureValType)
% subtype(SubType,SuperType,Term)

compile_sig_file(File,Files,[FileName|Files]) :-
	error_proc(double_sort_declaration),
	error_proc(sort_cycle),
	\+ recorded(sig,error_flag(yes),_),
	atom_concat(File,'.sig',FileName),
	compile_sig,
	open(FileName,write,Stream),
	write_sig(Stream),
	(  recorded(sig,feature_search(off),_)
        -> write_clause(Stream,feature_search(off))
        ;  compile_search_feature(Stream)
        ),
	close(Stream),
	no_style_check(single_var),
	error_proc(lonely_sort),
	error_proc(undefined_sortal_restriction),
	compile(FileName),!.

compile_sig_file(_,_,_) :-
        error_msg(comp_abort(#)),
	fail.

write_sig(S) :-
	recorded(sig,multifile('>'/2),_),
	( PredSpec = attval/5
	; PredSpec = subtype/3
	; PredSpec = search_feature/5
	; PredSpec = coref_pos/2
	),
	write_clause(S,(:- multifile(PredSpec))),
	fail.
write_sig(S) :-
	(  recorded(sig,sort_checking(off),_)
        -> write_clause(S,(:- sort_checking(off)))
        ;  write_clause(S,(:- sort_checking(on)))
        ),
        fail.
write_sig(S) :-
        (  recorded(sig,constraints(on),_)
        -> write_clause(S,(:- cl1_mode(on)))
        ;  write_clause(S,(:- cl1_mode(off)))
        ),
        fail.
write_sig(S) :-
	(  recorded(sig,cycles(off),_)
        -> write_clause(S,(:- occur_check(off)))
        ;  write_clause(S,(:- occur_check(on)))
        ),
        fail.
write_sig(S) :-
	( Term = attval(_,_,_,_,_) 
        ; Term = subtype(_,_,_) 
	; Term = coref_pos(_,_)
        ),
	recorded(sig,Term,_Ref),
	write_clause(S,Term),
	fail.
write_sig(_).

compile_sig :-
	clear_database(sig,attval(_,_,_,_,_)),
	clear_database(sig,subtype(_,_,_)),
	is_top(SUPER,Extensional),		% immediate subtype of TOP
	sub_intro(SUPER,SUB,FEAT),
	length(SUB,SUB_Length),
	length(FEAT,FEAT_Length),
	Length is Extensional + SUB_Length + FEAT_Length,
	atom_concat('$',SUPER,Super),
	functor(Term,Super,Length),
	recorda(sig,subtype(SUPER,top,Term),_),
	CorefPos is SUB_Length-(SUB_Length*Extensional)+Extensional,
	recorda(sig,coref_pos(Term,CorefPos),_),
	compile_features(Term,Term,SUPER,FEAT,Extensional+SUB_Length),
	compile_subtypes(Term,Term,SUPER,SUPER,SUB,Extensional),
	fail.
compile_sig.


% compile_features(SuperTerm,SubTerm,Supertype,Features,Counter)
compile_features(SuperTerm,SubTerm,SuperType,[Feat:Approp|Feats],N) :-
	Pos is N + 1,
	( arg(Pos,SubTerm,FV)
	; true                  % needed in case multiple occurences of
                                % type with multiple inheritance are replaced
                                % by atoms
	),
	!,
% the following if-then-else merges the various attval facts that arise
%       in case of multiple inheritance into one
        ( recorded(sig,attval(Feat,SuperType,SuperTerm,FV,Approp),Ref), % if
          erase(Ref)
        ->
           recorda(sig,attval(Feat,SuperType,SuperTerm,FV,Approp),_)    % then
        ;
           recorda(sig,attval(Feat,SuperType,SuperTerm,FV,Approp),_)    % else
        ),
        compile_features(SuperTerm,SubTerm,SuperType,Feats,Pos).
compile_features(_,_,_,[],_).

% compile_subtypes(SuperTerm,CurrentTerm,SuperType,CurrentType,Subtypes,Counter)

compile_subtypes(SuperTerm,Term,SuperType,Type,[Sub|Subs],N) :-
	Pos is N + 1,
	( arg(Pos,Term,Arg)      
        ; true                  % needed in case multiple occurences of
                                % type with multiple inheritance are replaced
                                % by atoms
	),
	!,
	comp_sub(SuperTerm,Arg,SuperType,Type,Sub),
	compile_subtypes(SuperTerm,Term,SuperType,Type,Subs,Pos).
compile_subtypes(_,_,_,_,[],_).

% comp_sub(SuperTerm,CurrentTerm,SuperType,CurrentType,SubType) 
%   NOTE: it seems that the third argument is not needed

comp_sub(SuperTerm,CurrentTerm,SuperType,CurrentType,SubTypes) :-
	member(SUB,SubTypes),
        sub_intro(SUB,Subs,Feat),
        length(Subs,SubLength),
        length(Feat,FeatLength),
        Length is SubLength + FeatLength,
        (  recorded(sig,subtype(SUB,OtherType,SuperTerm),Ref),
           erase(Ref)
        -> atom_concat('$',SUB,CurrentTerm), 
           (  CurrentType == OtherType
           -> Type = CurrentType
           ;  Type = CurrentType&OtherType
           )
        ;  atom_concat('$',SUB,Sub),
	   functor(CurrentTerm,Sub,Length),
	   Type = CurrentType
        ),
	recorda(sig,subtype(SUB,Type,SuperTerm),_),
	compile_subtypes(SuperTerm,CurrentTerm,SuperType,SUB,Subs,0),
	compile_features(SuperTerm,CurrentTerm,SuperType,Feat,SubLength),
	fail.
comp_sub(_,_,_,_,_).

sub_intro(SUPER,SubList,FEAT) :-
        recorded(sig,sub(SUPER,SubFeat),_),
	!,
        (  SubFeat = intro(Sub,Feat)
        -> trans_feat(Feat,FEAT)
        ;  (Sub = SubFeat, FEAT = [])
        ),
        make_list(Sub,SubList).
sub_intro(_,[],[]).               % no need to give explicit declarations
                                  % for types without subtypes or features
        
trans_feat([],[]).
trans_feat([Feature:Type|R],[Feature:Type|T]) :-
        atom(Feature),
	( Type = top
	; true
	),
	!,
	trans_feat(R,T).
trans_feat([Feature|R],[Feature:top|T]) :-
        atom(Feature),
	trans_feat(R,T).

make_list([],[]) :- !.       % needed for typed without subtypes
make_list(A*B,List) :-
	!,
	make_list(A,AList),
	append(AList,[B],List).
make_list(X,[X]).

is_top(Type,Extensional) :-
	recorded(sig,sub(top,AtomOrList),_),
	(  ( atom(AtomOrList); AtomOrList = -(_) )
	-> TOP = AtomOrList	
	;  member(TOP,AtomOrList)
	),
        extensionality(TOP,Type,Extensional).

extensionality(-(Type),Type,0) :-
	!.
extensionality(Type,Type,1).


/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:       compile_bool.pl 
% purpose:    compilation of boolean values a la Mellish
% created:    by Gertjan van Noord
% modified:   12 Jan 94 by GE for integration with ProFIT
% to do:	
% notes:	

% IMPORTS

% EXPORTS
% compile_bool_file/3
% eval_b_types/2
% give_boolean_type/2

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%% MELLISH' DISJUNCTION AND NEGATION OF ATOMIC TYPES %%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


% Path => Expression
%
% there are special types boolean(SetOfSets)
%
% eg. Name bool [1,2,3]&[sg,pl]&[mas,fem,neut].
%            
% Subtypes have no appropriate features, but should be atomic. Also no extra
% constraints attached to them. Uniqueness condition still applies.
%
% 
% syntax: Path => val
%                 (val & val)
%                 ~val
%                 ( val  or  val )
% or any combination.

compile_boo_file(_,Files,Files) :-
        \+ recorded(bool,_,_),
        !.
compile_boo_file(File,Files,[FileName|Files]) :-
        atom_concat(File,'.boo',FileName),
        open(FileName,write,Stream),
        write_boolean_types(Stream),
        compile_boolean_types(Stream),
        compile_boolean_atoms(Stream),
        close(Stream),
        no_style_check(single_var),
        compile(FileName).

write_boolean_types(Stream) :-
        recorded(bool,multifile(bool/2),_),
        ( PredSpec = bool/2
        ; PredSpec = btype/3
        ; PredSpec = boolean_atom/2
        ),
        write_clause(Stream,(:- multifile(PredSpec))),
        fail.
write_boolean_types(Stream) :-
        all((recorded(bool,bool(Type,ListOfSets),_Ref),
             write_clause(Stream,bool(Type,ListOfSets))
           )).
compile_boolean_types(Stream) :-
        all((recorded(bool,bool(Type,ListOfSets),_Ref),
             ff1(ListOfSets,Ar),       % calculates the # of combinations
             Ar2 is Ar + 1,            % add 1 to get n pairs of vars.
             functor(Term,Type,Ar2),   % build term
             arg(1,Term,0),            % initialize left end
             arg(Ar2,Term,1),          % initialize right end with other atom
             setof(X,poss(X,ListOfSets),List),  % List = possible combinations
             write_clause(Stream,btype(Type,List,Term))
           )).
compile_boolean_atoms(Stream) :-
	all((recorded(bool,bool(Type,ListOfSets),_Ref),
             member(Set,ListOfSets),
             member(Atom,Set),
             write_clause(Stream,boolean_atom(Atom,Type))
           )).

poss([],[]).
poss([H|T],[L|L2]):-
        member(H,L),
        poss(T,L2).


ff1([],0).
ff1([H|T],Out):-
        ff([H|T],1,Out).

ff([],In,In).
ff([H|T],In,Out):-
        length(H,I),
        In2 is In * I,
        ff(T,In2,Out).


/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:       compile_tpl.pl
% purpose:    loading of templates
% created:    08 Jan 94 by GE
% modified:	
% to do:      
% notes:	

% IMPORTS
% trans_term from sugar4.pl

% EXPORTS
% template/2 in .tpl file

compile_tpl_file(_,Files,Files) :-
	\+ recorded(tpl,_,_),      
	!.
compile_tpl_file(File,Files,[FileName|Files]) :-
        atom_concat(File,'.tpl',FileName),
        open(FileName,write,Stream),
	prolog_flag(unknown,Old,fail),
        compile_templates(Stream),
	prolog_flag(unknown,_,Old),
        close(Stream),
	clear_database(tpl),
        compile(FileName),
        style_check(single_var).

compile_templates(S) :-
        recorded(tpl,multifile(':='/2),_),
        (  constraints(on)
        -> write_prolog_clause(S,(:- multifile(template/4)))
	;  write_prolog_clause(S,(:- multifile(template/2)))
        ),
        fail.
compile_templates(S) :-
        recorded(tpl,template(Name,Def),_Ref),
        trans_name(Name,TName1,C0,C1),
        tt(Def,Term,[],C1,C2),
	trans_name(TName1,TName,C2,C), % this call for Terms in template 
                                       % name that are instantiated by 
                                       % translation of the template
        (  constraints(on)
	-> write_prolog_clause(S,template(TName,Term,C0,C))
	;  write_prolog_clause(S,template(TName,Term))
        ),
        fail.
compile_templates(_).

trans_name(Name,TName) -->
	{ functor(Name,F,A),
	  functor(TName,F,A)
        },
	trans_arguments(A,Name,TName,[]).

/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:      compile_plp5.pl
% purpose:   compiler for ProFIT clauses
% created:   01 Apr 93 on the Talgo from Barcelona to Valence
% modified:  Apr 93, Feb 94 for integration with ProFIT
% to do:     
% notes: 

/************************* COMPILER PREDICATES **************************/

compile_plp_file(_,'$$nil') :-
	\+ recorded(pl,_,_),
	!.
compile_plp_file(File,FileName) :-
	(  var(FileName)
        -> atom_concat(File,'.plp',FileName)
        ;  true
        ),
        open(FileName,write,Stream),
        write_prolog(Stream),
        close(Stream).

write_prolog(Stream) :-
        constraints(on),
        recorded(pl,clause(X),_Ref),
	(collect_solutions(trans_c_term(X,_),Liste) ->
	      all((member(PrologTerm,Liste),
                   write_c_term(Stream,PrologTerm)
                  ))
	 ;    error_msg(no_translation(X))),
	 fail.
write_prolog(Stream) :-
        constraints(off),
        recorded(pl,clause(X),_Ref),
	(collect_solutions(trans_term(X,_),Liste) ->
	      all((member(PrologTerm,Liste),
                   write_prolog_clause(Stream,PrologTerm)
                  ))
	 ;    error_msg(no_translation(X))),
	 fail.
write_prolog(_).

collect_solutions(Goal,_) :-
         call(Goal),
         Goal =.. [_,_,X],
         save_result(X),
         fail.
collect_solutions(_,Liste) :-
         recorded(pl,translation_result(Liste),Ref),
         erase(Ref).

save_result(X) :-
         (recorded(pl,translation_result(Y),Ref) ->
             erase(Ref),New = [X|Y]
          ;  New = [X]),
         recorda(pl,translation_result(New),_).
 





/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:     user_if.pl
% purpose:  user interface for queries
% created:  3 March 93 by GE
% modified: 15 Feb 94 by GE removed everything but ?/1
%           14 Sep 94 by jcb - pretty-printer for embedded terms,sets,finite
%                              domains
%           23 Sep 94 ge - added Sebastian Millies' copy_indep_term and hide/
%                          discover_feature				
% to do:    
% note:     


% eliminate_hidden_feature/2 converts a FIT term with hidden features into
% one without hidden feature leaving out unnecessary sorts

eliminate_hidden_features([],[]).
eliminate_hidden_features(.(X,Y),Term) :-
	Y == [],
	!,
	eliminate_hidden_features(X,ZwErg),
	(ZwErg = # ->
	    Term = #
	  ; Term = [ZwErg|[]]).
eliminate_hidden_features(.(X,Y),Term) :-
	eliminate_hidden_features(X,ZwErg1),
	eliminate_hidden_features(Y,ZwErg2),
	(\+ ZwErg1 = #, \+ ZwErg2 = # ->
            Term = .(ZwErg1,ZwErg2)
         ;  (\+ ZwErg1 = # ->
                Term = [ZwErg1|[]]
             ;  (\+ ZwErg2 = # ->
                    Term = ZwErg2
                 ;  Term = #))).

eliminate_hidden_features({}({}),{}) :- !.
eliminate_hidden_features({}(X),Term) :-
	eliminate_hidden_features(X,ZwErg),
	(\+ ZwErg = # ->
	    Term = {}(ZwErg)
	  ; #).

eliminate_hidden_features(X,Term) :-
	functor(X,F,N),
        N > 0,
        nonmember(F,[&,!,<,'$VAR']),
        !,
	X =..[_|ArgListe],
	eliminate_hidden_features(ArgListe,ZwErg),
	(ZwErg = # ->
	    atom_concat(F,'(#)',F0),
	    Term = F0
	;   Term =.. [F|ZwErg]).

eliminate_hidden_features(X&Y,Term) :-
        X = <_,
        !,
        eliminate_hidden_features(Y,ZwErg),
        (\+ ZwErg = # ->
	      Term = X&ZwErg
          ;   Term = #).

eliminate_hidden_features(X&Y,Term) :-
        !,
        eliminate_hidden_features(X,ZwErg1),
        eliminate_hidden_features(Y,ZwErg2),
        (\+ ZwErg1 = #, \+ ZwErg2 = # ->
            Term = ZwErg1&ZwErg2
         ;  (\+ ZwErg1 = # ->
                Term = ZwErg1
             ;  (\+ ZwErg2 = # ->
                    Term = ZwErg2
                 ;  Term = #))).

eliminate_hidden_features(X!Y,Term) :-
        !,
        (recorded(fit,hidden_feature(X),_) ->
            Term = #
         ;  eliminate_hidden_features(Y,ZwErg),
            Term = X!ZwErg).


eliminate_hidden_features(X,X).


hide_feature([]).
hide_feature([Head|Tail]) :-
	!,
	hide_feature(Head),
	hide_feature(Tail).
hide_feature(A) :-
        atom(A),
        (recorded(fit,hidden_feature(A),Ref) ->
	      erase(Ref)
	   ;  true),
        recordz(fit,hidden_feature(A),_).

show_hid_features :-
	nl,
	(recorded(fit,hidden_feature(X),_),
	    write(X),nl,fail
	 ;  true).

discover_feature([]).
discover_feature([Head|Tail]) :-
	!,
	discover_feature(Head),
	discover_feature(Tail).
discover_feature(A) :-
        recorded(fit,hidden_feature(A),Ref),
	erase(Ref).

discover_all_features :-
	(recorded(fit,hidden_feature(_),Ref),
	       erase(Ref),fail
	  ;    true).

% portray_message/2 for correct printing of ProFIT messages during the
% compilation

portray_message(_,loading(Com,File)) :-
    nl,
    Text = ['{',Com,' ',File,' ...   }'],
    write_list(Text).
portray_message(_,loaded(Com,File,Module,Time,Bytes)) :-
    nl,
    Text = ['{',Com,' ',File,' in module ',Module,', ',Time,' msec, ',Bytes,' Bytes}'],
    write_list(Text).

% '?'/1, prefix op used to give ProFIT queries from the Prolog prompt
% portray/1 should be defined suitably so that results are pretty-printed
'?'(Query) :- 
        clear_database(messages),
	trans_term(Query,Goal), 
        write_messages,
	(  Goal = _Module:_G
	-> ModGoal = Goal
	;  ModGoal = user:Goal
	),
	call(ModGoal).
'?'(_) :-
        write_messages,
        fail.

portray(Residue) :-
	nonvar(Residue),
        Residue = Module:Goal,
        write(Module), write(':'), portray(Goal).
portray(Prolog) :-
        (pp_option(format); pp_option(format2)),
        copy_term(Prolog, Term),
        untrans_term(Term,Fit),
	(recorded(fit,hidden_feature(_),_) ->
	       eliminate_hidden_features(Fit,Fit2)
	   ;   Fit2 = Fit),
        pretty_print(Fit2,4).
portray(Prolog) :-
	pp_option(on),
        copy_term(Prolog, Term),
	untrans_term(Term,Fit),
	write(Fit).
portray(F) :- float(F), !, format('~f', [F]).

pp(X) :-
	(X == on; X == format; X == format2; X == off),
	( recorded(fit,profit_portray(_),Ref),
	  erase(Ref),
	  fail
	; recorda(fit,profit_portray(X),_)
	),!. 

/****************************************************************************
pp(_) :-
	nl,write('Folgende Optionen stehen zur Verfuegung:'),nl,nl,
	write('off      : Ausgabe als PROLOG-Term'),nl,
	write('on       : Ausgabe des uebersetzten Terms'),nl,
	write('format  : pretty-printer mit Typangaben'),nl,
	write('format2  : pretty-printer ohne Typangaben'),nl.
****************************************************************************/

pp_option(X) :-
	recorded(fit,profit_portray(Y),_),
	!,
	X = Y.
pp_option(on).
	

:- discontiguous pretty_print/2.
pretty_print(X@Y,_) :-			%% finite domains
	!,
	(atomic(X) ->
	    write(X),write('@'),write(Y)
	;  (recorded(fit,profit_portray(Option),_), Option == format ->
	      write('('),write(X),write(')@'),write(Y)
	   ;  write(X))).

pretty_print({}(Liste),Indent) :-           %% Verarbeitung einer Menge
	!,
	arg_status(Liste,StatusList),
	IndentNew is Indent + 1,
	write('{'),
	list_print(Liste,StatusList,IndentNew,Term_Flag),
	(Term_Flag == true ->
	    nl,tab(Indent)
	  ; true),
	write('}').  
	
pretty_print('$$set'(Set),Indent):-     %% WS
	!,
	pretty_print(Set,Indent).

pretty_print(X,Indent) :-               %% Verarbeitung eines PROLOG-Terms
	functor(X,F,N),
	N > 0,
	nonmember(F,[&,!,<,'$VAR','.']),
	!,
	X =.. [_|Arg_Liste],
	arg_status(Arg_Liste,Status_Liste),
	write(F),write('('),
	atom_length(F,Len),
	IndentNew is Indent + Len + 1,
	list_print(Arg_Liste,Status_Liste,IndentNew,Term_Flag),
	(Term_Flag == true ->
	    IndentBracket is Indent + Len,
	    nl,tab(IndentBracket)
	;   true),
	write(')').
	 
	

pretty_print(.(Head,Tail),Indent) :-                %% Verarbeitung einer Liste
	!,
	write('['),
	IndentNew is Indent + 1,
	arg_status(.(Head,Tail),Status_Liste),
	list_print(.(Head,Tail),Status_Liste,IndentNew,Term_Flag),
	(Term_Flag == true ->
	    nl,tab(Indent)
	;   true),
	write(']').


list_print([Last|[]],_,Indent,Term_Flag) :-
	!,
	(compound(Last), \+ Last = '$VAR'(_) ->
	    Term_Flag = true
	 ;  true),
	 pretty_print(Last,Indent).

list_print([Head|Tail],[_,Status|Rest],Indent,Term_Flag) :-
	pretty_print(Head,Indent),
	( (compound(Head), \+ Head = '$VAR'(_)
           ; memberchk(Status,[komplex,variable])) ->
	          umbruch(Indent,Status,Term_Flag)
               ;  (Head = '...' ->
	               true  
	            ;  write(', '))),
	list_print(Tail,[Status|Rest],Indent,Term_Flag).

list_print('$VAR'(X),_,_,_) :-
	write('$VAR'(X)).              
    
pretty_print(X&FD,Indent) :-
        X = <(_),
        !,
        (recorded(fit,profit_portray(Option),_), Option == format ->
	    write(X), write(&),nl,tab(Indent)
	  ; true),
        pretty_print(FD,Indent).

pretty_print(X&FD,Indent) :-
        X = '$VAR'(_),
        !,
	write(X), write(&),nl,tab(Indent),
        pretty_print(FD,Indent).

pretty_print(X&Y,Indent) :-
        !, pretty_print(X,Indent), write('&'),nl,tab(Indent),
        pretty_print(Y,Indent).

pretty_print(A!B,Indent) :-
	atom(A),
        !,
        write(A), write(!), 
        atom_length(A,Len),
        Indent1 is Indent + Len + 1,
        pretty_print(B,Indent1).

pretty_print(X,_) :-
   write(X).

arg_status('$VAR'(_),[variable]).
arg_status([],[]).
arg_status([Head|Tail],[X|Resultat]) :-
	arg_status(Tail,Resultat),
	(Head = '$VAR'(_) ->
	    X = simpel
	 ;  (compound(Head) ->
	        X = komplex
	     ;  X = simpel)).

umbruch(Indent,Status,Term_Flag) :-
	(Term_Flag \== true, Status = variable ->
	    write('|')
	;   nl,tab(Indent),
	    (Status = variable ->
		write('|')
	    ;   write(',')),
	    nl,tab(Indent),
	    Term_Flag = true).

/* $Id: profit.pl,v 1.8 1995/12/03 16:33:06 erbach Exp erbach $ */
% file:      cycle.pl
% purpose:   translate a cyclic Prolog term into a Prolog term with variables
%            and a description of the cycles occuring in it
% created:   20 Mar 94 by GE
% modified:  15 Nov 95 fixed bug with display of cyclic terms (W. Skut)
% to do:     
% notes:     these prodcedures can be used to:
%            a) print out cyclic terms as Prolog terms plus =/2 goals
%            b) numbvars and translate feature terms, and print out
%               any cycles contained therein.

% test(N) :- 
% 	term(N,Term), 
% 	write_prolog_clause(user,Term).
% test(N,NCTerm,Cyc) :-
% 	term(N,Term),
% 	trans_prolog_term(Term,NCTerm,Cyc,[]).
% 
% term(1,cyclic_list(L)) :- L = [a|L].
% term(2,cyclic_term(L)) :- L = f(a,g(L),c).
% term(3,f([L])) :- L = f(a,g(L),c).
% term(4,L) :- L = f(f(L),f(L)).  % produces same constraint twice
% term(5,L) :- L = f(A,g(L),B), A = [a|A], B = f(g(B)).
% term(6,f(A,C)) :- C = g(A,C).
 
trans_prolog_term(Term,PrologTerm) -->
	(  { cycle(Term,[],[C|Cycles],[]) }
	-> trans_cyclic_term(Term,PrologTerm,[C|Cycles])
	;  { Term = PrologTerm }
        ).

% cycle/2 detects cycles in Prolog terms
cycle(Var,_) -->
	{ var(Var), ! }.

cycle(Term,SoFar) -->
	{ strict_member(Term,SoFar), ! },
	[Term/_].

cycle(Term,SoFar) -->
	{ functor(Term,_Functor,Arity) },
	cycle_arguments(Arity,Term,SoFar).

cycle_arguments(0,_,_) --> !.
cycle_arguments(N,Term,SoFar) -->
	{ arg(N,Term,Arg) },
	cycle(Arg,[Term|SoFar]),
	{ N1 is N-1 },
        cycle_arguments(N1,Term,SoFar).

trans_cyclic_term(Term,Term,_) -->
	{ var(Term) },
	!.
trans_cyclic_term(CyclicTerm,NewVar,Cycles) -->
	{ strict_member2(CyclicTerm/NewVar,Cycles) },
	!,
	build_cycle_desc(3,CyclicTerm,CyclicTerm,NewVar,CycleDesc,Cycles,[]),
	[NewVar=CycleDesc].
trans_cyclic_term(CyclicTerm,PrologTerm,Cycles) -->
	{ functor(CyclicTerm,Functor,Arity),
	  functor(PrologTerm,Functor,Arity)
        },
	trans_cyclic_args(Arity,CyclicTerm,PrologTerm,Cycles).

trans_cyclic_args(0,_,_,_) --> !.
trans_cyclic_args(N,CyclicTerm,PrologTerm,Cycles) -->
	{ arg(N,CyclicTerm,CyclicArg),
	arg(N,PrologTerm,PrologArg)
        },
	trans_cyclic_term(CyclicArg,PrologArg,Cycles),
	{ N1 is N-1 },
	trans_cyclic_args(N1,CyclicTerm,PrologTerm,Cycles).

build_cycle_desc(1,Term,CyclicTerm,NewVar,NewVar,_,_) -->
	{ Term == CyclicTerm, nonvar(Term), ! }.
build_cycle_desc(2,Term,CyclicTerm,NewVar,CycleDesc,Cycles,SoFar) -->
        !,
	{ functor(Term,Functor,Arity),
	  functor(CycleDesc, Functor,Arity)
        },
	build_cycle_desc_args(Arity,Term,CyclicTerm,NewVar,CycleDesc,Cycles,[Term|SoFar]).
build_cycle_desc(3,Term,CyclicTerm,NewVar,CycleDesc,Cycles,SoFar) -->
	{ functor(Term,Functor,Arity),
	  functor(CycleDesc, Functor,Arity)
        },
	build_cycle_desc_args(Arity,Term,CyclicTerm,NewVar,CycleDesc,Cycles,SoFar).

build_cycle_desc_args(0,_,_,_,_,_,_) --> !.
build_cycle_desc_args(N,Term,CyclicTerm,NewVar,CycleDesc,Cycles,SoFar) -->
	{ arg(N,Term,ArgN),
	  arg(N,CycleDesc,DescArgN)
        },
	(  { strict_subterm(CyclicTerm,ArgN,SoFar) }
	-> build_cycle_desc(_,ArgN,CyclicTerm,NewVar,DescArgN,Cycles,SoFar)
	;  trans_cyclic_term(ArgN,DescArgN,Cycles)
	),
	{ N1 is N - 1 },
        build_cycle_desc_args(N1,Term,CyclicTerm,NewVar,CycleDesc,Cycles,SoFar).

strict_subterm(X,Y,_) :- X == Y.
strict_subterm(_,Var,_) :- var(Var), !, fail.
strict_subterm(X,Y,SoFar) :-
	functor(Y,_,A),
	between(N,1,A),
	arg(N,Y,Z),
	\+ strict_member(Z,SoFar),
	strict_subterm(X,Z,[Z|SoFar]).

between(N,Min,Max) :-
	Min =< Max,
	N = Min.
between(N,Min,Max) :-
	Min < Max,
	Min1 is Min+1,
	between(N,Min1,Max).
	
% strict_member2(X,L)
% X/Var is a strict_member2 of L if L has an element Y/Var such that X == Y.
strict_member2(X/Var,[XX/Var|_]) :- X == XX, !.
strict_member2(X,[_|R]) :- nonvar(R), strict_member2(X,R).      




















































































/*Id$*/

% file   : error.pl
% purpose: error processing
% created: Oct 94 by JCB

error_proc(double_sort_declaration) :-
	recorded(sig,sort_list(List),_),
	double_test(List,Double_List),
	(Double_List == [] ->
            true
	 ;  error_msg(double_sort_definiton(Double_List))),
	 !.
	
error_proc(sort_cycle) :-
	 subtype_test(top,[])
     ;   true.

error_proc(undefined_sortal_restriction) :-
         all((recorded(sig,attval(_,_,_,_,Restriction),_),
	     ( (recorded(sig,subtype(Restriction,_,_),_)
	       ;Restriction = set
               ;Restriction = lp_set 
               ;Restriction = top) ->
	           true
	      ;    error_msg(undef_restriction(Restriction))))). 

error_proc(lonely_sort) :-
	all((recorded(sig,sub(Type,SubTypes),_),
	     ((recorded(sig,subtype(_,Type,_),_)
	      ;recorded(sig,subtype(Type,_,_),_)) ->
		       true
                    ;  error_msg(lonely_sort(>(Type,SubTypes))))
            )).
	
error_proc(def_attr,Var) :-
        var(Var),
        !.
error_proc(def_attr,Attr) :-
        (attval(Attr,_,_,_,_) ->
              true
	 ;    error_msg(undefined_feature(Attr)),!,fail).

error_proc(undefined_sort,Var) :-
        var(Var),
        !.
error_proc(undefined_sort,Sort) :-
        (subtype(Sort,_,_) ->
             true
	 ;   error_msg(undefined_sort(Sort)),!,fail).

% syntax_check(Term_to_test)

syntax_check(>(top,(Sub) intro Feat)) :-
	error_msg(syntax(>(top,(Sub) intro Feat))),fail.
syntax_check(>(top,A*B)) :-
	error_msg(syntax(>(top,A*B))),fail.
syntax_check(>(top,Sub)) :- (atomic(Sub);functor(Sub,'-',1)). 

syntax_check(>(Super,(Sub) intro Feat)) :-
	!,
	(list_check(Feat,':') ->
	    syntax_check(>(Super,Sub))
	;   error_msg(syntax(Feat)),fail).

syntax_check(>(Super,Sub)) :-
	!,
	(Super = top ->
	    Allowed_Functor = '-'
	;   Allowed_Functor = '#'),      %i.e. no functor allowed
	(atomic(Super), multi_dim_check(Sub,Allowed_Functor) ->
	    true
	;   error_msg(syntax(>(Super,Sub))),fail).

syntax_check(intro(Super,Feat)) :-
	(list_check(Feat,':') ->
	    true
	;   error_msg(syntax(intro(Super,Feat))),fail).

syntax_check(fin_dom(A,B)) :-
	(atom(A), multi_dim_check(B,#) ->
	    true
	;   error_msg(syntax(fin_dom(A,B))),fail).
	
syntax_check(bool(A,B)) :-
        (atom(A), multi_dim_check(B,#) ->
            true
        ;   error_msg(syntax(bool(A,B))),fail).

syntax_check(hidden_features(List)) :-
	(list_check(List,#) ->
	    true
	 ;  error_msg(syntax(hidden_feature(List))),fail).



syntax_check(_).     % everything else is all right


% error(Code,Error_or_Warning,Text)
% Error_or_Warning: err = Error
%                   war = Warning
%                   msg = Progress Message
% Code = [ErrorCode,Wrong_Term]

%   E R R O R   M E S S A G E S

error(sort_cycle(_),err,"Cycle in the sort hierarchy").
error(double_sort_definiton(_),err,"a sort must not be defined more than once").
error(syntax(_),err,"syntax error").
error(undefined_feature(_),err,"a feature isn't declared").
error(undefined_sort(_),err,"a sort isn't declared").
error(wrong_searchpath(_),err,"a search path doesn't exist").
error(undef_restriction(_),err,"a sort used as a restriction isn't declard").
error(wrong_bool(_),err,"error in boolean term").
error(wrong_bool_atom(_),err,"a atom used in a boolean term isn't a boolean atom").
error(wrong_bool_type(_),err,"a type used in a boolean term isn't a boolean type").
error(file_not_exist(_),err,"the file doesn't exist").
error(no_translation(_),err,"there's no Prolog term for this ProFIT term").
error(comp_abort(_),err,"compilation aborted").
error(impossible_filename(_),err,"the arg. to fit/1 can be an atom or library/1 or a list of such").

%    W A R N I N G S

error(lonely_sort(_),war,"a sort can't be reached from 'top'").


error_msg(Code) :-
	error(Code,Type,Message),
	(Type = err ->
	    (recorded(sig,error_flag(yes),_) ->
		true
	     ;  recorda(sig,error_flag(yes),_))
	 ;  true),
	Code =.. [_,Term],
	recordz(messages,message(Type,Term,Message),_).
        
write_type(err) :- write('ProFIT ERROR:   ').
write_type(war) :- write('ProFIT WARNING: ').
 
msg_format(sort_cycle,Type,[H|T],Wort,String) :-
	(Type = H ->
	    atom_concat(Type,Wort,String)
	 ;  atom_concat(H,Wort,N),
	    atom_concat(' -> ',N,W),
	    msg_format(sort_cycle,Type,T,W,String)).


subtype_test(Type,List_of_sorts) :-
	recorded(sig,sub(Type,Sorts),_),
	make_sort_list(Sorts,List),
	member(X,List),
	(member(X,List_of_sorts) ->
	    msg_format(sort_cycle,X,[Type|List_of_sorts],'',String),
	    error_msg(sort_cycle(>(String,Sorts))),fail
	 ;  subtype_test(X,[Type|List_of_sorts])).
	

% list_check(List,Functor): true, if each of the elements of List is 
%                             - a atom not being 'top' or
%                             - a compound term with the functor Functor 
%                               and its arguments are atomic or
%                             - if List is the empty list



list_check([],_).
list_check([H|T],F) :-
	atomic(H),
	!,
	H \== top,
	list_check(T,F).
list_check([H|T],F) :-
	functor(H,F,_),
	H =.. [_|Argumente],
	list_check(Argumente,#),
	list_check(T,F).


% multi_dim_check(Term,Functor): Term = Term * A
%                                       |A
%                                A    = [_]
% true, if list_check/2 is true with every list of Term


multi_dim_check(B*A,Functor) :-
	!,
	list_check(A,Functor),
	multi_dim_check(B,Functor).
multi_dim_check(B,Functor) :- list_check(B,Functor).


my_delete(_,[],[]).
my_delete(Element,[Element|Rest],Liste) :-
        !,
        my_delete(Element,Rest,Liste).
my_delete(Element,[X|Rest],[X|Liste]) :-
        my_delete(Element,Rest,Liste).

% double_check(+List,?List_of_Elements)
%
% List_of_Elements contains all elements appearing more than once in List

double_test([],[]).
double_test([H|T],[H|List]) :-
        member(H,T),
        !,
        my_delete(H,T,T2),
        double_test(T2,List).
double_test([_|T],List) :-
        double_test(T,List).

make_sort_list(A intro _, List) :-
	!,
	make_sort_list(A,List).
make_sort_list(B*A,List) :-
	!,
	make_sort_list(B,ZwErg),
	append(A,ZwErg,List).
make_sort_list(A,A) :-
	functor(A,'.',_),
        !.
make_sort_list(A,[A]).

%% [matsc] misc. compatibility

tab(N) :- (for(_,1,N) do write(' ')).

tab(S, N) :- (for(_,1,N), param(S) do write(S, ' ')).

