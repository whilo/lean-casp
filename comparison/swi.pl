:- use_module(library(http/json)).
:- use_module(library(scasp/compile)).
:- use_module(library(scasp/solve)).
:- use_module(library(sscasp/source), [read_program/2]).
:- use_module(library(sscasp/run), [scasp_loaded/4, scasp_ask/4]).

% Wall time, in nanoseconds as in the Lean harness. Preparation excludes file IO
% for sscasp. scasp_load/2 includes reading the file in the classic interface.
verdict(Goal, A) :- (once(Goal) -> A=true ; A=false).

sample(B, Goal, Prep, Ns, Answer) :-
    get_time(E), Prep is round((E-B)*1.0e9),
    verdict(Goal,Answer), get_time(T0), verdict(Goal,Answer), get_time(T1),
    Ns is round((T1-T0)*1.0e9).

trial(classic,File,Prep,Ns,A) :-
    get_time(B), scasp_load(File, [unknown(fail)]), scasp_query(Q,_,[]),
    sample(B,solve(Q,[],_,_),Prep,Ns,A).
trial(new,File,Prep,Ns,A) :-
    read_program(File,S), get_time(B),
    once(scasp_loaded(S.terms, L, sample(B,scasp_ask(L,S.query,_,_),Prep,Ns,A), [])).

run(Engine, File) :-
    findall(row(P,N,A),(between(1,7,_),trial(Engine,File,P,N,A)),Rows),
    length(Rows,7), Rows=[row(_,_,A)|_], forall(member(row(_,_,V),Rows),V==A),
    findall(P,member(row(P,_,_),Rows),Ps), msort(Ps,SortedP), nth0(3,SortedP,MedianP),
    findall(N,member(row(_,N,_),Rows),Ns), msort(Ns,SortedN), nth0(3,SortedN,MedianN),
    format('~w\t~d\t~d~n',[A,MedianP,MedianN]).

% Apply domain restrictions after the open query has returned its constraints.
domain_value(Domain, X) :- member(X, Domain).
rows(Goal, Vars, Domain) :-
    findall(Vars, (call(Goal), maplist(domain_value(Domain), Vars)), All),
    sort(All, Unique), json_write(current_output, Unique, [width(0)]), nl.

run_rows(classic, File, Domain) :-
    scasp_load(File,[unknown(fail)]), scasp_query(Q,_,[]),
    term_variables(Q, Vars), rows(solve(Q,[],_,_), Vars, Domain).
run_rows(new, File, Domain) :-
    read_program(File,S), term_variables(S.query, Vars),
    once(scasp_loaded(S.terms,L,rows(scasp_ask(L,S.query,_,_), Vars,Domain),[])).

:- initialization(main, main).
main([Engine,File,Domain]) :-
    atomic_list_concat(Values, ',', Domain),
    call_with_time_limit(30,run_rows(Engine,File,Values)).
main([Engine,File]) :- call_with_time_limit(30, run(Engine,File)).
