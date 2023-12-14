/* g4c-reasoner-complete.pl
   part of G4C
   Prover for checking whether the formal criteria of one grant imply
   that of another one.
   The implemented logic is standard classical propositional logic, in
   the form of an invertible G3c sequent calculus (see, e.g., Troelstra,
   Schwichtenberg: Basic Proof Theory).
*/

/* Data structures:
   - Formulae are defined via the following grammar in BNF:
          Fml ::= at(Atom) | at(false) | at(true) | Fml and Fml | Fml or Fml |
          Fml -> Fml | and(List) | or(List) | neg(Fml)
     where
          - Atom is an atomic statement
          - List is a list of formulae
   - Sequents are structures of the form
        seq(Gamma,Delta)
        Gamma => Delta
     where Gamma and Delta are lists of formulae.
   - derivation trees are trees constructed using the constructor
     'der' with the following arguments:
          der(Rule_name, Conclusion, Principal_formula, Premisses)
      where 
          - Rule_name is the name of the applied rule
          - Conclusion is the conclusion of the rule application
          - Principal_formula is the principal formula of the rule
            application
          - Premisses is the list of derivations of the premisses of the
            rule application, i.e., the list of successor nodes.
*/


:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(dif)).
:- use_module(library(pio)).

/* operator definitions
*/
  :- op(400,fy,neg).
  :- op(500,xfy,and).
  :- op(600,xfy,or).
  :- op(700,xfy,->).
  :- op(750,xfy,=>).
  :- op(800,xfy,/).

/* prove_and_print
   takes a sequent, tries to prove it and if successful writes the
   derivation as an html string to user output.
*/
prove_and_print(Seq) :-
    prov2(Seq,Derivation),
    phrase_to_stream(pp_result(Derivation),user_output),!.



/* rule /2
   First argument is the rule name.
   Second argument is the rule in the format List / PF where List is a list of sequents, and PF is the principal formula, i.e. a structure Fml => [] or [] => Fml 
*/
% left rules:
% falsum
rule(botL, [] / at(false) => []).
rule(botL, [] / false => []).
% negation
rule(negL, [ [] => [A] ] / neg(A) => [] ).
% conjunction
rule(andL, [[A,B]=>[]] / and(A,B)=>[]).
rule(andL, [[A|List] => []] / and([A|List]) => []).
% disjunction
rule(orL, [[A] => [], [B] => []] / or(A,B) => []).
rule(orL, Prem_list / or(Fml_list) => []) :-
    maplist(sequent_lhs_formula, Prem_list, Fml_list).
% implication
rule(toL, [[B] => [], [] => [A]] / A -> B => []).
% defined formulae left
rule(df, [ [Definition] => [] ] / df(Name) => [] ) :-
    subrule(Name, förderkriterien(Definition)).
% right rules
% verum
rule(topR, [] / [] => at(true)).
rule(topR, [] / [] => true).
% negation
rule(negR, [ [A] => [] ] / [] => neg(A) ).
% disjunction
rule(orR, [ [] => [A,B] ] / [] => or(A,B)).
rule(orR, [ [] => List ] / [] => or(List)).
% implication
rule(toR, [ [A] => [B] ] / [] => A -> B).
% conjunction
rule(andR, [ [] => [A], [] => [B] ] / [] => and(A,B)).
rule(andR, Prem_list / [] => and(Fml_list) ) :-
    maplist(sequent_rhs_formula, Prem_list, Fml_list).
% defined formulae right
rule(df, [ [] => [Definition]] / [] => df(Name)) :-
    subrule(Name, förderkriterien(Definition)).


/* sequent_lhs_formula
   true if the first argument is a sequent with exactly the second argument on the left hand side.
*/
sequent_lhs_formula([A] => [], A).
/* sequent_rhs_formula
   true if the first argument is a sequent with exactly the second argument on the right hand side.
*/
sequent_rhs_formula([] => [A], A).


/* initial_sequent /2
   first argument is the name of the rule, second is the principal formulae in the form Fml => Fml.
*/
initial_sequent(init, A => A).
% Ground sequent for rechtsform_in
initial_sequent(ground, at(rechtsform_in(List1)) => at(rechtsform_in(List2))) :-
    maplist(rebmem(List2), List1).
% Ground sequent for önace_in
initial_sequent(ground, at(önace_in(List1)) => at(önace_in(List2))) :-
    maplist(list_contains_prefix(List2),List1).
% Ground sequents for unternehmenssitz_in
initial_sequent(ground, at(unternehmenssitz_in(List1)) => at(unternehmenssitz_in(List2))) :-
    maplist(country_name_as_gemeindekennziffer,List1,L1),
    maplist(country_name_as_gemeindekennziffer,List2,L2),
    maplist(list_contains_prefix(L2),L1).
% Unternehmenssitz is unique
initial_sequent(ground, [at(unternehmenssitz_in(List1)), at(unternehmenssitz_in(List2))] => []) :-
    maplist(country_name_as_gemeindekennziffer,List1,L1),
    maplist(country_name_as_gemeindekennziffer,List2,L2),
    maplist(no_prefixes(L1), L2),
    maplist(no_prefixes(L2), L1).
% Ground sequents for betriebsstandort_in
initial_sequent(ground, at(betriebsstandort_in(List1)) => at(betriebsstandort_in(List2))) :-
    maplist(country_name_as_gemeindekennziffer,List1,L1),
    maplist(country_name_as_gemeindekennziffer,List2,L2),
    maplist(list_contains_prefix(L2),L1).
% Ground sequents for mitgliedschatf_in_wirtschaftskammer_in
initial_sequent(ground, at(mitgliedschaft_in_wirtschaftskammer_in(List1)) => at(mitgliedschaft_in_wirtschaftskammer_in(List2))) :-
    maplist(country_name_as_gemeindekennziffer,List1,L1),
    maplist(country_name_as_gemeindekennziffer,List2,L2),
    maplist(list_contains_prefix(L2),L1).


/* prov /1
   true if the argument is a sequent derivable using the rules.
*/
/* initial and ground sequents
*/
prov(Gamma => Delta) :-
    member(A,Gamma),
    member(B,Delta),
    initial_sequent(_,A => B).

/* single premiss left rules
*/
/* left rules
*/
prov(Gamma => Delta) :-
    select(Fml,Gamma,Omega),
    rule(_,Prems / Fml => []),
    merge_sequent_list(Prems, Omega => Delta, New_Prems),
    maplist(prov,New_Prems).
/* right rules
*/
prov(Gamma => Delta) :-
    select(Fml, Delta, Pi),
    rule(_, Prems / [] => Fml),
    merge_sequent_list(Prems,Gamma => Pi, New_prems),
    maplist(prov, New_prems).


/* prov2 /2
   true if the first argument is a sequent derivable using the rules and the second argument is the derivation tree.
*/
/* initial and ground sequents
*/
prov2(Gamma => Delta,der(Rule_name, Gamma => Delta, [A] => [B], [])) :-
    member(A,Gamma),
    member(B,Delta),
    initial_sequent(Rule_name,A => B).
prov2(Gamma => Delta, der(Rule_name, Gamma => Delta, [A,B] => [],[])) :-
    member(A, Gamma),
    member(B, Gamma),
    dif(A,B),
    initial_sequent(Rule_name, [A,B] => []).
/* left rules
*/
prov2(Gamma => Delta, der(Rule_name, Gamma => Delta, [Fml] => [], New_prems_ders)) :-
    select(Fml,Gamma,Omega),
    rule(Rule_name,Prems / Fml => []),
    merge_sequent_list(Prems, Omega => Delta, New_Prems),
    maplist(prov2,New_Prems, New_prems_ders).
/* right rules
*/
prov2(Gamma => Delta, der(Rule_name, Gamma => Delta, [] => [Fml], New_prems_ders)) :-
    select(Fml, Delta, Pi),
    rule(Rule_name, Prems / [] => Fml),
    merge_sequent_list(Prems,Gamma => Pi, New_prems),
    maplist(prov2, New_prems, New_prems_ders).



/* merge_sequent_list /3
*/
merge_sequent_list([],_,[]).
merge_sequent_list([Gamma => Delta], Sigma => Pi, [Omega => Theta]) :-
    append(Gamma,Sigma,Omega),
    append(Delta, Pi, Theta).
merge_sequent_list([Gamma => Delta, Seq|List], Sigma => Pi, [Omega => Theta, Seq2 | List2]) :-
    append(Gamma,Sigma,Omega),
    append(Delta, Pi, Theta),
    merge_sequent_list([Seq | List], Sigma => Pi, [Seq2 | List2]).



/* provable
   provable(Sequent, Der) is true if Sequent is derivable in the
   sequent calculus G3c with derivation Der.
   NOTE: Legacy.
*/
provable(seq(L,R),Der) :- prov2(L => R,Der).


% rebmem /2
% member with inverted order of arguments for convenience.
rebmem(List, A) :- member(A,List).

% prefix
% true if first argument (List) is a prefix of the second argument (List)
prefix([],_).
prefix([A|List1],[A|List2]) :-
    prefix(List1,List2).

% list_contains_prefix
% true if first argument (List), contains a prefix of the second argument.
list_contains_prefix([List1|_],List2) :-
    prefix(List1,List2).
list_contains_prefix([_|Ls],List2) :-
    list_contains_prefix(Ls,List2).

% no_prefixes /
% true if none of the elements of the first argument is a prefix of the second argument
no_prefixes([],_).
no_prefixes([A|L1],B) :-
    no_prefix(A,B),
    no_prefixes(L1,B).

% no_prefix /2
% true if the first argument is not a prefix of the second argument
no_prefix([_|_],[]).
no_prefix([A|_],[B|_]) :-
    dif(A,B).
no_prefix([A|L1],[A|L2]) :-
    no_prefix(L1,L2).
	   

% country_name_as_gemeindekennziffer
% converts between names for bundeslaender and their codes.
country_name_as_gemeindekennziffer("Land-Bgld","1").
country_name_as_gemeindekennziffer("Land-Kärnten","2").
country_name_as_gemeindekennziffer("Land-Nö","3").
country_name_as_gemeindekennziffer("Land-Oö","4").
country_name_as_gemeindekennziffer("Land-Salzurg","5").
country_name_as_gemeindekennziffer("Land-Stmk","6").
country_name_as_gemeindekennziffer("Land-Tirol","7").
country_name_as_gemeindekennziffer("Land-Vgb","8").
country_name_as_gemeindekennziffer("Land-Wien","9").
country_name_as_gemeindekennziffer(X,X) :- maplist(dif(X),["Land-Bgld","Land-Kärnten","Land-Nö","Land-Oö","Land-Salzurg","Land-Stmk","Land-Tirol","Land-Vgb","Land-Wien"]).



/* Test predicates for uniqueness of unternehmenssitz_in
*/
% add_pf /3
% true if the third argument contains the maximum of the second argument and any elements from the first argument (List)
/*
add_pf([],A,A).
add_pf([A|Xs],B,C) :- dif(A,B), prefix(B,A), add_pf(Xs,A,C).
add_pf([A|Xs],B,B) :- dif(A,B), prefix(A,B), add_pf(Xs,B,C).
add_pf([A|Xs],B,C) :- dif(A,B), no_prefix(A,B), no_prefix(B,A), add_pf(Xs,B,C).
*/
/*
add_pf([],A,A).
add_pf([A|Xs],B,C) :- prefix(B,A), add_pf(Xs,A,C).
add_pf([A|Xs],B,C) :- no_prefix(A,B), add_pf(Xs,B,C).
*/



/* pretty printing
   pp_deriv(der(Rule, Seq, PF, Suc))
   DCG for pretty printing a derivation in html
*/
pp_deriv(der(Rule,Seq,PF,Suc)) -->
    "Die Aussage <br /><code>", pp_Seq(Seq), "</code><br /> ist herleitbar, denn:<br />", pp_rule_justification(Rule,PF),
    "<ul>", pp_deriv_list(Suc), "</ul>".

/* pp_deriv_list
   DCG for pretty printing a list of derivations in html (each
   derivation as a list item
*/
pp_deriv_list([]) --> [].
pp_deriv_list([Der|List]) -->
    "<li> ", pp_deriv(Der), "</li>", pp_deriv_list(List).


/* pp_rule_justification
   DCG for pretty printing the justification for a rule using the
   principal formulae of that rule.
   NOTE: To be specified
*/
pp_rule_justification(init,PF) -->
    "Die Aussage gilt, da:<br /><code>", pp_Seq(PF), "</code>".
pp_rule_justification(ground,PF) -->
    "Die Aussage gilt, da:<br /><code>", pp_Seq(PF), "</code>".
pp_rule_justification(botL,_) --> "Die Aussage gilt, da <code>", pp_Fml(false), "</code> immer falsch ist.".
pp_rule_justification(topR,_) --> "Die Aussage gilt, da <code>", pp_Fml(true), "</code> immer wahr ist.".
pp_rule_justification(_,_) --> "Die Aussage folgt mittels Aussagenlogik aus:".

/* pp_Seq
   DCG for pretty printing a sequent in html
*/
pp_Seq(seq(Gamma,Delta)) -->
    "If we assume that ( ", pp_Fml_list(l,Gamma),
    "),<br /> then it is the case that ( ", pp_Fml_list(r,Delta)," )".
pp_Seq(Gamma => Delta) -->
    "Unter der Annahme, dass ( ", pp_Fml_list(l,Gamma),
    "),<br /> gilt immer: ( ", pp_Fml_list(r,Delta)," )".

/* pp_Fml_list
   DCG for pretty printing a list of formulae
*/
pp_Fml_list(l, []) --> "true".
pp_Fml_list(r, []) --> "wir haben einen Widerspruch".
pp_Fml_list(_, [A|[]]) --> 
    pp_Fml(A).
pp_Fml_list(l, [A|Tail]) --> 
    pp_Fml(A), " und ", pp_Fml_list(l, Tail).
pp_Fml_list(r, [A|Tail]) --> 
    pp_Fml(A), " oder ", pp_Fml_list(r, Tail).

/* pp_Fml_DCG /2
 * DCG to write a formula. Takes additional argument Form for the
 * format (either 'screen', 'latex' or 'html').
*/
% clauses for html: 
pp_Fml(true) --> "true".
pp_Fml(at(true)) --> "true".
pp_Fml(false) --> "false".
pp_Fml(at(false)) --> "false".
pp_Fml(at(önace_in(List))) --> "Die ÖNACE-Klassifizierung fällt unter: ", pp_list(List).
pp_Fml(at(unternehmenssitz_in(List))) --> "Der Unternehmenssitz ist in einem der folgenden: ", pp_list(List).
pp_Fml(at(betriebsstandort_in(List))) --> "Ein Betriebsstandort ist in einem der folgenden: ", pp_list(List).
pp_Fml(at(rechtsform_in(List))) --> "Die Rechtsform des Unternehmens ist eine der folgenden: ", pp_list(List).
pp_Fml(at(X)) --> [X].
pp_Fml(and(A,B)) -->
    "(", pp_Fml(A),
    ") und (",
    pp_Fml(B), ")".
pp_Fml(and([A,B])) -->
    "(", pp_Fml(A),
    ") und (",
    pp_Fml(B), ")".
pp_Fml(and([A,B|List])) -->
    "(", pp_Fml(A),
    ") und ",
    pp_Fml(and([B|List])).
pp_Fml(or(A,B)) -->
    "(", pp_Fml(A),
    ") oder (",
    pp_Fml(B), ")".
pp_Fml(or([A,B])) -->
    "(", pp_Fml(A),
    ") oder (",
    pp_Fml(B), ")".
pp_Fml(or([A,B|List])) -->
    "(", pp_Fml(A),
    ") oder ",
    pp_Fml(and([B|List])).
pp_Fml(->(A,B)) -->
    "wenn (", pp_Fml(A),
    "), so (",
    pp_Fml(B), ")".
pp_Fml(neg(A)) -->
    "es ist nicht der Fall, dass: (",
    pp_Fml(A),
    ")".

pp_list([]) --> [].
pp_list([A]) --> A.
pp_list([A|Ls]) --> A, ", ", pp_list(Ls).

pp_html_header --> "<!DOCTYPE html> <head> <title>Test page</title> </head><body>  <div>". 
% <style>  <!-- .abstract {    color: rgb(55,55,55);    display:none;    width: 100%;    text-align: left;    margin:15px;    }  body {    font-family:\"Helvetica Neue\",Helvetica,Arial,sans-serif;    font-size:14px;    line-height:1.42857143;    color:#333;    background-color:#fff  }  kbd {    padding:2px 4px;    font-size:90%;    color:#fff;    background-color:#333;    border-radius:3px;    -webkit-box-shadow:inset 0 -1px 0 rgba(0,0,0,.25);    box-shadow:inset 0 -1px 0 rgba(0,0,0,.25)  }  code {    padding:2px 4px;    font-size:90%;    color:#c7254e;    background-color:#f9f2f4;    border-radius:4px  }  hr {    margin-top:20px;    margin-bottom:20px;    border:0;    border-top:1px solid #eee  } --> </style> 

pp_html_footer --> "  </div>  </body></html>\n".


pp_result(Tree) -->
    pp_html_header,
    pp_deriv(Tree),
    pp_html_footer.



/* Concepts
   Part for extracting the used concepts from the list of grants.
*/

% cpt
% DCG for extracting the atomic concepts from a formula representing
% the grant conditions

% Or
cpt(or([])) --> [].
cpt(or([X|Tail])) --> cpt(X), cpt(or(Tail)).
cpt(or(X,Y)) --> cpt(X), cpt(Y).
% And
cpt(and([])) --> [].
cpt(and([X|Tail])) --> cpt(X), cpt(and(Tail)).
cpt(and(X,Y)) --> cpt(X), cpt(Y).
% Not
cpt(not(X)) --> cpt(X).
cpt(neg(X)) --> cpt(X).
% Atomic formulae
cpt(true) --> [].
cpt(at(true)) --> [].
cpt(false) --> [].
cpt(at(false)) --> [].
cpt(at(önace_in(_))) --> ["Önace_in"].
cpt(at(unternehmenssitz_in(_))) --> ["Unternehmenssitz_in"].
cpt(at(betriebsstandort_in(_))) --> ["Betriebsstandort_in"].
cpt(at(rechtsform_in(_))) --> ["Rechtsform_in"].
cpt(at(mitgliedschaft_in_wirtschaftskammer_in(_))) --> ["Mitgliedschaft_in_Wirtschaftskammer_in"].
cpt(df(Name)) --> {subrule(Name,förderkriterien(X))}, cpt(X).


% find_concepts
% DCG for extracting the atomic concepts from a list of formulae
% representing grant conditions.
find_concepts([]) --> [].
find_concepts([X|Tail]) --> cpt(X),find_concepts(Tail).


% concept_set /1
% true if Set is the set of concepts used in the grants.
concept_set :- findall(X, förderung(_,förderkriterien(X)), Xs),
		      phrase(find_concepts(Xs), Cs),
		      list_to_set(Cs, Set),
		      nl, write("Die in den Förderungen enthaltenen Konzepte sind:"), nl,
		      pp_write(Set),nl,!.




% pp_write
% for writing a list of items separated by a newline each.
pp_write([]).
pp_write([X]) :- write(X),nl.
pp_write([X,Y|Tail]) :- write(X), nl, pp_write([Y|Tail]).




/* Grants
   Information about a number of example grants
*/
förderung("G4c/Grants_Umweltförderung - Effiziente Energienutzung", förderkriterien(neg( ( at( önace_in( [ "84.1" ] ) )) ))).
förderung("G4c/Grants_Umweltförderung - Erneuerbare Energieträger", förderkriterien(neg( ( at( önace_in( [ "84.1" ] ) )) ))).
förderung("G4c/Grants_Öko:Fit Kärnten Umwelt- Und Effizienzberatung Für Betriebe Und Gemeinden", förderkriterien(( at( unternehmenssitz_in( [ "Land-Kärnten" ] ) ) or  at( betriebsstandort_in( [ "Land-Kärnten" ] ) )))).
förderung("G4c/Grants_Qualifizierungsförderung Für Beschäftigte (Qfb)", förderkriterien((( at( unternehmenssitz_in( [ "Land-Kärnten" ] ) ) or  at( betriebsstandort_in( [ "Land-Kärnten" ] ) )) and neg( (( at( önace_in( [ "64", "65", "66", "67", "68" ] ) ) or  at( rechtsform_in( [ "Öffentlich-Rechtliche-Körperschaft", "Landesgesetzlich-Eingesetzte-Stiftung-Oder-Fonds", "Bundesgesetzlich-Eingesetzte-Stiftung-Oder-Fonds" ] ) ) or  at( önace_in( [ "94.92" ] ) ))) ) and at(true)))).
förderung("G4c/Grants_Nachhaltig Wirtschaften: Umweltberatungen (Nöwtf)", förderkriterien((neg( ( at( önace_in( [ "01", "02", "03", "64", "65", "66", "84", "85", "86", "87", "88", "90", "91", "92", "93", "94", "95", "96", "97", "98", "99" ] ) )) ) and ( at( unternehmenssitz_in( [ "Land-Nö" ] ) ) or  at( betriebsstandort_in( [ "Land-Nö" ] ) ))))).
förderung("G4c/Grants_Förderung Umwelt- Und Energieberatung Oberösterreich", förderkriterien(( at( unternehmenssitz_in( [ "Land-Oö" ] ) ) or  at( betriebsstandort_in( [ "Land-Oö" ] ) )))).
förderung("G4c/Grants_Offensive 'Lehrlingsfreundlichstes Bundesland Salzburg'", förderkriterien(( at( unternehmenssitz_in( [ "Land-Salzburg" ] ) ) and at(true) and at(true)))).
förderung("G4c/Grants_Betriebliche Beratung Im Bereich Umwelt Und Abfallwirtschaft Salzburg", förderkriterien(( at( unternehmenssitz_in( [ "Land-Salzburg" ] ) ) or  at( betriebsstandort_in( [ "Land-Salzburg" ] ) )))).
förderung("G4c/Grants_Lebensqualität Bauernhof - Psychosoziale Beratung Für Bäuerliche Betriebe/Familien", förderkriterien((( at( unternehmenssitz_in( [ "Land-Salzburg" ] ) ) or  at( betriebsstandort_in( [ "Land-Salzburg" ] ) )) and (( at( önace_in( [ "01" ] ) ) and neg( ( at( önace_in( [ "01.7" ] ) )) )) or  at( önace_in( [ "02" ] ) ))))).
förderung("G4c/Grants_Salzburg 2050 Partnerbetriebe", förderkriterien(( at( unternehmenssitz_in( [ "Land-Salzburg" ] ) ) or  at( betriebsstandort_in( [ "Land-Salzburg" ] ) )))).
förderung("G4c/Grants_Mint-Offensive", förderkriterien(( at( unternehmenssitz_in( [ "Land-Salzburg" ] ) ) and at(true)))).
förderung("G4c/Grants_Maßnahmen Zur Ausbildung Und (Höher-)Qualifizierung", förderkriterien(( at( unternehmenssitz_in( [ "Land-Salzburg" ] ) ) and at(true)))).
förderung("G4c/Grants_Beratungskostenzuschuss Für Gastronomie-/Hotelleriebetriebe In Der Steiermark", förderkriterien((( df( "G4c/Grants_Gv.At:Natürliche-Oder-Juristische-Person" )  or  at( rechtsform_in( [ "Offene-Gesellschaft", "Kommanditgesellschaft" ] ) )) and ( at( önace_in( [ "55" ] ) ) or  at( önace_in( [ "56" ] ) )) and ( at( unternehmenssitz_in( [ "Land-Stmk" ] ) ) or  at( betriebsstandort_in( [ "Land-Stmk" ] ) ))))).
förderung("G4c/Grants_Förderung Zur Wirtschaftsinitiative Nachhaltigkeit Steiermark", förderkriterien(( at( unternehmenssitz_in( [ "Land-Stmk" ] ) ) or  at( betriebsstandort_in( [ "Land-Stmk" ] ) )))).
förderung("G4c/Grants_Tiroler Energie- Und Umweltprogramm Ecotirol", förderkriterien( at( mitgliedschaft_in_wirtschaftskammer_in("Land-Tirol") ))).
förderung("G4c/Grants_Umwelt- Und Energieberatungen Vorarlberg", förderkriterien(( at( unternehmenssitz_in( [ "Land-Vbg" ] ) ) or  at( betriebsstandort_in( [ "Land-Vbg" ] ) )))).
förderung("G4c/Grants_Förderung Von Einzelbetrieblichen Investitionen In Der Landwirtschaft Vorarlberg", förderkriterien(( df( "G4c/Grants_Gv.At:Natürliche-Oder-Juristische-Person" )  and ( at( önace_in( [ "01" ] ) ) or  at( önace_in( [ "02" ] ) )) and ( at( unternehmenssitz_in( [ "Land-Vbg" ] ) ) or  at( betriebsstandort_in( [ "Land-Vbg" ] ) ))))).
förderung("G4c/Grants_Oekobusiness Wien", förderkriterien((( at( unternehmenssitz_in( [ "Land-Wien" ] ) ) or  at( betriebsstandort_in( [ "Land-Wien" ] ) )) and ( at( mitgliedschaft_in_wirtschaftskammer_in("Land-Wien") ) or  at( rechtsform_in( [ "In-Gründung" ] ) ))))).
förderung("G4c/Grants_Referenzförderung Für Wiener Arthouse-Kinos", förderkriterien(( at( önace_in( [ "59.14" ] ) ) and (( df( "G4c/Grants_Gv.At:Ist-Juristische-Person" )  and  at( unternehmenssitz_in( [ "Land-Wien" ] ) )) or ( at( rechtsform_in( [ "Offene-Gesellschaft", "Kommanditgesellschaft" ] ) ) and  at( unternehmenssitz_in( [ "Land-Wien" ] ) )) or ( at( rechtsform_in( [ "Einzelunternehmen" ] ) ) and  at( unternehmenssitz_in( [ "Land-Wien" ] ) ))) and at(true) and at(true)))).
förderung("G4c/Grants_Tierzuchtförderung - Barbeihilfen Bei Anschaffung Maschineller Einrichtungen", förderkriterien((( at( rechtsform_in( [ "Einzelunternehmen" ] ) ) and  at( unternehmenssitz_in( [ 20201 ] ) ) and ( at( önace_in( [ "01" ] ) ) or  at( önace_in( [ "02" ] ) ))) or ((( at( rechtsform_in( [ "Genossenschaft" ] ) ) and ( at( önace_in( [ "01" ] ) ) or  at( önace_in( [ "02" ] ) ))) or ( at( rechtsform_in( [ "Verein" ] ) ) and  at( önace_in( [ "01" ] ) ))) and  at( unternehmenssitz_in( [ 20201 ] ) )) or at(false)))).
förderung("G4c/Grants_Tierzuchtförderung - Barbeihilfen Bei Viehverlusten", förderkriterien((( at( rechtsform_in( [ "Einzelunternehmen" ] ) ) and  at( unternehmenssitz_in( [ 20201 ] ) ) and ( at( önace_in( [ "01" ] ) ) or  at( önace_in( [ "02" ] ) ))) or ((( at( rechtsform_in( [ "Genossenschaft" ] ) ) and ( at( önace_in( [ "01" ] ) ) or  at( önace_in( [ "02" ] ) ))) or ( at( rechtsform_in( [ "Verein" ] ) ) and  at( önace_in( [ "01" ] ) ))) and  at( unternehmenssitz_in( [ 20201 ] ) )) or at(false)))).
förderung("G4c/Grants_Tierzuchtförderung - Kostenbeiträge Zu Den Impfkosten Von Weidetieren Villach", förderkriterien((( at( rechtsform_in( [ "Einzelunternehmen" ] ) ) and  at( unternehmenssitz_in( [ 20201 ] ) ) and ( at( önace_in( [ "01" ] ) ) or  at( önace_in( [ "02" ] ) ))) or ((( at( rechtsform_in( [ "Genossenschaft" ] ) ) and ( at( önace_in( [ "01" ] ) ) or  at( önace_in( [ "02" ] ) ))) or ( at( rechtsform_in( [ "Verein" ] ) ) and  at( önace_in( [ "01" ] ) ))) and  at( unternehmenssitz_in( [ 20201 ] ) )) or at(false)))).
förderung("G4c/Grants_Tierzuchtförderung - Anteilige Kostenübernahme Bei Landwirtschaftlichem Wegebau Villach", förderkriterien((( at( rechtsform_in( [ "Einzelunternehmen" ] ) ) and  at( unternehmenssitz_in( [ 20201 ] ) ) and ( at( önace_in( [ "01" ] ) ) or  at( önace_in( [ "02" ] ) ))) or ((( at( rechtsform_in( [ "Genossenschaft" ] ) ) and ( at( önace_in( [ "01" ] ) ) or  at( önace_in( [ "02" ] ) ))) or ( at( rechtsform_in( [ "Verein" ] ) ) and  at( önace_in( [ "01" ] ) ))) and  at( unternehmenssitz_in( [ 20201 ] ) )) or at(false)))).
förderung("G4c/Grants_Innovationsförderung Villach", förderkriterien(( at( unternehmenssitz_in( [ 20201 ] ) )))).
förderung("G4c/Grants_Subventionen Von Bauernblumenwiesen Villach", förderkriterien((( at( unternehmenssitz_in( [ 20201 ] ) ) or  at( betriebsstandort_in( [ 20201 ] ) )) and ( at( önace_in( [ "01" ] ) ) and neg( ( at( önace_in( [ "01.7" ] ) )) ))))).
förderung("G4c/Grants_Förderung Der Umsiedlung Heimischer Insektenvölker", förderkriterien(( at( betriebsstandort_in( [ 20201 ] ) ) or  at( unternehmenssitz_in( [ 20201 ] ) )))).
förderung("G4c/Grants_Umweltschutz- Und Energieeffizienzförderung - Förderung Sonstiger Energieeffizienzmaßnahmen Villach", förderkriterien(( df( "G4c/Grants_Gv.At:Natürliche-Oder-Juristische-Person" )  and ( at( unternehmenssitz_in( [ 20201 ] ) ) or  at( betriebsstandort_in( [ 20201 ] ) ))))).
förderung("G4c/Grants_Allgemeine Investitionsförderung Villach", förderkriterien((( df( "G4c/Grants_Gv.At:Natürliche-Oder-Juristische-Person" )  or  at( rechtsform_in( [ "Offene-Gesellschaft", "Kommanditgesellschaft" ] ) )) and  at( mitgliedschaft_in_wirtschaftskammer_in("Land-Kärnten") ) and ( at( unternehmenssitz_in( [ 20201 ] ) ) or  at( betriebsstandort_in( [ 20201 ] ) ))))).
förderung("G4c/Grants_Förderung Frauenspezifischer Beratungseinrichtungen Villach", förderkriterien(( at( betriebsstandort_in( [ 20201 ] ) ) or  at( unternehmenssitz_in( [ 20201 ] ) )))).
förderung("G4c/Grants_Subventionen An Soziale Einrichtungen, Vereine Und Verbände Villach", förderkriterien((( df( "G4c/Grants_Gv.At:Natürliche-Oder-Juristische-Person" )  or  at( rechtsform_in( [ "Verein" ] ) )) and  at( unternehmenssitz_in( [ 20201 ] ) )))).
förderung("G4c/Grants_Standort- Und Infrastrukturunterstützungen Villach", förderkriterien(( at( unternehmenssitz_in( [ 20201 ] ) ) or  at( betriebsstandort_in( [ 20201 ] ) )))).
förderung("G4c/Grants_Umweltförderung - Lastenfahrräder Graz", förderkriterien(( at( unternehmenssitz_in( [ 60101 ] ) ) or  at( betriebsstandort_in( [ 60101 ] ) )))).
förderung("G4c/Grants_Umweltförderung - Fahrradabstellanlagen Graz", förderkriterien(( at( unternehmenssitz_in( [ 60101 ] ) ) or  at( betriebsstandort_in( [ 60101 ] ) )))).
förderung("G4c/Grants_Umweltförderung - Fahrradserviceboxen Graz", förderkriterien(( at( unternehmenssitz_in( [ 60101 ] ) ) or  at( betriebsstandort_in( [ 60101 ] ) )))).
förderung("G4c/Grants_Klima-Euro Für Bezirke Der Stadt Graz", förderkriterien(( at( unternehmenssitz_in( [ 60101 ] ) ) or  at( betriebsstandort_in( [ 60101 ] ) )))).
förderung("G4c/Grants_Alternative Betriebsmittel Für Landwirtschaftliche Betriebe Graz", förderkriterien(( at( önace_in( [ "01" ] ) ) and neg( ( at( önace_in( [ "01.7" ] ) )) ) and  at( unternehmenssitz_in( [ 60101 ] ) )))).
förderung("G4c/Grants_Arbeitsplatzförderung Gratkorn", förderkriterien( df( "G4c/Grants_Grants/Per-Gkz/60613-Gratkorn:Allgemeine-Voraussetzungen-Gratkorn" ) )).
förderung("G4c/Grants_Gründer*Innenförderung Gratkorn", förderkriterien( df( "G4c/Grants_Grants/Per-Gkz/60613-Gratkorn:Allgemeine-Voraussetzungen-Gratkorn" ) )).
förderung("G4c/Grants_Immaterielle Förderung Gratkorn", förderkriterien( df( "G4c/Grants_Grants/Per-Gkz/60613-Gratkorn:Allgemeine-Voraussetzungen-Gratkorn" ) )).
förderung("G4c/Grants_Humanpotenzial", förderkriterien( df( "G4c/Grants_Ffg:Allgemeine-Voraussetzungen" ) )).
förderung("G4c/Grants_Kooperationsstrukturen", förderkriterien( df( "G4c/Grants_Ffg:Allgemeine-Voraussetzungen" ) )).
förderung("G4c/Grants_Life Sciences", förderkriterien( df( "G4c/Grants_Ffg:Allgemeine-Voraussetzungen" ) )).
förderung("G4c/Grants_Produktionstechnologien", förderkriterien( df( "G4c/Grants_Ffg:Allgemeine-Voraussetzungen" ) )).
förderung("G4c/Grants_Weltraum", förderkriterien( df( "G4c/Grants_Ffg:Allgemeine-Voraussetzungen" ) )).
förderung("G4c/Grants_Mobilitätssystem", förderkriterien( df( "G4c/Grants_Ffg:Allgemeine-Voraussetzungen" ) )).
förderung("G4c/Grants_Digitale Technologien", förderkriterien( df( "G4c/Grants_Ffg:Allgemeine-Voraussetzungen" ) )).
förderung("G4c/Grants_Energie- Und Umwelttechnologien", förderkriterien( df( "G4c/Grants_Ffg:Allgemeine-Voraussetzungen" ) )).
subrule("G4c/Grants_Gv.At:Ist-Juristische-Person", förderkriterien( at( rechtsform_in( [ "Genossenschaft", "Verein", "Versicherungsverein-Auf-Gegenseitigkeit", "Kleiner-Versicherungsverein", "Gemeinnützige-Stiftung", "Landesgesetzlich-Eingerichtete-Stiftung-Oder-Fonds", "Bundesgesetzlich-Eingerichtete-Gemeinnützige-Stiftung", "Privatstiftung", "Kapitalgesellschaft", "Aktiengesellschaft", "Gesellschaft-Mit-Beschränkter-Haftung", "Europäische-Gesellschaft", "Europäische-Genossenschaft", "Agrargemeinschaft", "Öffentlich-Rechtliche-Körperschaft", "Sparkasse" ] ) ))).
subrule("G4c/Grants_Gv.At:Natürliche-Oder-Juristische-Person", förderkriterien(( at( rechtsform_in( [ "Einzelunternehmen" ] ) ) or  df( "G4c/Grants_Gv.At:Ist-Juristische-Person" ) ))).
subrule("G4c/Grants_Gv.At:Ist-Unternehmen", förderkriterien( at( rechtsform_in( [ "Genossenschaft", "Kapitalgesellschaft", "Aktiengesellschaft", "Gesellschaft-Mit-Beschränkter-Haftung", "Europäische-Gesellschaft", "Europäische-Genossenschaft", "Sparkasse" ] ) ))).
subrule("G4c/Grants_Grants/Per-Gkz/60613-Gratkorn:Allgemeine-Voraussetzungen-Gratkorn", förderkriterien((( at( rechtsform_in( [ "Einzelunternehmen" ] ) ) or  df( "G4c/Grants_Gv.At:Ist-Juristische-Person" ) ) and  at( unternehmenssitz_in( [ 60613 ] ) ) and neg( (( at( önace_in( [ "92" ] ) ) or  at( önace_in( [ "96.09" ] ) ) or ( at( önace_in( [ "47", "45.11-2", "46", "45.31", "45.11-1" ] ) ) or ( at( önace_in( [ "68.3" ] ) ))))) )))).
subrule("G4c/Grants_Ffg:Allgemeine-Voraussetzungen", förderkriterien(( df( "G4c/Grants_Gv.At:Natürliche-Oder-Juristische-Person" )  and ( at( unternehmenssitz_in( [ "Land-Bgld", "Land-Kärnten", "Land-Nö", "Land-Oö", "Land-Salzburg", "Land-Stmk", "Land-Tirol", "Land-Vbg", "Land-Wien" ] ) ) or  at( betriebsstandort_in( [ "Land-Bgld", "Land-Kärnten", "Land-Nö", "Land-Oö", "Land-Salzburg", "Land-Stmk", "Land-Tirol", "Land-Vbg", "Land-Wien" ] ) )) and neg( ( at( rechtsform_in( [ "Gesellschaft-Mit-Beschränkter-Haftung" ] ) )) ) and at(true) and at(true)))).
