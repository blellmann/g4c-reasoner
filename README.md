# g4c-reasoner

Reasoning with Grants4Companies

*g4c-reasoner* is an implementation of a sequent system for reasoning
with formalised grant conditions of Austrian business grants. It is
part of a PoC-implementation of novel features for the application
*Grants4Companies* in the Austrian [Business Service
Portal](https://www.usp.gv.at/en/index.html).

*g4c-reasoner* is written in [Scryer Prolog](https://www.scryer.pl), a
strongly ISO-conformant and freely available Prolog implementation.


## Usage

You can run *g4c-reasoner* locally or using the [Scryer
Playground](https://play.scryer.pl).


### Running *g4c-reasoner* locally

To run *g4c-reasoner* locally, make sure you have Scryer Prolog
installed (see the [Scryer Prolog website](https://www.scryer.pl) for
information on how to do this). Download the file
*g4c-reasoner-complete.pl* from this repository and load it in Scryer
Prolog, e.g. via:

> `?- ['g4c-reasoner-complete'].`

(this assumes that you are in the directory containing the file). Now
you are ready to enter your queries (also see the example queries below).


### Running *g4c-reasoner* via the Scryer Playground

To run *g4c-reasoner* via the Scryer Playground, first download the file
*g4c-reasoner-complete.pl* from this repository and open it in a text
editor of your choice. Then head over to the [Scryer
Playground](https://play.scryer.pl). Copy the whole contents of
*g4c-reasoner-complete.pl* into the area on the left hand side of the
Scryer Playground.

You can enter your queries in the area on the right hand side of the
Scryer Playground and execute them via the "Execute!" button. See also
below for example queries.


### Example Queries

To show grants with their formalised grant conditions, execute

> `?- förderung(Name, Condition).`

To show pairs of grants where the conditions of the first imply the
conditions of the second, execute

> `?- förderung(F1, förderkriterien(K1)), förderung(F2, förderkriterien(K2)), dif(K1,K2), prov2([K1] => [K2], Tree).`

The term instantiating the variable `Tree` represents the sequent derivation.

To show pairs of grants where the conditions of the first imply the
conditions of the second and to print a string representing the
derivation in (formalised) natural language, execute

> `?- förderung(F1, förderkriterien(K1)), förderung(F2, förderkriterien(K2)), dif(K1,K2), prove_and_print([K1] => [K2]).`

The string is printed on the standard output. In case you are running
this query in the Scryer Playground, you might want to copy the output
(the string starting with `<!DOCTYPE html>` and ending with `</html>`)
into a temporary file an open this in a browser.


### More details

*g4c-reasoner* uses the following **data structures**:

**Formulae** are defined via the following grammar in BNF:

> `Fml ::= at(Atom) | at(false) | at(true) | Fml and Fml | Fml or Fml |`
> `Fml -> Fml | and(List) | or(List) | neg(Fml)`

where

- `Atom` is an atomic statement
- `List` is a list of formulae

Examples of atomic statements are:

- `rechtsform_in(List)` where `List` is a list of strings
- `unternehmenssitz_in(List)` where `List` is a list of Austrian
  municipality codes (max 5-digit numbers)
- `betriebsstandort_in(List)` where `List` is a list of Austrian
  municipality codes (max 5-digit numbers)
- `önace_in(List)` where `List` is a list of Austrian ÖNACE-codes for
  the economic activity (max 5-digit numbers)
- `mitgliedschaft_in_wirtschaftskammer_in(List)` where `List` is a
  list of Austrian municipality codes or codes for counties
  ("Land-Bgld", "Land-Kärnten", "Land-Nö", "Land-Oö", "Land-Salzburg",
  "Land-Stmk", "Land-Tirol", "Land-Vbg", "Land-Wien")


**Sequents** are structures of the form

> `seq(Gamma,Delta)`
> `Gamma => Delta`

where `Gamma` and `Delta` are lists of formulae.


**Derivation trees** are trees constructed using the constructor `der`
with the following arguments:

> `der(Rule_name, Conclusion, Principal_formula, Premisses)`

where 

- `Rule_name` is the name of the applied rule
- `Conclusion` is the conclusion of the rule application
- `Principal_formula` is the principal formula of the rule application
- `Premisses` is the list of derivations of the premisses of the rule application, i.e., the list of successor nodes.


The main predicate is `prov2`, which can be used to search for a
derivation for an implication between two formulae `F1` and `F2` via:

> `?- prov2([F1] => [F2], Tree).`

E.g., to check whether the formula `neg at(b) and ( at(a) -> at(b) )`
implies the formula `neg at(a)`, run

> `?- prov2([neg at(b) and ( at(a) -> at(b) )] => [neg at(a)], Tree).`

If this query is successful, the instantiation of the variable `Tree`
will represent the derivation.


The derivations can also be output in formalised natural language. The
main predicate for this is `prove_and_print`, which takes a sequent as
argument. E.g., running the query

> `?- prove_and_print([neg at(b) and ( at(a) -> at(b) )] => [neg at(a)]).`

searches for a derivation of the sequent `[neg at(b) and ( at(a) ->
at(b) )] => [neg at(a)]` and outputs an html-string with the
explanation on std-out. If you run *g4c-reasoner* locally, you may
also run, e.g., 

> `?- prov2(Seq,Tree), phrase_to_file(pp_result(Tree), 'output.hml').`

to print the explanation directly to the file `output.html`.
