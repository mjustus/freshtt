freshtt
=======

A type checker for [FreshMLTT][PittsMatthiesenDerickx2014], a dependent type
theory with abstractable names together with an equational characterisation of
freshness inspired by the corresponding notion in [Nominal
Sets][GabbayPitts2002].

Usage
-----

    freshtt FILE

Syntax
------

A file consists of a semicolon-separated list of definitions

    DEF_1;
    ...  ;
    DEF_n

where each definition `DEFi` consists of a name (that later definitions can
refer to) a type and a body (of that type):

    ID : TERM = TERM

There's no syntactic distinction between types and terms.  Terms are formed as
follows

* local definitions

        let ID : TERM = TERM in TERM

* cumulative hierarchy of universes

        U n

    where `n` is an integer

* universe of name sorts

        N

* simple and dependent function types

        TERM -> TERM
        (ID1, ..., IDn : TERM) -> TERM

    The arrow `->` can be replaced by the unicode right arrow character, `→`.

* simple and dependent name abstraction types

        [ID1, ..., IDn : TERM] -> TERM
        [TERM] TERM

* function abstraction (domain-free)

        \ID1 ... IDn. TERM
        λID1 ... IDn. TERM

* name abstraction (domain-free)

        !ID1 ... IDn. TERM
        αID1 ... IDn. TERM


* local name abstraction (domain-full)

        ?ID : TERM. TERM
        νID : TERM. TERM

* function application

        TERM TERM

* concretion

        TERM @ ID

* name swapping

        swap ID ID in TERM

* type annotation

        TERM :: TERM

Some syntactic sugar:

* Telescopic type syntax: consecutive dependent function and name abstractions
  can be written without a separating arrow (`->`), i.e. instead of

        (ID : TERM) -> [ID : TERM] -> ...

    we can write

        (ID : TERM) [ID : TERM] -> ...


Hacking
-------

* `parser.mly`: parser for *freshtt* programs
* `raw.ml`: abstract syntax close to concrete syntax and a pretty-printer
* `term.ml`: internal syntax (note that `Fun` and `Nab` are non-binding!)
* `eval.ml` and `readback.ml`: [NbE-style normalisation][Abel2013]
  procedure. In particular, `eval` performs weak-head normalisation and
  `rb_nf` eta expands and reduction under alpha- and lambda-abstractions.
* `model.ml`: values in the NbE model. Alpha- and lambda-abstractions are
  represented by `Term.t` closures.
* `normal.ml`: normal forms
* `check.ml`: [bidirectional type checker][Coquand1996]

References
----------

1. A. Abel, [Normalization by Evaluation: Dependent Types and Impredicativity][Abel2013].
2. T. Coquand, [An algorithm for type-checking dependent types][Coquand1996].
3. M. J. Gabbay, A. M. Pitts, [A New Approach to Abstract Syntax with Variable Binding][GabbayPitts2002].
4. A. M. Pitts, J. Matthiesen and J. Derikx, [A Dependent Type Theory with Abstractable Names][PittsMatthiesenDerickx2014].

[Abel2013]: <http://www2.tcs.ifi.lmu.de/~abel/publications.html#habil> (A. Abel, Normalization by Evaluation: Dependent Types and Impredicativity.)
[Coquand1996]: <http://www.cse.chalmers.se/~coquand/type.ps> (T. Coquand, An algorithm for type-checking dependent types.)
[GabbayPitts2002]: <https://www.cl.cam.ac.uk/~amp12/papers/#newaas-jv> (M. J. Gabbay, A. M. Pitts, A New Approach to Abstract Syntax with Variable Binding.)
[PittsMatthiesenDerickx2014]: <https://www.cl.cam.ac.uk/~amp12/papers/#deptta> (A. M. Pitts, J. Matthiesen and J. Derikx, A Dependent Type Theory with Abstractable Names.)

