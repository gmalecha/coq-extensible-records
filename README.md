coq-extensible-records
======================

Implementation of extensible records in Coq. These records use string
keys and have a canonical representation allowing you to state
equality of two records using standard equality (see examples/Demo.v).

Usage
-----

The type of extensible records is ```record``` (defined in CoreRecord), but the library Notation provides *reasonable* (but not ideal) syntax for them.

    {@ @}               (* empty record *)
    {@ ("x" %e nat) @}  (* record with a single field "x" of type nat *)
    {@ ("x" %e nat) , ("y" %e bool) @} (* "x" is a nat, "y" is a bool *)

Record values are defined using ```{# #}```.

    {# #} : {@ @}
    {# "x" :- 3 #} : {@ ("x" %e nat) @}
    {# "x" :- 3 ; "y" :- true #} : {@ ("x" %e nat) , ("y" %e bool) @}

Note: Some records may need annotations for record scope, i.e. add %record as in

    {# "x" :- 3 #}%record : {@ ("x" %e nat) @}

Records also support 'with' notation.

    {# bar with "x" :- 4 #}
    {# bar with "x" :- 4 ; "y" :- false #}

All of these operations are completely definitional

    Goal ({# "x" :- 3 ; "y" :- true #} !! "x"%string) = 3.
    Proof.
      reflexivity.
    Defined.

    Goal {# "x" :- 3 ; "y" :- true #} = {# "y" :- true ; "x" :- 3 #}.
    Proof.
      reflexivity.
    Defined.

Bugs
----

If you find a bug or have an enhancement suggestion, please report it on github: https://github.com/gmalecha/coq-extensible-records/issues

Install with OPAM
-----------------
Run:

    opam install coq-extensible-records

See http://coq.io/opam/ for opam configuration
