Require Import Coq.Strings.String.
Require Import Records.Records.
Require Import Records.Notation.

Definition foo : {@ ("x" %e nat) @} :=
  {# "x" :- 3 #}%record.

Definition foo_ext : {@ ("x" %e nat) , ("y" %e bool) @} :=
  {# "x" :- 3 ; "y" :- true #}.

Definition bar :=
  {# "x" :- 3 ; "y" :- true #}.

Definition bar' :=
  {# bar with "x" :- 4 #}%record.

Goal (bar' !! "x"%string) = 4.
Proof.
  reflexivity.
Defined.

Goal {# "x" :- 3 ; "y" :- true #} = {# "y" :- true ; "x" :- 3 #}.
Proof.
  reflexivity.
Defined.