Require Import Coq.Strings.String.
Require Import Records.Records.

Definition foo_empty : {@ @} := {# #}.

Definition foo : {@ ("x" %e nat) @} :=
  {# "x" :- 3 #}%record.

Definition foo_ext : {@ ("x" %e nat) , ("y" %e bool) @} :=
  {# "x" :- 3 ; "y" :- true #}.

Definition bar :=
  {# "x" :- 3 ; "y" :- true #}.

Definition bar' :=
  {# bar with "x" :- 4 #}%record.

Definition bar'' :=
  {# bar with "x" :- 4 ; "y" :- false #}%record.
Set Printing Universes.

Goal (bar' !! "x"%string) = 4.
Proof.
  reflexivity.
Defined.

Goal {# "x" :- 3 ; "y" :- true #} = {# "y" :- true ; "x" :- 3 #}.
Proof.
  reflexivity.
Defined.

(* Records in Records *)
Definition nested : {@ ("x" %e {@ "y" %e nat @}) @} :=
  {# "x" :- {# "y" :- 3 #} #}.