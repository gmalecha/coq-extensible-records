Require Import Coq.Strings.String.
Require Import Records.Records.

Definition foo : {{ ("x" %e nat) }} :=
  record_singleton ("x")%string 3%nat.

Definition foo_ext : {{ ("x" %e nat) , ("y" %e bool) }} :=
  Rjoin (record_singleton ("x")%string 3%nat)
        (record_singleton ("y")%string true).