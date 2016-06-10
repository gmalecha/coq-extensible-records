Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.BinNums.
Require Import Records.Records.

Set Implicit Arguments.
Set Strict Implicit.

Delimit Scope fields_scope with fields.
Delimit Scope field_decl_scope with field_decl.
Delimit Scope field_scope with field.

Bind Scope field_scope with field.

Notation "x '%e' y" :=
  (@pair field Type x%string y%type) (at level 0) : field_decl_scope.

Notation "{@ x , .. , y @}" :=
  (record (Fields (FScons x%field_decl .. (FScons y%field_decl FSnil) .. ))) : type_scope.

Delimit Scope record_field_assign_scope with record_field_assign.
Delimit Scope record_scope with record.

Notation "x ':-' y" :=
  (@record_singleton _ x%string y) (at level 20) : record_field_assign_scope.

Notation "{# r 'with' a ; .. ; b #}" :=
  (@Rjoin _ _ a%record_field_assign .. (@Rjoin _ _ b%record_field_assign r) ..) : record_scope.

Notation "{#  x ; .. ; y  #}" :=
  (@Rjoin _ _ x%record_field_assign .. (@Rjoin _ _ y%record_field_assign record_empty) ..).

Definition Rget {fs : fields} (r : record fs) (f : field) {T}
           (pf : fields_get f fs = Some T) : T :=
  record_get (get_member _ fs pf) r.

Notation "r !! f" :=
  (@Rget _ r%record f%string _ ltac:(simpl; exact eq_refl)) (at level 30).


Arguments Fields fs%fields : rename.