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
Notation "[ ]" := FSnil : fields_scope.
Notation "[ x , .. , y ]" := (FScons x%field_decl .. (FScons y%field_decl FSnil) .. ) : fields_scope.
Notation "x '%e' y" := (@pair field Type x%string y%type) (at level 0) : field_decl_scope.
Notation "{{ x , .. , y }}" := (record (Fields (FScons x%field_decl .. (FScons y%field_decl FSnil) .. ))) : type_scope.

Arguments Fields fs%fields : rename.