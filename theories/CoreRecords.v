Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.BinNums.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.

Local Open Scope positive.

Monomorphic Definition field : Type := positive.

Section poly.
  Universe U.

  Inductive fields : Type :=
  | pm_Leaf : fields
  | pm_Branch : fields -> option Type@{U} -> fields -> fields.

  Fixpoint fields_insert (p : field) (t : Type@{U}) (m : fields) {struct p} : fields :=
    match p with
      | xH => pm_Branch match m with
                          | pm_Leaf => pm_Leaf
                          | pm_Branch l _ _ => l
                        end
                        (Some t)
                        match m with
                          | pm_Leaf => pm_Leaf
                          | pm_Branch _ _ r => r
                        end
      | xO p' =>
        pm_Branch (fields_insert p' t match m with
                                      | pm_Leaf => pm_Leaf
                                      | pm_Branch l _ _ => l
                                      end)
                  match m with
                    | pm_Leaf => None
                    | pm_Branch _ v _ => v
                  end
                  match m with
                    | pm_Leaf => pm_Leaf
                    | pm_Branch _ _ r => r
                  end
      | xI p' =>
        pm_Branch match m with
                    | pm_Leaf => pm_Leaf
                    | pm_Branch l _ _ => l
                  end
                  match m with
                    | pm_Leaf => None
                    | pm_Branch _ v _ => v
                  end
                  (fields_insert p' t match m with
                                 | pm_Leaf => pm_Leaf
                                 | pm_Branch _ _ r => r
                               end)
    end.

  Fixpoint fields_get (p : field) (m : fields) {struct p} : option Type@{U} :=
    match p with
      | xH => match m with
                | pm_Leaf => None
                | pm_Branch _ x _ => x
              end
      | xO p' => fields_get p' match m with
                               | pm_Leaf => pm_Leaf
                               | pm_Branch L _ _ => L
                             end
      | xI p' => fields_get p' match m with
                               | pm_Leaf => pm_Leaf
                               | pm_Branch _ _ R => R
                             end
    end.

  Definition fields_leaf : fields := pm_Leaf.
  Definition fields_singleton (p : field) (t : Type) : fields :=
    fields_insert p t fields_leaf.

  Inductive member (val : Type@{U}) : fields -> Type :=
  | pmm_H : forall L R, member val (pm_Branch L (Some val) R)
  | pmm_L : forall V L R, member val L -> member val (pm_Branch L V R)
  | pmm_R : forall V L R, member val R -> member val (pm_Branch L V R).
  Arguments pmm_H {_ _ _}.
  Arguments pmm_L {_ _ _ _} _.
  Arguments pmm_R {_ _ _ _} _.

  Fixpoint get_member val p {struct p}
  : forall m, fields_get p m = Some val -> member val m :=
    match p as p return forall m, fields_get p m = Some val -> member val m with
      | xH => fun m =>
        match m as m return fields_get xH m = Some val -> member val m with
        | pm_Leaf => fun pf : None = Some _ =>
                       match pf in _ = Z return match Z with
                                                | Some _ => _
                                                | None => unit
                                                end
                       with
                       | eq_refl => tt
                       end
        | pm_Branch _ None _ => fun pf : None = Some _ =>
                                  match pf in _ = Z return match Z with
                                                           | Some _ => _
                                                           | None => unit
                                                           end
                                  with
                                  | eq_refl => tt
                                  end
        | pm_Branch _ (Some x) _ => fun pf : Some x = Some val =>
                                      match eq_sym pf in _ = Z return member val (pm_Branch _ Z _) with
                                      | eq_refl => pmm_H
                                      end
        end
      | xO p' => fun m =>
        match m as m return fields_get (xO p') m = Some val -> member val m with
        | pm_Leaf => fun pf : fields_get p' pm_Leaf = Some val =>
                       @get_member _ p' pm_Leaf pf
        | pm_Branch l _ _ => fun pf : fields_get p' l = Some val =>
                       @pmm_L _ _ _ _ (@get_member _ p' l pf)
        end
      | xI p' => fun m =>
        match m as m return fields_get (xI p') m = Some val -> member val m with
        | pm_Leaf => fun pf : fields_get p' pm_Leaf = Some val =>
                       @get_member _ p' pm_Leaf pf
        | pm_Branch l _ r => fun pf : fields_get p' r = Some val =>
                               @pmm_R _ _ _ _ (@get_member _ p' r pf)
        end
    end.

  Inductive record : fields -> Type :=
  | pr_Leaf : record pm_Leaf
  | pr_Branch : forall L R (V : option Type@{U}),
      record L ->
      match V return Type@{U} with
        | None => unit
        | Some t => t
      end ->
      record R ->
      record (pm_Branch L V R).

  Definition record_left {L} {V : option Type@{U}} {R}
             (r : record (pm_Branch L V R)) : record L :=
    match r in record z
          return match z with
                 | pm_Branch L _ _ => record L
                 | _ => unit
                 end
    with
      | pr_Branch _ l _ _ => l
      | pr_Leaf => tt
    end.

  Definition record_at {L} {V : option Type@{U}} {R} (r : record (pm_Branch L V R))
  : match V with
    | None => unit
    | Some t => t
    end :=
    match r in record z
          return match z with
                 | pm_Branch _ V _ => match V return Type@{U} with
                                     | None => unit
                                     | Some t => t
                                     end
                 | _ => unit
                 end
    with
      | pr_Branch _ _ v _ => v
      | pr_Leaf => tt
    end.

  Definition record_here {L v R} (r : record (pm_Branch L (Some v) R)) : v :=
    match r in record z
          return match z return Type@{U} with
                 | pm_Branch _ (Some v) _ => v
                 | _ => unit
                 end
    with
      | pr_Branch _ _ v _ => v
      | pr_Leaf => tt
    end.


  Definition record_right {L V R} (r : record (pm_Branch L V R)) : record R :=
    match r in record z return match z with
                                  | pm_Branch _ _ R => record R
                                  | _ => unit
                                end
    with
      | pr_Branch _ _ _ r => r
      | pr_Leaf => tt
    end.

  Fixpoint record_get {val} {pm : fields} (m : member val pm) : record pm -> val :=
    match m in member _ pm return record pm -> val with
      | pmm_H => fun r => record_here r
      | pmm_L m' => fun r => record_get m' (record_left r)
      | pmm_R m' => fun r => record_get m' (record_right r)
    end.

  Fixpoint record_set {val} {pm : fields} (m : member val pm) (x : val) {struct m}
  : record pm -> record pm :=
    match m in member _ pm return record pm -> record pm with
    | pmm_H => fun r =>
      pr_Branch (Some _)
                (record_left r)
                x
                (record_right r)
    | pmm_L m' => fun r =>
      pr_Branch _
                (record_set m' x (record_left r))
                (record_at r)
                (record_right r)
    | pmm_R m' => fun r =>
      pr_Branch _ (record_left r)
                (record_at r)
                (record_set m' x (record_right r))
    end.

  Definition record_empty : record pm_Leaf := pr_Leaf.
  Fixpoint record_singleton {T} (p : field) (val : T) {struct p}
  : record (fields_singleton p T) :=
    match p as p return record (fields_singleton p T) with
    | xH => pr_Branch (Some T) pr_Leaf val pr_Leaf
    | xI p' =>
      pr_Branch
        match fields_leaf with
        | pm_Leaf => None
        | pm_Branch _ v _ => v
        end pr_Leaf tt (record_singleton p' val)
    | xO p0 =>
      pr_Branch
        match fields_leaf with
        | pm_Leaf => None
        | pm_Branch _ v _ => v
        end (record_singleton p0 val) tt pr_Leaf
    end.

  Fixpoint disjoint (a b : fields) : bool :=
    match a , b with
    | pm_Leaf , _ => true
    | _ , pm_Leaf => true
    | pm_Branch aL None aR , pm_Branch bL _ bR =>
      disjoint aL bL && disjoint aR bR
    | pm_Branch aL _ aR , pm_Branch bL None bR =>
      disjoint aL bL && disjoint aR bR
    | pm_Branch _ (Some _) _ , pm_Branch _ (Some _) _ => false
    end%bool.

  Fixpoint fields_join (a b : fields) : fields :=
    match a with
    | pm_Leaf => b
    | pm_Branch aL aV aR =>
      match b with
      | pm_Leaf => a
      | pm_Branch bL bV bR =>
        pm_Branch (fields_join aL bL)
                  match aV with
                  | None => bV
                  | Some X => aV
                  end
                  (fields_join aR bR)
      end
    end.

  Fixpoint Rjoin {l r : fields} (L : record l) {struct L}
  : record r -> record (fields_join l r) :=
    match L in record l return record r -> record (fields_join l r) with
      | pr_Leaf => fun v => v
      | @pr_Branch l' r' v lL lV lR => fun R =>
        match R in record r return record (fields_join (pm_Branch l' v r') r) with
          | pr_Leaf => @pr_Branch l' r' v lL lV lR
          | @pr_Branch rl' rr' rv rL rV rR =>
            let val' :=
                match v as o return match o with
                                      | Some t => t
                                      | None => unit
                                    end ->
                                    match match o with
                                            | Some _ => o
                                            | None => rv
                                          end with
                                      | Some t => t
                                      | None => unit
                                    end
                with
                  | Some t => fun lV0 : t => lV0
                  | None => fun _ : unit => rV
                end lV
            in
            @pr_Branch (fields_join l' rl') (fields_join r' rr') _
                       (Rjoin lL rL) val' (Rjoin lR rR)
        end
    end.

Definition bool_to_p (x : bool) : positive -> positive :=
  match x with
    | true => xI
    | false => xO
  end.

Section localized.
  Local Notation "x >> y" := (bool_to_p x y) (at level 30, right associativity).

  Definition ascii_to_p (x : ascii) (p : positive) : positive :=
    match x with
      | Ascii a b c d e f g h =>
        a >> b >> c >> d >> e >> f >> g >> h >> p
    end.
End localized.

Fixpoint string_to_p (s : string) : field :=
  match s with
    | EmptyString => 1
    | String asc rst => ascii_to_p asc (string_to_p rst)
  end%positive.

Inductive FieldSpec : Type :=
| FSnil : FieldSpec
| FScons : (field * Type) -> FieldSpec -> FieldSpec.

Coercion string_to_p : string >-> field.

Fixpoint Fields (ls : FieldSpec) : fields :=
  match ls with
  | FSnil => pm_Leaf
  | FScons (f, t) ls =>
    fields_insert f t (Fields ls)
  end.

End poly.