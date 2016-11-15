Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Numbers.BinNums.

Set Implicit Arguments.
Set Strict Implicit.
Set Universe Polymorphism.
Set Printing Universes.

Local Open Scope positive.

Monomorphic Definition field : Type := positive.

Section poly.
  Universe U.

  Inductive fields : Type :=
  | pm_Leaf : fields
  | pm_Branch : fields -> option Type@{U} -> fields -> fields.

  Definition fields_left (f : fields) : fields :=
    match f with
    | pm_Leaf => pm_Leaf
    | pm_Branch l _ _ => l
    end.

  Definition fields_right (f : fields) : fields :=
    match f with
    | pm_Leaf => pm_Leaf
    | pm_Branch _ _ r => r
    end.

  Definition fields_here (f : fields) : option Type@{U} :=
    match f with
    | pm_Leaf => None
    | pm_Branch _ s _ => s
    end.

  Fixpoint fields_insert (p : field) (t : Type@{U}) (m : fields) {struct p} : fields :=
    match p with
      | xH => pm_Branch match m with
                          | pm_Leaf => pm_Leaf
                          | pm_Branch l _ _ => l
                        end
                        (@Some Type@{U} t)
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
  | pmm_L : forall (V : option Type@{U}) L R, member val L -> member val (pm_Branch L V R)
  | pmm_R : forall (V : option Type@{U}) L R, member val R -> member val (pm_Branch L V R).
  Arguments pmm_H {_ _ _}.
  Arguments pmm_L {_ _ _ _} _.
  Arguments pmm_R {_ _ _ _} _.

  Fixpoint get_member (val : Type@{U}) p {struct p}
  : forall m, fields_get p m = @Some Type@{U} val -> member val m :=
    match p as p return forall m, fields_get p m = @Some Type@{U} val -> member@{U} val m with
      | xH => fun m =>
        match m as m return fields_get xH m = @Some Type@{U} val -> member@{U} val m with
        | pm_Leaf => fun pf : None = @Some Type@{U} _ =>
                       match pf in _ = Z return match Z with
                                                | Some _ => _
                                                | None => unit
                                                end
                       with
                       | eq_refl => tt
                       end
        | pm_Branch _ None _ => fun pf : None = @Some Type@{U} _ =>
                                  match pf in _ = Z return match Z with
                                                           | Some _ => _
                                                           | None => unit
                                                           end
                                  with
                                  | eq_refl => tt
                                  end
        | pm_Branch _ (Some x) _ => fun pf : @Some Type@{U} x = @Some Type@{U} val =>
                                      match eq_sym pf in _ = Z return member@{U} val (pm_Branch _ Z _) with
                                      | eq_refl => pmm_H
                                      end
        end
      | xO p' => fun m =>
        match m as m return fields_get (xO p') m = @Some Type@{U} val -> member@{U} val m with
        | pm_Leaf => fun pf : fields_get p' pm_Leaf = @Some Type@{U} val =>
                       @get_member _ p' pm_Leaf pf
        | pm_Branch l _ _ => fun pf : fields_get p' l = @Some Type@{U} val =>
                       @pmm_L _ _ _ _ (@get_member _ p' l pf)
        end
      | xI p' => fun m =>
        match m as m return fields_get (xI p') m = @Some Type@{U} val -> member@{U} val m with
        | pm_Leaf => fun pf : fields_get p' pm_Leaf = @Some Type@{U} val =>
                       @get_member _ p' pm_Leaf pf
        | pm_Branch l _ r => fun pf : fields_get p' r = @Some Type@{U} val =>
                               @pmm_R _ _ _ _ (@get_member _ p' r pf)
        end
    end.


  Inductive record (f : fields) : Type@{U} :=
  | pr_Leaf' : f = pm_Leaf -> record f
  | pr_Branch' : (* forall L R (V : option Type@{U}), *)
      record (fields_left f) ->
      match f return Type@{U} with
      | pm_Leaf => Empty_set
      | _ =>
        match fields_here f return Type@{U} with
        | None => unit
        | Some t => t
        end
      end ->
      record (fields_right f) ->
      record f.

  Definition pr_Leaf : record pm_Leaf := pr_Leaf' eq_refl.
  Definition pr_Branch {L : fields} {V : option Type@{U}} {R : fields}
             (l : record L) (v : match V return Type@{U} with
                                 | None => unit
                                 | Some t => t
                                 end)
             (r : record R)
   : record (pm_Branch L V R) :=
     pr_Branch' (pm_Branch L V R) l v r.

  Definition pr_BranchSome {L : fields} {V : Type@{U}} {R : fields}
             (l : record L) (v : V)
             (r : record R)
   : record (pm_Branch L (@Some Type@{U} V) R) :=
     pr_Branch' (pm_Branch L (@Some Type@{U} V) R) l v r.

  Definition pr_BranchNone {L R : _}
             (l : record L)
             (r : record R)
   : record (pm_Branch L (@None Type@{U}) R) :=
     pr_Branch' (pm_Branch L (@None Type@{U}) R) l tt r.

  Definition record_elim {fs : fields} (r : record fs) (T : fields -> Type)
             (empty : T pm_Leaf)
             (branch : forall l v r, record l -> match v return Type@{U} with
                                           | None => unit
                                           | Some t => t
                                           end -> record r -> T (pm_Branch l v r))
  : T fs :=
    match r with
    | pr_Leaf' pf => match pf in _ = Z return T Z -> T _ with
                    | eq_refl => fun x => x
                    end empty
    | pr_Branch' _ l v r =>
      match fs as fs
            return record (fields_left fs) ->
                   match fs return Type@{U} with
                   | pm_Leaf => Empty_set
                   | pm_Branch _ _ _ => match fields_here fs return Type@{U} with
                                       | Some t => t
                                       | None => unit
                                       end
                   end -> record (fields_right fs) -> T fs
      with
      | pm_Leaf => fun _ (x : Empty_set) _ => match x with end
      | pm_Branch l v r => @branch l v r
      end l v r
    end.

  Definition record_left {L} {V : option Type@{U}} {R}
             (r : record (pm_Branch L V R)) : record L :=
    match r with
    | pr_Branch' _ l _ _ => l
    | pr_Leaf' z =>
      match z in _ = Z return match Z with
                              | pm_Leaf => _
                              | pm_Branch _ _ _ => unit
                              end
      with
      | eq_refl => tt
      end
    end.

  Definition record_at {L} {V : option Type@{U}} {R} (r : record (pm_Branch L V R))
  : match V return Type@{U} with
    | None => unit
    | Some t => t
    end :=
    match r with
    | pr_Branch' _ _ v _ => v
    | pr_Leaf' pf => match pf with
                    | eq_refl => idProp
                    end
    end.

  Definition record_here {L : fields} (v : Type@{U}) {R : fields}
             (r : record (pm_Branch L (@Some Type@{U} v) R)) : v :=
    match r with
    | pr_Branch' _ _ v _ => v
    | pr_Leaf' pf => match pf with
                    | eq_refl => idProp
                    end
    end.

  Definition record_right {L V R} (r : record (pm_Branch L V R)) : record R :=
    match r with
    | pr_Branch' _ _ _ r => r
    | pr_Leaf' pf => match pf with
                    | eq_refl => idProp
                    end
    end.

  Fixpoint record_get {val : Type@{U}} {pm : fields} (m : member val pm) : record pm -> val :=
    match m in member _ pm return record pm -> val with
      | pmm_H => fun r => record_here r
      | pmm_L m' => fun r => record_get m' (record_left r)
      | pmm_R m' => fun r => record_get m' (record_right r)
    end.

  Fixpoint record_set {val : Type@{U}} {pm : fields} (m : member val pm) (x : val) {struct m}
  : record pm -> record pm :=
    match m in member _ pm return record pm -> record pm with
    | @pmm_H _ L R => fun r =>
      @pr_BranchSome L val R
                (record_left r)
                x
                (record_right r)
    | @pmm_L _ v L R m' => fun r =>
      @pr_Branch L v R
                (record_set m' x (record_left r))
                (record_at r)
                (record_right r)
    | @pmm_R _ v L R m' => fun r =>
      @pr_Branch L v R
                (record_left r)
                (record_at r)
                (record_set m' x (record_right r))
    end.

  Definition record_empty : record pm_Leaf := pr_Leaf.
  Fixpoint record_singleton {T : Type@{U}} (p : field) (val : T) {struct p}
  : record (fields_singleton p T) :=
    match p as p return record (fields_singleton p T) with
    | xH => pr_BranchSome pr_Leaf val pr_Leaf
    | xI p' =>
      pr_BranchNone pr_Leaf (record_singleton p' val)
    | xO p0 =>
      pr_BranchNone (record_singleton p0 val) pr_Leaf
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
  : record r -> record (fields_join l r).
  refine
    match L with
      | pr_Leaf' pf => fun v =>
        match eq_sym pf in _ = Z return record (fields_join Z r) with
        | eq_refl => v
        end
      | @pr_Branch' _ lL lV lR => fun R =>
        match R with
          | pr_Leaf' pf =>
            match eq_sym pf in _ = Z return record (fields_join l Z) with
            | eq_refl => _
            end
          | @pr_Branch' _ rL rV rR =>
            match l as l' , r as r'
                  return record (fields_left l') ->
                         match l' return Type@{U} with
                         | pm_Leaf => Empty_set
                         | pm_Branch _ _ _ => match fields_here l' return Type@{U} with
                                             | Some t => t
                                             | None => unit
                                             end
                         end ->
                         record (fields_right l') ->
                         record (fields_left r') ->
                         match r' return Type@{U} with
                         | pm_Leaf => Empty_set
                         | pm_Branch _ _ _ => match fields_here r' return Type@{U} with
                                             | Some t => t
                                             | None => unit
                                             end
                         end ->
                         record (fields_right r') ->
                         record (fields_join l' r')
            with
            | pm_Leaf , _ => fun _ x _ _ _ _ => match x with end
            | _ , pm_Leaf => fun _ _ _ _ x _ => match x with end
            | pm_Branch L V R , pm_Branch L' V' R' =>
              fun lb l rb lb' r rb' =>
                @pr_Branch' (pm_Branch _ _ _)
                           (Rjoin _ _ lb lb') _ (Rjoin _ _ rb rb')
            end lL lV lR rL rV rR
        end
    end.
  { destruct l; simpl in *.
    { destruct lV. }
    { subst. constructor 2; simpl; try assumption. } }
  { simpl in *. destruct V; assumption. }
  Defined.

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
