Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith
        Fiat.Common.ilist
        Fiat.Common.ilist2.

Section ilist2_pair.

  (* Lists of elements whose types depend on two indexing sets.  *)

  Import Vectors.VectorDef.VectorNotations.

  Context {A A' : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The type of indexed elements. *)
  Context {C : forall a (a' : A'), B a -> Type}.

  Fixpoint ilist2_pair {n}
           {l : Vector.t A n}
           (il : ilist2 l)
           (l' : Vector.t A' n)
    : Type :=
    match n return forall (l :Vector.t A n),
        ilist2 l -> Vector.t A' n -> Type with
    | 0 => fun _ _ _ => unit
    | S n' => fun l il l' =>
                   @prim_prod (C (Vector.hd l') (ilist2_hd' il))
                              (ilist2_pair (ilist2_tl' il) (Vector.tl l'))
    end l il l'.

  Definition icons2_pair
             {a : A}
             {b : B a}
             {a' : A'}
             {n}
             {l : Vector.t A n}
             {l' : Vector.t A' n}
             (il : ilist2 l)
             (ilp : ilist2_pair il l')
             (c : C a' b)
  : ilist2_pair (icons2 b il) (a' :: l')
    := {| prim_fst := c; prim_snd := ilp |}.

  Definition inil2_pair : ilist2_pair inil2 [] := tt.

  (* Get the car of an ilist2_pair. *)
  (*Definition ilist2_pair_hd {n}
             (As : Vector.t A n)
             (As' : Vector.t A' n)
             (il : ilist2_pair As As') :
    match n return
          forall (As : Vector.t A n)
                 (As' : Vector.t A' n)
                 (il : ilist2_pair As As'), Type with
    | 0 => fun As As' il => unit
    | S n' => fun As As' il' => B (Vector.hd As) (Vector.hd As')
    end As As' il :=
    match n return forall As As' il,
        match n return forall (As : Vector.t A n)
                              (As' : Vector.t A' n)
                              (il : ilist2_pair As As'), Type with
        | 0 => fun As As' il => unit
        | S n' => fun As As' il => B (Vector.hd As) (Vector.hd As')
        end As As' il with
    | 0 => fun _ _ _ => tt
    | S n' => fun As As' il => prim_fst il
    end As As' il.

  (* Get the cdr of an ilist2_pair. *)
  Definition ilist2_pair_tl {n}
             (As : Vector.t A n)
             (As' : Vector.t A' n)
             (il : ilist2_pair As As') :
    match n return
          forall (As : Vector.t A n)
                 (As' : Vector.t A' n)
                 (il : ilist2_pair As As'), Type with
    | 0 => fun As As' il => unit
    | S n' => fun As As' il' => ilist2_pair (Vector.tl As) (Vector.tl As')
    end As As' il :=
    match n return forall As As' il,
        match n return forall (As : Vector.t A n)
                              (As' : Vector.t A' n)
                              (il : ilist2_pair As As'), Type with
        | 0 => fun As As' il => unit
        | S n' => fun As As' il => ilist2_pair (Vector.tl As) (Vector.tl As')
        end As As' il with
    | 0 => fun _ _ _ => tt
    | S n' => fun As As' il => prim_snd il
    end As As' il. *)

  Fixpoint ith2_pair
           {m : nat}
           {As : Vector.t A m}
           {As' : Vector.t A' m}
           {il : ilist2 As}
           (ilp : ilist2_pair il As')
           (n : Fin.t m)
           {struct n}
    : C (Vector.nth As' n) (ith2 il n) .
        revert il ilp n; pattern m, As, As'.
        match goal with
          |- ?f m As As' => simpl; apply (Vector.rect2 f); simpl; intros
        end.
        - inversion n.
        - revert v1 v2 a b il ilp X; pattern n, n0.
          apply Fin.caseS; simpl.
          + intros; exact (prim_fst ilp).
          + intros; exact (X _ (prim_snd ilp) _).
  Defined.
End ilist2_pair.
