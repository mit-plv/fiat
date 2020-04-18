Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith
        Fiat.Common.ilist
        Fiat.Common.ilist3.

Section ilist3_pair.

  (* Lists of elements whose types depend on two indexing sets.  *)

  Import Vectors.VectorDef.VectorNotations.

  Context {A A' : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The type of indexed elements. *)
  Context {C : forall a (a' : A'), B a -> Type}.

  Fixpoint ilist3_pair {n}
           {l : Vector.t A n}
           (il : ilist3 l)
           (l' : Vector.t A' n)
    : Type :=
    match n return forall (l :Vector.t A n),
        ilist3 l -> Vector.t A' n -> Type with
    | 0 => fun _ _ _ => unit
    | S n' => fun l il l' =>
                   @prim_prod (C (Vector.hd l') (ilist3_hd' il))
                              (ilist3_pair (ilist3_tl' il) (Vector.tl l'))
    end l il l'.

  Definition icons3_pair
             {a : A}
             {b : B a}
             {a' : A'}
             {n}
             {l : Vector.t A n}
             {l' : Vector.t A' n}
             (il : ilist3 l)
             (ilp : ilist3_pair il l')
             (c : C a' b)
  : ilist3_pair (icons3 b il) (a' :: l')
    := {| prim_fst := c; prim_snd := ilp |}.

  Definition inil3_pair : ilist3_pair inil3 [] := tt.

  (* Get the car of an ilist3_pair. *)
  (*Definition ilist3_pair_hd {n}
             (As : Vector.t A n)
             (As' : Vector.t A' n)
             (il : ilist3_pair As As') :
    match n return
          forall (As : Vector.t A n)
                 (As' : Vector.t A' n)
                 (il : ilist3_pair As As'), Type with
    | 0 => fun As As' il => unit
    | S n' => fun As As' il' => B (Vector.hd As) (Vector.hd As')
    end As As' il :=
    match n return forall As As' il,
        match n return forall (As : Vector.t A n)
                              (As' : Vector.t A' n)
                              (il : ilist3_pair As As'), Type with
        | 0 => fun As As' il => unit
        | S n' => fun As As' il => B (Vector.hd As) (Vector.hd As')
        end As As' il with
    | 0 => fun _ _ _ => tt
    | S n' => fun As As' il => prim_fst il
    end As As' il.

  (* Get the cdr of an ilist3_pair. *)
  Definition ilist3_pair_tl {n}
             (As : Vector.t A n)
             (As' : Vector.t A' n)
             (il : ilist3_pair As As') :
    match n return
          forall (As : Vector.t A n)
                 (As' : Vector.t A' n)
                 (il : ilist3_pair As As'), Type with
    | 0 => fun As As' il => unit
    | S n' => fun As As' il' => ilist3_pair (Vector.tl As) (Vector.tl As')
    end As As' il :=
    match n return forall As As' il,
        match n return forall (As : Vector.t A n)
                              (As' : Vector.t A' n)
                              (il : ilist3_pair As As'), Type with
        | 0 => fun As As' il => unit
        | S n' => fun As As' il => ilist3_pair (Vector.tl As) (Vector.tl As')
        end As As' il with
    | 0 => fun _ _ _ => tt
    | S n' => fun As As' il => prim_snd il
    end As As' il. *)

  Fixpoint ith3_pair
           {m : nat}
           {As : Vector.t A m}
           {As' : Vector.t A' m}
           {il : ilist3 As}
           (ilp : ilist3_pair il As')
           (n : Fin.t m)
           {struct n}
    : C (Vector.nth As' n) (ith3 il n) .
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
End ilist3_pair.

Arguments icons3_pair [_ _ _ _ _ _ _ _ _ _ _ ] _ _.
Arguments inil3_pair [_ _ _ _ ].
Arguments ith3_pair [_ _ _ _ _ _ _ _] _ _.
