Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith
        Fiat.Common.ilist
        Fiat.Common.ilist3.

Section i3list2.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Import Vectors.VectorDef.VectorNotations.

  Context {A : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The type of indexed elements. *)
  Variable C : forall a, B a ->  Type. (* The type of doubly-indexed elements. *)

  Fixpoint i3list2 {n}
           {l : Vector.t A n}
    : ilist3 (B := B) l -> Type :=
    match l return ilist3 (B := B) l -> Type with
    | [] => fun _ => unit
    | a :: l' => fun il => @prim_prod (C (ilist3_hd il))
                                      (i3list2 (ilist3_tl il))
    end.

  Definition i3cons2
             {a : A}
             {n}
             {l : Vector.t A n}
             {b : B a}
             {il : ilist3 l}
             (c : C b)
             (il3 : i3list2 il)
  : i3list2 (icons3 b il)
    := {| prim_fst := c; prim_snd := il3 |}.

  Definition i3nil2 : i3list2 inil3 := tt.

  (* Get the car of an i3list. *)
  Definition i3list2_hd {n}
             (As : Vector.t A n)
             (Bs : ilist3 As)
             (i3l : i3list2 Bs) :
    match As return forall Bs : ilist3 As, i3list2 Bs -> Type with
    | a :: As' => fun Bs i3l => C (ilist3_hd Bs)
      | [] => fun _ _ => unit
    end Bs i3l :=
    match As as As' return
          forall Bs i3l,
          match As' return forall Bs : ilist3 As', i3list2 Bs -> Type with
          | a :: As' => fun Bs i3l => C (ilist3_hd Bs)
          | [] => fun _ _ => unit
          end Bs i3l with
    | [] => fun _ _ => tt
    | a :: As' => fun Bs il => prim_fst il
    end Bs i3l.

  (* Get the cdr of an i3list. *)
  Definition i3list2_tl {n}
             (As : Vector.t A n)
             (Bs : ilist3 As)
             (i3l : i3list2 Bs) :
    match As return forall Bs : ilist3 As, i3list2 Bs -> Type with
    | a :: As' => fun Bs i3l => i3list2 (ilist3_tl Bs)
    | [] => fun _ _ => unit
    end Bs i3l :=
    match As as As' return
          forall Bs i3l,
          match As' return forall Bs : ilist3 As', i3list2 Bs -> Type with
          | a :: As' => fun Bs i3l => i3list2 (ilist3_tl Bs)
          | [] => fun _ _ => unit
          end Bs i3l with
    | [] => fun _ _ => tt
    | a :: As' => fun Bs il => prim_snd il
    end Bs i3l.

  Fixpoint i3th2
           {m : nat}
           {As : Vector.t A m}
           {Bs : ilist3 As}
           (i3l : i3list2 Bs)
           (n : Fin.t m)
           {struct n}
    : C (ith3 Bs n) :=
    match n in Fin.t m return
          forall (As : Vector.t A m)
                 (Bs : ilist3 As),
            i3list2 Bs
            -> C (ith3 Bs n) with
    | Fin.F1 k =>
      fun As Bs i3l =>
        Vector.caseS (fun n As =>
                        forall (Bs : ilist3 As), i3list2 Bs
                                   -> C (ith3 Bs (@Fin.F1 n)))
                     (fun a' n' As' (Bs' : ilist3 (a' :: As')) i3l' => prim_fst i3l' ) As Bs i3l
    | Fin.FS k n'' =>
      fun As Bs i3l =>
        Vector_caseS' Fin.t
                      (fun n' As i =>
                        forall (Bs'' : ilist3 As),
                          i3list2 Bs''
                          -> C (ith3 Bs'' (@Fin.FS n' i)))
                     (fun a' n' As' n'' (Bs' : ilist3 (a' :: As')) i3l' => i3th2 (prim_snd i3l') n'')
                     As n'' Bs i3l
    end As Bs i3l.

End i3list2.

Fixpoint i3map2
         {A : Type}
         {B : A -> Type}
         {C C' : forall a, B a ->  Type}
         (f : forall a b, C a b -> C' a b)
         {m : nat}
         {As : Vector.t A m}
         {Bs : ilist3 As}
         (i3l : i3list2 C Bs)
  : i3list2 C' Bs :=
  match As return
        forall (Bs : ilist3 As),
          i3list2 C Bs
          -> i3list2 C' Bs with
  | Vector.nil => fun _ _ => tt
  | Vector.cons a _ l' => fun Bs Cs => {| prim_fst := f a _ (prim_fst Cs);
                                          prim_snd := i3map2 f (prim_snd Cs) |}
  end Bs i3l.

Lemma i3th2_i3map2 {A : Type}
      {B : A -> Type}
      {C C' : forall a, B a ->  Type}
  : forall (f : forall a b, C a b -> C' a b)
           {m : nat}
           (n : Fin.t m)
           {As : Vector.t A m}
           {Bs : ilist3 As}
           (i3l : i3list2 C Bs),
    f _ _ (i3th2 C i3l n) = i3th2 C' (i3map2 f i3l) n.
Proof.
  induction n; intro.
  - eapply Vector.caseS with (v := As); intros; simpl in *; destruct i3l; reflexivity.
  - revert n0 IHn.
    pattern n, As.
    match goal with
      |- ?P n As =>
      simpl; eapply (@Vector.rectS _ P); intros
    end.
    + inversion n0.
    + eapply IHn.
Qed.

Arguments i3cons2 [_ _ _ _ _ _ _ _] _ _.
Arguments i3nil2 [_ _ _].
Arguments i3th2 [_ _ _ _ _ _] _ _.
