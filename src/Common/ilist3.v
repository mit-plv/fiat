Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Arith.
Require Import Fiat.Common.ilist.
Require Import Fiat.Common.

Section ilist3.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Import Vectors.VectorDef.VectorNotations.

  Context {A : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The type of indexed elements. *)

  Fixpoint ilist3 {n} (l : Vector.t A n) : Type :=
    match l with
      | [] => unit
      | a :: l => @prim_prod (B a) (ilist3 l)
    end.

  Definition icons3
             (a : A)
             {n}
             {l : Vector.t A n}
             (b : B a)
             (il : ilist3 l)
  : ilist3 (a :: l)
    := {| prim_fst := b; prim_snd := il |}.

  Definition inil3 : ilist3 [] := tt.

  (* Get the car of an ilist3. *)
  Definition ilist3_hd {n} {As : Vector.t A n} (il : ilist3 As) :
    match As return ilist3 As -> Type with
      | a :: As' => fun il => B a
      | [] => fun _ => unit
    end il :=
    match As return
          forall (il : ilist3 As),
            match As return ilist3 As -> Type with
              | a :: As' => fun il => B a
              | [] => fun _ => unit
            end il with
      | a :: As => fun il => prim_fst il
      | [] => fun il => tt
    end il.

  Definition ilist3_hd' {n} {As : Vector.t A (S n)} (il : ilist3 As) :
    B (Vector.hd As)
    := Vector.caseS (fun n As => ilist3 As -> B (Vector.hd As))
                           (fun a As m => ilist3_hd) As il.

  (* Get the cdr of an ilist3. *)
  Definition ilist3_tl {n} {As : Vector.t A n} (il : ilist3 As) :
    match As return ilist3 As -> Type with
      | a :: As' => fun il => ilist3 As'
      | [] => fun _ => unit
    end il :=
    match As return
          forall (il : ilist3 As),
            match As return ilist3 As -> Type with
              | a :: As' => fun il => ilist3 As'
              | [] => fun _ => unit
            end il with
      | a :: As => fun il => prim_snd il
      | [] => fun il => tt
    end il.

  Definition ilist3_tl'
             {n} {As : Vector.t A (S n)} (il : ilist3 As)
    : ilist3 (Vector.tl As) :=
    Vector.caseS (fun n As => ilist3 As -> ilist3 (Vector.tl As))
                 (fun a As m => ilist3_tl) As il.

  Infix "++" := Vector.append : vector_scope.

  (* Appending ilist3s *)
  Fixpoint ilist3_app {n} {As : Vector.t A n}
    : forall {n'} {As' : Vector.t A n'},  ilist3 As -> ilist3 As' -> ilist3 (As ++ As') :=
      match As return
            forall {n'} (As' : Vector.t A n'),
              ilist3 As -> ilist3 As' -> ilist3 (As ++ As') with
        | [] =>
          fun n' As' il il' => il'
        | a :: As'' =>
          fun n' As' il il' =>
            {| prim_fst := ilist3_hd il;
               prim_snd := ilist3_app (ilist3_tl il) il' |}
      end.

  (* Membership in an indexed list. *)

  Inductive ilist3_In {a : A} (b : B a)
  : forall {n} {As : Vector.t A n} (il : ilist3 As), Prop :=
  | In_hd : forall n' As' (il : ilist3 (n := n') As'),
              ilist3_In b (icons3 b il)
  | In_tl : forall {n'} a' (b' : B a') As' (il : ilist3 (n := n') As'),
              ilist3_In b il ->
              ilist3_In b (icons3 b' il).

  (* Looking up the ith value, returning None for indices not in the Vector.t *)

  Fixpoint ith3
           {m : nat}
           {As : Vector.t A m}
           (il : ilist3 As)
           (n : Fin.t m)
           {struct n}
    : B (Vector.nth As n) :=
    match n in Fin.t m return
          forall (As : Vector.t A m),
            ilist3 As
            -> B (Vector.nth As n) with
    | Fin.F1 k =>
      fun As =>
        Vector.caseS (fun n As => ilist3 As
                                  -> B (Vector.nth As (@Fin.F1 n)))
                     (fun h n t => ilist3_hd) As
    | Fin.FS k n' =>
      fun As =>
        Vector_caseS' Fin.t
                      (fun n As n' =>
                          ilist3 As
                          -> B (Vector.nth As (@Fin.FS n n')))
                     (fun h n t m il => ith3 (ilist3_tl il) m)
                     As n'
    end As il.

  Lemma ilist3_invert {n} (As : Vector.t A n) (il : ilist3 As) :
    match As as As' return ilist3 As' -> Prop with
      | a :: As' => fun il => exists b il', il = icons3 b il'
      | [] => fun il => il = inil3
    end il.
  Proof.
    destruct As; destruct il; simpl; unfold icons3; eauto.
  Qed.

  Lemma ilist3_invert' {n} (As : Vector.t A n) (il : ilist3 As) :
    match As as As' return ilist3 As' -> Type with
      | a :: As' => fun il => sigT (fun b => sigT (fun il' => il = icons3 b il'))
      | [] => fun il => il = inil3
    end il.
  Proof.
    destruct As; destruct il; unfold icons3; eauto.
  Qed.

End ilist3.

(** ** Mapping a function over a(n i)[list], in two non-dependent ways *)
Section ilist3_map.
  Context {A} (B : A -> Type).

  Import Vectors.VectorDef.VectorNotations.

  Fixpoint imap3_list (f : forall a : A, B a) {n} (As : Vector.t A n) : ilist3 As
    := match As with
         | [] => inil3
         | x :: xs => @icons3 _ B x _ _ (f x) (imap3_list f xs)
       end.

End ilist3_map.

Ltac icons3_invert :=
  repeat match goal with
           | [il : ilist3 _ (_ :: _) |- _]
             => let il' := fresh "il" in
                let b' := fresh "b" in
                let il'_eq := fresh "il_eq" in
                generalize (ilist3_invert il);
                  intros il'; destruct il' as [b' [il' il'_eq]]; subst
         end.

Section ilist3_imap.

  (* Mapping a function over an indexed Vector.t. *)

  Import Vectors.VectorDef.VectorNotations.

  Variable A : Type. (* The indexing type. *)
  Variable B B' : A -> Type. (* The two types of indexed elements. *)
  Variable f : forall a, B a -> B' a. (* The function to map over the Vector.t. *)

  Fixpoint imap3 {n} (As : Vector.t A n)
    : ilist3 (B:=B) As -> ilist3 (B:=B') As :=
    match As return ilist3 As -> ilist3 As with
    | [] => fun il => inil3
    | a :: As' => fun il => icons3 (f (ilist3_hd il)) (imap3 As' (ilist3_tl il))
    end.

  (* [imap] behaves as expected with the [ith3_default] lookup
     function. *)
  Lemma ith_imap3 :
    forall {n}
           (m : Fin.t n)
           (As : Vector.t A n)
           (il : ilist3 As),
      f (ith3 il m) = ith3 (imap3 As il) m.
  Proof.
    induction m; intro.
    - eapply Vector.caseS with (v := As); intros; simpl in *; destruct il; reflexivity.
    - revert m IHm.
      pattern n, As.
      match goal with
        |- ?P n As =>
        simpl; eapply (@Vector.rectS _ P); intros
      end.
      inversion m.
      eapply IHm.
  Qed.

End ilist3_imap.

Section ilist3_replace.

  Import Vectors.VectorDef.VectorNotations.

  (* Replacing an element of an indexed Vector.t. *)
  Context {A : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The two types of indexed elements. *)

  Fixpoint replace_Index3
             {m}
             (As : Vector.t A m)
             (il : ilist3 As)
             (n : Fin.t m)
             (new_b : B (Vector.nth As n))
             {struct n}
    : ilist3 (B:=B) As :=
    match n in Fin.t m return
          forall (As : Vector.t A m),
            ilist3 As
            -> B (Vector.nth As n)
            -> ilist3 As with
    | Fin.F1 k =>
      fun As =>
        Vector.caseS (fun n As => ilist3 As
                                  -> B (Vector.nth As (@Fin.F1 n))
                                  -> ilist3 As)
                     (fun h n t il new_b => icons3 new_b (ilist3_tl il) ) As
    | Fin.FS k n' =>
      fun As =>
        Vector_caseS' Fin.t
                      (fun n As n' =>
                          ilist3 As
                          -> B (Vector.nth As (@Fin.FS n n'))
                          -> ilist3 As)
                     (fun h n t m il new_b => icons3 (ilist3_hd il)
                                                    (@replace_Index3 _ _ (ilist3_tl il) _ new_b))
                     As n'
    end As il new_b.

  Lemma ith_replace3_Index_neq {m}
    : forall
      (n n' : Fin.t m)
      (As : Vector.t A m)
      (il : ilist3 As)
      (new_b : B (Vector.nth As n')),
      n <> n'
      -> ith3 (replace_Index3 As il n' new_b) n = ith3 il n.
  Proof.
    intros n n'; pattern m, n, n'.
    match goal with
      |- ?P m n n' => simpl; eapply (Fin.rect2 P); intros
    end.
    - congruence.
    - generalize il f new_b; clear f new_b il H.
      pattern n0, As.
      match goal with
        |- ?P n0 As =>
        simpl; apply (@Vector.rectS _ P); intros; reflexivity
      end.
    - generalize il f new_b; clear f new_b il H.
      pattern n0, As.
      match goal with
        |- ?P n0 As =>
        simpl; apply (@Vector.rectS _ P); intros; reflexivity
      end.
    - assert (f <> g) by congruence.
      generalize il f g new_b H H1; clear f g new_b il H H1 H0.
      pattern n0, As.
      match goal with
        |- ?P n0 As =>
        simpl; apply (@Vector.caseS _ P); intros;
        eapply (H _ (prim_snd il) new_b); eauto
      end.
  Qed.

  Lemma ith_replace3_Index_eq {m}
    : forall
      (n : Fin.t m)
      (As : Vector.t A m)
      (il : ilist3 As)
      (new_b : B (Vector.nth As n)),
      ith3 (replace_Index3 As il n new_b) n = new_b.
  Proof.
    induction n; simpl.
    - intro As; pattern n, As.
      match goal with
        |- ?P n As =>
        simpl; apply (@Vector.caseS _ P); intros; reflexivity
      end.
    - intro As; revert n0 IHn; pattern n, As.
      match goal with
        |- ?P n As =>
        simpl; apply (@Vector.caseS _ P); simpl; eauto
      end.
  Qed.


End ilist3_replace.

(*Lemma imap_replace3_Index
      {A}
      {m}
      {B B' : A -> Type}
  : forall (f : forall idx'', B idx'' -> B' idx'')
           (idx : Fin.t m )
           (Bound : Vector.t A m)
           (il : ilist3 Bound)
           b,
    imap3 B B' f Bound (replace_Index3 Bound il idx b) =
    replace_Index3 Bound (imap3 B B' f Bound il) idx (f _ b).
Proof.
  induction idx.
  - intro Bound; pattern n, Bound.
    match goal with
      |- ?P n Bound =>
      simpl; apply (@Vector.caseS _ P); intros; reflexivity
    end.
  - intro Bound; revert idx IHidx; pattern n, Bound.
    match goal with
      |- ?P n Bound =>
      simpl; apply (@Vector.caseS _ P); intros; simpl; f_equal; eauto
    end.
Qed. *)
