Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Arith.
Require Import Fiat.Common.ilist.
Require Import Fiat.Common.
Require Export Fiat.Common.VectorFacts.

Section ilist2.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Import Vectors.VectorDef.VectorNotations.

  Context {A : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The type of indexed elements. *)

  Fixpoint ilist2 {n} (l : Vector.t A n) : Type :=
    match l with
      | [] => unit
      | a :: l => @prim_prod (B a) (ilist2 l)
    end.

  Definition icons2
             (a : A)
             {n}
             {l : Vector.t A n}
             (b : B a)
             (il : ilist2 l)
  : ilist2 (a :: l)
    := {| prim_fst := b; prim_snd := il |}.

  Definition inil2 : ilist2 [] := tt.

  (* Get the car of an ilist2. *)
  Definition ilist2_hd {n} {As : Vector.t A n} (il : ilist2 As) :
    match As return ilist2 As -> Type with
      | a :: As' => fun il => B a
      | [] => fun _ => unit
    end il :=
    match As return
          forall (il : ilist2 As),
            match As return ilist2 As -> Type with
              | a :: As' => fun il => B a
              | [] => fun _ => unit
            end il with
      | a :: As => fun il => prim_fst il
      | [] => fun il => tt
    end il.

  Definition ilist2_hd' {n} {As : Vector.t A (S n)} (il : ilist2 As) :
    B (Vector.hd As)
    := Vector.caseS (fun n As => ilist2 As -> B (Vector.hd As))
                           (fun a As m => ilist2_hd) As il.

  (* Get the cdr of an ilist2. *)
  Definition ilist2_tl {n} {As : Vector.t A n} (il : ilist2 As) :
    match As return ilist2 As -> Type with
      | a :: As' => fun il => ilist2 As'
      | [] => fun _ => unit
    end il :=
    match As return
          forall (il : ilist2 As),
            match As return ilist2 As -> Type with
              | a :: As' => fun il => ilist2 As'
              | [] => fun _ => unit
            end il with
      | a :: As => fun il => prim_snd il
      | [] => fun il => tt
    end il.

  Definition ilist2_tl'
             {n} {As : Vector.t A (S n)} (il : ilist2 As)
    : ilist2 (Vector.tl As) :=
    Vector.caseS (fun n As => ilist2 As -> ilist2 (Vector.tl As))
                 (fun a As m => ilist2_tl) As il.

  Infix "++" := Vector.append : vector_scope.

  (* Appending ilist2s *)
  Fixpoint ilist2_app {n} {As : Vector.t A n}
    : forall {n'} {As' : Vector.t A n'},  ilist2 As -> ilist2 As' -> ilist2 (As ++ As') :=
      match As return
            forall {n'} (As' : Vector.t A n'),
              ilist2 As -> ilist2 As' -> ilist2 (As ++ As') with
        | [] =>
          fun n' As' il il' => il'
        | a :: As'' =>
          fun n' As' il il' =>
            {| prim_fst := ilist2_hd il;
               prim_snd := ilist2_app (ilist2_tl il) il' |}
      end.

  (* Membership in an indexed list. *)

  Inductive ilist2_In {a : A} (b : B a)
  : forall {n} {As : Vector.t A n} (il : ilist2 As), Prop :=
  | In_hd : forall n' As' (il : ilist2 (n := n') As'),
              ilist2_In b (icons2 b il)
  | In_tl : forall {n'} a' (b' : B a') As' (il : ilist2 (n := n') As'),
              ilist2_In b il ->
              ilist2_In b (icons2 b' il).

  (* Looking up the ith value, returning None for indices not in the Vector.t *)

  Fixpoint ith2
           {m : nat}
           {As : Vector.t A m}
           (il : ilist2 As)
           (n : Fin.t m)
           {struct n}
    : B (Vector.nth As n) :=
    match n in Fin.t m return
          forall (As : Vector.t A m),
            ilist2 As
            -> B (Vector.nth As n) with
    | Fin.F1 k =>
      fun As =>
        Vector.caseS (fun n As => ilist2 As
                                  -> B (Vector.nth As (@Fin.F1 n)))
                     (fun h n t => ilist2_hd) As
    | Fin.FS k n' =>
      fun As =>
        Vector_caseS' Fin.t
                      (fun n As n' =>
                         ilist2 As
                          -> B (Vector.nth As (@Fin.FS n n')))
                     (fun h n t m il => ith2 (ilist2_tl il) m)
                     As n'
    end As il.

  Lemma ilist2_invert {n} (As : Vector.t A n) (il : ilist2 As) :
    match As as As' return ilist2 As' -> Prop with
      | a :: As' => fun il => exists b il', il = icons2 b il'
      | [] => fun il => il = inil2
    end il.
  Proof.
    destruct As; destruct il; simpl; unfold icons2; eauto.
  Qed.

  Lemma ilist2_invert' {n} (As : Vector.t A n) (il : ilist2 As) :
    match As as As' return ilist2 As' -> Type with
      | a :: As' => fun il => sigT (fun b => sigT (fun il' => il = icons2 b il'))
      | [] => fun il => il = inil2
    end il.
  Proof.
    destruct As; destruct il; unfold icons2; eauto.
  Qed.

End ilist2.

(** ** Mapping a function over a(n i)[list], in two non-dependent ways *)
Section ilist2_map.
  Context {A} (B : A -> Type).

  Import Vectors.VectorDef.VectorNotations.

  Fixpoint imap2_list (f : forall a : A, B a) {n} (As : Vector.t A n) : ilist2 As
    := match As with
         | [] => inil2
         | x :: xs => @icons2 _ B x _ _ (f x) (imap2_list f xs)
       end.

End ilist2_map.

Ltac icons2_invert :=
  repeat match goal with
           | [il : ilist2 _ (_ :: _) |- _]
             => let il' := fresh "il" in
                let b' := fresh "b" in
                let il'_eq := fresh "il_eq" in
                generalize (ilist2_invert il);
                  intros il'; destruct il' as [b' [il' il'_eq]]; subst
         end.

Section ilist2_imap.

  (* Mapping a function over an indexed Vector.t. *)

  Import Vectors.VectorDef.VectorNotations.

  Variable A : Type. (* The indexing type. *)
  Variable B B' : A -> Type. (* The two types of indexed elements. *)
  Variable f : forall a, B a -> B' a. (* The function to map over the Vector.t. *)

  Fixpoint imap2 {n} (As : Vector.t A n)
    : ilist2 As -> ilist2 As :=
    match As return ilist2 As -> ilist2 As with
    | [] => fun il => inil2
    | a :: As' => fun il => icons2 (@f a (ilist2_hd il)) (imap2 As' (ilist2_tl il))
    end.

  (* [imap] behaves as expected with the [ith2_default] lookup
     function. *)
  Lemma ith_imap2 :
    forall {n}
           (m : Fin.t n)
           (As : Vector.t A n)
           (il : ilist2 As),
      f (ith2 il m) = ith2 (imap2 As il) m.
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

End ilist2_imap.

Section ilist2_replace.

  Import Vectors.VectorDef.VectorNotations.

  (* Replacing an element of an indexed Vector.t. *)
  Context {A : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The two types of indexed elements. *)

  Fixpoint replace_Index2
             {m}
             (As : Vector.t A m)
             (il : ilist2 As)
             (n : Fin.t m)
             (new_b : B (Vector.nth As n))
             {struct n}
    : ilist2 As :=
    match n in Fin.t m return
          forall (As : Vector.t A m),
            @ilist2 _ B _ As
            -> B (Vector.nth As n)
            -> ilist2 As with
    | Fin.F1 k =>
      fun As =>
        Vector.caseS (fun n As => ilist2 As
                                  -> B (Vector.nth As (@Fin.F1 n))
                                  -> ilist2 As)
                     (fun h n t il new_b => icons2 new_b (ilist2_tl il) ) As
    | Fin.FS k n' =>
      fun As =>
        Vector_caseS' Fin.t
                      (fun n As n' =>
                          ilist2 As
                          -> B (Vector.nth As (@Fin.FS n n'))
                          -> ilist2 As)
                     (fun h n t m il new_b => icons2 (ilist2_hd il)
                                                    (@replace_Index2 _ _ (ilist2_tl il) _ new_b))
                     As n'
    end As il new_b.

  Lemma ith_replace2_Index_neq {m}
    : forall
      (n n' : Fin.t m)
      (As : Vector.t A m)
      (il : ilist2 As)
      (new_b : B (Vector.nth As n')),
      n <> n'
      -> ith2 (replace_Index2 As il n' new_b) n = ith2 il n.
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

  Lemma ith_replace2_Index_eq {m}
    : forall
      (n : Fin.t m)
      (As : Vector.t A m)
      (il : ilist2 As)
      (new_b : B (Vector.nth As n)),
      ith2 (replace_Index2 As il n new_b) n = new_b.
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


End ilist2_replace.

Lemma imap_replace2_Index
      {A}
      {m}
      {B B' : A -> Type}
  : forall (f : forall idx'', B idx'' -> B' idx'')
           (idx : Fin.t m )
           (Bound : Vector.t A m)
           (il : ilist2 Bound)
           b,
    imap2 B B' f Bound (replace_Index2 Bound il idx b) =
    replace_Index2 Bound (imap2 B B' f Bound il) idx (f _ b).
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
Qed.

Section ilist2_update.

  Import Vectors.VectorDef.VectorNotations.

  (* Replacing an element of an indexed Vector.t. *)
  Context {A : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The two types of indexed elements. *)

  Fixpoint update_Index2
             {m}
             (As : Vector.t A m)
             (il : ilist2 As)
             (n : Fin.t m)
             (update_b : B (Vector.nth As n) -> B (Vector.nth As n))
             {struct n}
    : ilist2 As :=
    match n in Fin.t m return
          forall (As : Vector.t A m),
            @ilist2 _ B _ As
            -> (B (Vector.nth As n) -> B (Vector.nth As n))
            -> ilist2 As with
    | Fin.F1 k =>
      fun As =>
        Vector.caseS (fun n As => ilist2 As
                                  -> (B (Vector.nth As (@Fin.F1 n)) -> B (Vector.nth As (@Fin.F1 n)))
                                  -> ilist2 As)
                     (fun h n t il update_b => icons2 (update_b (ilist2_hd il)) (ilist2_tl il) ) As
    | Fin.FS k n' =>
      fun As =>
        Vector_caseS' Fin.t
                      (fun n As n' =>
                          ilist2 As
                          -> (B (Vector.nth As (@Fin.FS n n')) -> B (Vector.nth As (@Fin.FS n n')))
                          -> ilist2 As)
                      (fun h n t m il update_b => icons2 (ilist2_hd il)
                                                    (@update_Index2 _ _ (ilist2_tl il) _ update_b))
                      As n'
    end As il update_b.

  Lemma ith_update_Index2_neq {m}
    : forall
      (n n' : Fin.t m)
      (As : Vector.t A m)
      (il : ilist2 As)
      (update_b : B (Vector.nth As n') -> B (Vector.nth As n')),
      n <> n'
      -> ith2 (update_Index2 As il n' update_b) n = ith2 il n.
  Proof.
    intros n n'; pattern m, n, n'.
    match goal with
      |- ?P m n n' => simpl; eapply (Fin.rect2 P); intros
    end.
    - congruence.
    - generalize il f update_b; clear f update_b il H.
      pattern n0, As.
      match goal with
        |- ?P n0 As =>
        simpl; apply (@Vector.rectS _ P); intros; reflexivity
      end.
    - generalize il f update_b; clear f update_b il H.
      pattern n0, As.
      match goal with
        |- ?P n0 As =>
        simpl; apply (@Vector.rectS _ P); intros; reflexivity
      end.
    - assert (f <> g) by congruence.
      generalize il f g update_b H H1; clear f g update_b il H H1 H0.
      pattern n0, As.
      match goal with
        |- ?P n0 As =>
        simpl; apply (@Vector.caseS _ P); intros;
        eapply (H _ (prim_snd il) update_b); eauto
      end.
  Qed.
  Set Printing All.

  Lemma ith_update_Index2_eq {m}
    : forall
      (n : Fin.t m)
      (As : Vector.t A m)
      (il : ilist2 As)
      (update_b : B (Vector.nth As n) -> B (Vector.nth As n)),
      ith2 (update_Index2 As il n update_b) n = update_b (ith2 il n).
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

End ilist2_update.
