Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith
        Fiat.Common.ilist
        Fiat.Common.ilist3.

Section i3list.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Import Vectors.VectorDef.VectorNotations.

  Context {A : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The type of indexed elements. *)
  Variable C : forall a, B a ->  Type. (* The type of doubly-indexed elements. *)

  Fixpoint i3list {n}
           {l : Vector.t A n}
    : ilist3 (B := B) l -> Type :=
    match l return ilist3 (B := B) l -> Type with
    | [] => fun _ => unit
    | a :: l' => fun il => @prim_prod (C (ilist3_hd il))
                                      (i3list (ilist3_tl il))
    end.

  Definition i3cons
             {a : A}
             {n}
             {l : Vector.t A n}
             {b : B a}
             {il : ilist3 l}
             (c : C b)
             (il3 : i3list il)
  : i3list (icons3 b il)
    := {| prim_fst := c; prim_snd := il3 |}.

  Definition i3nil : i3list inil3 := tt.

  (* Get the car of an i3list. *)
  Definition i3list_hd {n}
             (As : Vector.t A n)
             (Bs : ilist3 As)
             (i3l : i3list Bs) :
    match As return forall Bs : ilist3 As, i3list Bs -> Type with
    | a :: As' => fun Bs i3l => C (ilist3_hd Bs)
      | [] => fun _ _ => unit
    end Bs i3l :=
    match As as As' return
          forall Bs i3l,
          match As' return forall Bs : ilist3 As', i3list Bs -> Type with
          | a :: As' => fun Bs i3l => C (ilist3_hd Bs)
          | [] => fun _ _ => unit
          end Bs i3l with
    | [] => fun _ _ => tt
    | a :: As' => fun Bs il => prim_fst il
    end Bs i3l.

  (* Get the cdr of an i3list. *)
  Definition i3list_tl {n}
             (As : Vector.t A n)
             (Bs : ilist3 As)
             (i3l : i3list Bs) :
    match As return forall Bs : ilist3 As, i3list Bs -> Type with
    | a :: As' => fun Bs i3l => i3list (ilist3_tl Bs)
    | [] => fun _ _ => unit
    end Bs i3l :=
    match As as As' return
          forall Bs i3l,
          match As' return forall Bs : ilist3 As', i3list Bs -> Type with
          | a :: As' => fun Bs i3l => i3list (ilist3_tl Bs)
          | [] => fun _ _ => unit
          end Bs i3l with
    | [] => fun _ _ => tt
    | a :: As' => fun Bs il => prim_snd il
    end Bs i3l.

  Fixpoint i3th
           {m : nat}
           {As : Vector.t A m}
           {Bs : ilist3 As}
           (i3l : i3list Bs)
           (n : Fin.t m)
           {struct n}
    : C (ith3 Bs n) :=
    match n in Fin.t m return
          forall (As : Vector.t A m)
                 (Bs : ilist3 As),
            i3list Bs
            -> C (ith3 Bs n) with
    | Fin.F1 k =>
      fun As Bs i3l =>
        Vector.caseS (fun n As =>
                        forall (Bs : ilist3 As), i3list Bs
                                   -> C (ith3 Bs (@Fin.F1 n)))
                     (fun a' n' As' (Bs' : ilist3 (a' :: As')) i3l' => prim_fst i3l' ) As Bs i3l
    | Fin.FS k n'' =>
      fun As Bs i3l =>
        Vector_caseS' Fin.t
                      (fun n' As i =>
                        forall (Bs'' : ilist3 As),
                          i3list Bs''
                          -> C (ith3 Bs'' (@Fin.FS n' i)))
                     (fun a' n' As' n'' (Bs' : ilist3 (a' :: As')) i3l' => i3th (prim_snd i3l') n'')
                     As n'' Bs i3l
    end As Bs i3l.

End i3list.

Arguments i3cons [_ _ _ _ _ _ _ _] _ _.
Arguments i3nil [_ _ _].
Arguments i3th [_ _ _ _ _ _] _ _.

Section i3list_replace.

  (* Replacing an element of an indexed list. *)
  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The two types of indexed elements. *)
  Variable C : forall a, B a -> Type. (* The type of doubly-indexed elements. *)

  Import Vectors.VectorDef.VectorNotations.

  Fixpoint replace3_Index3
          {m : nat}
          {As : Vector.t A m}
          {Bs : ilist3 As}
          (i3l : i3list C Bs)
          (n : Fin.t m)
          (new_c : C (ith3 Bs n))
    : i3list C Bs :=
        match n in Fin.t m return
          forall (As : Vector.t A m)
                 (Bs : ilist3 As),
            i3list C Bs
            -> C (ith3 Bs n)
            -> i3list C Bs with
        | Fin.F1 k =>
          fun As Bs i3l new_c =>
            Vector.caseS (fun n As =>
                            forall (Bs : ilist3 As), i3list C Bs
                                                     -> C (ith3 Bs (@Fin.F1 n))
                                                     -> i3list C Bs)
                         (fun a' n' As' (Bs' : ilist3 (a' :: As')) i3l' new_c => i3cons new_c (prim_snd i3l') ) As Bs i3l new_c
    | Fin.FS k n'' =>
      fun As Bs i3l new_c =>
        Vector.caseS (fun n' As =>
                        forall (i : Fin.t n') (Bs'' : ilist3 As),
                          i3list C Bs''
                          -> C (ith3 Bs'' (@Fin.FS n' i))
                          -> i3list C Bs'')
                     (fun a' n' As' n'' (Bs' : ilist3 (a' :: As')) i3l' new_c => i3cons (prim_fst i3l') (replace3_Index3 (prim_snd i3l') n'' new_c))
                     As n'' Bs i3l new_c
        end As Bs i3l new_c.

  Lemma i3th_replace_Index_neq
    : forall {m : nat}
             {As : Vector.t A m}
             {Bs : ilist3 As}
             (i3l : i3list C Bs)
             (n n' : Fin.t m)
             (new_c : C (ith3 Bs n)),
      n <> n'
      -> i3th (replace3_Index3 i3l n new_c) n' =
         i3th i3l n'.
  Proof.
    induction As.
    - intros; inversion n.
    - intros; revert n' As Bs i3l new_c H IHAs; pattern n, n0.
      match goal with
        |- ?P n n0 => simpl; apply (@Fin.caseS P); clear n n0; simpl in *
      end.
      + intros n n'; pattern n, n';
        match goal with
          |- ?P n n' => simpl; apply (@Fin.caseS P); clear n n'; intros; simpl in *;
                        eauto; congruence
        end.
      + intros n p n'; revert p; pattern n, n';
        match goal with
          |- ?P n n' => simpl; apply (@Fin.caseS P); clear n n'; intros; simpl in *;
                        eauto
        end.
        eapply IHAs; congruence.
  Qed.

  Lemma i3th_replace_Index_eq
    : forall {m : nat}
             {As : Vector.t A m}
             {Bs : ilist3 As}
             (i3l : i3list C Bs)
             (n : Fin.t m)
             (new_c : C (ith3 Bs n)),
      i3th (replace3_Index3 i3l n new_c) n = new_c.
  Proof.
    induction As.
    - intros; inversion n.
    - intros; revert As Bs i3l new_c IHAs; pattern n, n0.
      match goal with
        |- ?P n n0 => simpl; apply (@Fin.caseS P); clear n n0; simpl in *; eauto
      end.
  Qed.

  (*Program Fixpoint replace_Index3'
           (n : nat)
           (As : list A)
           (Bs : ilist B As)
           (Cs : i3list C Bs)
           (new_c : Dep_Option_elim_P C (ith_error Bs n))
           {struct Cs} : i3list C Bs :=
    match n return
          Dep_Option_elim_P C (ith_error Bs n)
            -> i3list C Bs with
      | 0 => match Cs in i3list _ Bs return
                   Dep_Option_elim_P C (ith_error Bs 0)
                   -> i3list C Bs with
                 | i3nil Bs =>
                   fun _ => i3nil _ Bs
                 | i3cons a As' Bs' c i3l' =>
                   fun new_c =>
                     i3cons Bs' new_c i3l'
               end
      | S n => match Cs in i3list _ Bs return
                     Dep_Option_elim_P C (ith_error Bs (S n))
                     -> i3list C Bs with
                 | i3nil Bs => fun _ => i3nil _ Bs
                 | i3cons a As' Bs' c i3l' =>
                   fun new_c =>
                     i3cons Bs' c (@replace_Index3' n As' (ilist_tl Bs') i3l' new_c)
               end
    end new_c.

  Lemma i3th_replace_Index'_neq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i3list C Bs)
      (n' : nat)
      (new_c : Dep_Option_elim_P C (ith_error Bs n')),
      n <> n'
      -> i3th_error' (replace_Index3' n' Cs new_c) n =
         i3th_error' Cs n.
  Proof.
    induction n; simpl; destruct Cs; intros; icons_invert;
    simpl in *; auto;
    destruct n'; simpl; try congruence.
    unfold replace_Index3.
    eapply IHn; congruence.
  Qed.

  Lemma i3th_replace_Index'_eq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i3list C Bs)
      (new_c : Dep_Option_elim_P C (ith_error Bs n)),
      i3th_error' (replace_Index3' n Cs new_c) n = new_c.
  Proof.
    induction n; destruct Cs; simpl; auto; intros;
    destruct new_c; eauto.
  Qed. *)

End i3list_replace.

  Lemma replace3_Index3_eq:
    forall (A : Type) (B : A -> Type) (C : forall a : A, B a -> Type)
           (m : nat) (As : Vector.t A m) (Bs : ilist3 As)
           (i3l : i3list C Bs) (n : Fin.t m),
      replace3_Index3 B C i3l n (i3th i3l n) = i3l.
  Proof.
    induction As.
    - intros; inversion n.
    - intros; revert As Bs i3l IHAs; pattern n, n0.
      match goal with
        |- ?P n n0 => simpl; apply (@Fin.caseS P); clear n n0; simpl in *; eauto
      end.
      + destruct i3l; simpl; reflexivity.
      + destruct i3l; simpl; intros.
        unfold i3cons; f_equal.
        eapply IHAs; eauto.
  Qed.

Lemma ilist3_eq_ith3
  : forall (A : Type) (B : A -> Type) C (m : nat) (As : Vector.t A m)
           (Bs : ilist3 As)
           (il il' : i3list (B := B) C Bs),
    (forall idx : Fin.t m, i3th il idx = i3th il' idx)
    -> il = il'.
Proof.
  induction As.
  - unfold ilist3; intros.
    destruct il; destruct il'; reflexivity.
  - intros.
    destruct il; destruct il'.
    f_equal; eauto.
    + apply (H (Fin.F1)).
    + eapply IHAs; intros.
      eapply (H (Fin.FS idx)).
Qed.
