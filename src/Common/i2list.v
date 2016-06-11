Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith
        Fiat.Common.ilist
        Fiat.Common.ilist2.

Section i2list.

  (* Lists of elements whose types depend on an indexing set (CPDT's hlists).
     These lists are a convenient way to implement finite maps
     whose elements depend on their keys. The data structures used
     by our ADT notations uses these to implement notation-friendly
     method lookups.  *)

  Import Vectors.VectorDef.VectorNotations.

  Context {A : Type}. (* The indexing type. *)
  Context {B : A -> Type}. (* The type of indexed elements. *)
  Variable C : forall a, B a ->  Type. (* The type of doubly-indexed elements. *)

  Fixpoint i2list {n}
           {l : Vector.t A n}
    : ilist2 (B := B) l -> Type :=
    match l return ilist2 (B := B) l -> Type with
    | [] => fun _ => unit
    | a :: l' => fun il => @prim_prod (C (ilist2_hd il))
                                      (i2list (ilist2_tl il))
    end.

  Definition i2cons
             {a : A}
             {n}
             {l : Vector.t A n}
             {b : B a}
             {il : ilist2 l}
             (c : C b)
             (il2 : i2list il)
  : i2list (icons2 b il)
    := {| prim_fst := c; prim_snd := il2 |}.

  Definition i2nil : i2list inil2 := tt.

  (* Get the car of an i2list. *)
  Definition i2list_hd {n}
             (As : Vector.t A n)
             (Bs : ilist2 As)
             (i2l : i2list Bs) :
    match As return forall Bs : ilist2 As, i2list Bs -> Type with
    | a :: As' => fun Bs i2l => C (ilist2_hd Bs)
      | [] => fun _ _ => unit
    end Bs i2l :=
    match As as As' return
          forall Bs i2l,
          match As' return forall Bs : ilist2 As', i2list Bs -> Type with
          | a :: As' => fun Bs i2l => C (ilist2_hd Bs)
          | [] => fun _ _ => unit
          end Bs i2l with
    | [] => fun _ _ => tt
    | a :: As' => fun Bs il => prim_fst il
    end Bs i2l.

  (* Get the cdr of an i2list. *)
  Definition i2list_tl {n}
             (As : Vector.t A n)
             (Bs : ilist2 As)
             (i2l : i2list Bs) :
    match As return forall Bs : ilist2 As, i2list Bs -> Type with
    | a :: As' => fun Bs i2l => i2list (ilist2_tl Bs)
    | [] => fun _ _ => unit
    end Bs i2l :=
    match As as As' return
          forall Bs i2l,
          match As' return forall Bs : ilist2 As', i2list Bs -> Type with
          | a :: As' => fun Bs i2l => i2list (ilist2_tl Bs)
          | [] => fun _ _ => unit
          end Bs i2l with
    | [] => fun _ _ => tt
    | a :: As' => fun Bs il => prim_snd il
    end Bs i2l.

  Fixpoint i2th
           {m : nat}
           {As : Vector.t A m}
           {Bs : ilist2 As}
           (i2l : i2list Bs)
           (n : Fin.t m)
           {struct n}
    : C (ith2 Bs n) :=
    match n in Fin.t m return
          forall (As : Vector.t A m)
                 (Bs : ilist2 As),
            i2list Bs
            -> C (ith2 Bs n) with
    | Fin.F1 k =>
      fun As Bs i2l =>
        Vector.caseS (fun n As =>
                        forall (Bs : ilist2 As), i2list Bs
                                   -> C (ith2 Bs (@Fin.F1 n)))
                     (fun a' n' As' (Bs' : ilist2 (a' :: As')) i2l' => prim_fst i2l' ) As Bs i2l
    | Fin.FS k n'' =>
      fun As Bs i2l =>
        Vector_caseS' Fin.t
                      (fun n' As i =>
                        forall (Bs'' : ilist2 As),
                          i2list Bs''
                          -> C (ith2 Bs'' (@Fin.FS n' i)))
                     (fun a' n' As' n'' (Bs' : ilist2 (a' :: As')) i2l' => i2th (prim_snd i2l') n'')
                     As n'' Bs i2l
    end As Bs i2l.

End i2list.

Arguments i2cons [_ _ _ _ _ _ _ _] _ _.
Arguments i2nil [_ _ _].
Arguments i2th [_ _ _ _ _ _] _ _.

Section i2list_replace.

  (* Replacing an element of an indexed list. *)
  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The two types of indexed elements. *)
  Variable C : forall a, B a -> Type. (* The type of doubly-indexed elements. *)

  Import Vectors.VectorDef.VectorNotations.

  Fixpoint replace2_Index2
          {m : nat}
          {As : Vector.t A m}
          {Bs : ilist2 As}
          (i2l : i2list C Bs)
          (n : Fin.t m)
          (new_c : C (ith2 Bs n))
    : i2list C Bs :=
        match n in Fin.t m return
          forall (As : Vector.t A m)
                 (Bs : ilist2 As),
            i2list C Bs
            -> C (ith2 Bs n)
            -> i2list C Bs with
        | Fin.F1 k =>
          fun As Bs i2l new_c =>
            Vector.caseS (fun n As =>
                            forall (Bs : ilist2 As), i2list C Bs
                                                     -> C (ith2 Bs (@Fin.F1 n))
                                                     -> i2list C Bs)
                         (fun a' n' As' (Bs' : ilist2 (a' :: As')) i2l' new_c => i2cons new_c (prim_snd i2l') ) As Bs i2l new_c
    | Fin.FS k n'' =>
      fun As Bs i2l new_c =>
        Vector.caseS (fun n' As =>
                        forall (i : Fin.t n') (Bs'' : ilist2 As),
                          i2list C Bs''
                          -> C (ith2 Bs'' (@Fin.FS n' i))
                          -> i2list C Bs'')
                     (fun a' n' As' n'' (Bs' : ilist2 (a' :: As')) i2l' new_c => i2cons (prim_fst i2l') (replace2_Index2 (prim_snd i2l') n'' new_c))
                     As n'' Bs i2l new_c
        end As Bs i2l new_c.

  Lemma i2th_replace_Index_neq
    : forall {m : nat}
             {As : Vector.t A m}
             {Bs : ilist2 As}
             (i2l : i2list C Bs)
             (n n' : Fin.t m)
             (new_c : C (ith2 Bs n)),
      n <> n'
      -> i2th (replace2_Index2 i2l n new_c) n' =
         i2th i2l n'.
  Proof.
    induction As.
    - intros; inversion n.
    - intros; revert n' As Bs i2l new_c H IHAs; pattern n, n0.
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

  Lemma i2th_replace_Index_eq
    : forall {m : nat}
             {As : Vector.t A m}
             {Bs : ilist2 As}
             (i2l : i2list C Bs)
             (n : Fin.t m)
             (new_c : C (ith2 Bs n)),
      i2th (replace2_Index2 i2l n new_c) n = new_c.
  Proof.
    induction As.
    - intros; inversion n.
    - intros; revert As Bs i2l new_c IHAs; pattern n, n0.
      match goal with
        |- ?P n n0 => simpl; apply (@Fin.caseS P); clear n n0; simpl in *; eauto
      end.
  Qed.

  (*Program Fixpoint replace_Index2'
           (n : nat)
           (As : list A)
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (new_c : Dep_Option_elim_P C (ith_error Bs n))
           {struct Cs} : i2list C Bs :=
    match n return
          Dep_Option_elim_P C (ith_error Bs n)
            -> i2list C Bs with
      | 0 => match Cs in i2list _ Bs return
                   Dep_Option_elim_P C (ith_error Bs 0)
                   -> i2list C Bs with
                 | i2nil Bs =>
                   fun _ => i2nil _ Bs
                 | i2cons a As' Bs' c i2l' =>
                   fun new_c =>
                     i2cons Bs' new_c i2l'
               end
      | S n => match Cs in i2list _ Bs return
                     Dep_Option_elim_P C (ith_error Bs (S n))
                     -> i2list C Bs with
                 | i2nil Bs => fun _ => i2nil _ Bs
                 | i2cons a As' Bs' c i2l' =>
                   fun new_c =>
                     i2cons Bs' c (@replace_Index2' n As' (ilist_tl Bs') i2l' new_c)
               end
    end new_c.

  Lemma i2th_replace_Index'_neq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i2list C Bs)
      (n' : nat)
      (new_c : Dep_Option_elim_P C (ith_error Bs n')),
      n <> n'
      -> i2th_error' (replace_Index2' n' Cs new_c) n =
         i2th_error' Cs n.
  Proof.
    induction n; simpl; destruct Cs; intros; icons_invert;
    simpl in *; auto;
    destruct n'; simpl; try congruence.
    unfold replace_Index2.
    eapply IHn; congruence.
  Qed.

  Lemma i2th_replace_Index'_eq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i2list C Bs)
      (new_c : Dep_Option_elim_P C (ith_error Bs n)),
      i2th_error' (replace_Index2' n Cs new_c) n = new_c.
  Proof.
    induction n; destruct Cs; simpl; auto; intros;
    destruct new_c; eauto.
  Qed. *)

End i2list_replace.
