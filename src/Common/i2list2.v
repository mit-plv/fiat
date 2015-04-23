Generalizable All Variables.
Set Implicit Arguments.

Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Arith Fiat.Common.ilist Fiat.Common.ilist2.

Section i2list2.

  (* Lists of elements whose types depend on a pairs of indexing set
     (CPDT's hlists). *)

  Variable A : Type. (* The indexing type. *)
  Variable B B' : A -> Type. (* The type of indexed elements. *)
  Variable C : forall a, B a -> B' a -> Type. (* The type of doubly-indexed elements. *)

  Inductive i2list2 : forall (As : list A),
                        ilist B As -> ilist B' As -> Type :=
  | i2cons2 : forall a As (Bs : ilist B (a :: As))
                     (Bs' : ilist B' (a :: As))
                     (c : C (ilist_hd Bs) (ilist_hd Bs')),
                i2list2 (ilist_tl Bs) (ilist_tl Bs') -> i2list2 Bs Bs'
  | i2nil2 : forall (Bs : ilist B nil)
                    (Bs' : ilist B' nil),
               i2list2 Bs Bs'.

  (* Get the car of an i2list2. *)

  Definition i2list2_hd (As : list A)
             (Bs : ilist B As)
             (Bs' : ilist B' As)
             (i2l : i2list2 Bs Bs') :
    match As return
          forall (Bs : ilist B As)
                 (Bs' : ilist B' As), i2list2 Bs Bs' -> Type with
      | a :: As' => fun Bs Bs' i2l => C (ilist_hd Bs) (ilist_hd Bs')
      | nil => fun _ _ _ => unit
    end Bs Bs' i2l :=
    match i2l with
      | i2cons2 a As Bs Bs' c i2l' => c
      | i2nil2 Bs Bs' => tt
    end.

  (* Get the cdr of an i2list2. *)
  Definition i2list2_tl (As : list A)
             (Bs : ilist B As)
             (Bs' : ilist B' As)
             (i2l : i2list2 Bs Bs') :
    match As as As' return
          forall (Bs : ilist B As')
                 (Bs' : ilist B' As'), i2list2 Bs Bs' -> Type with
      | a :: As' => fun Bs Bs' il => i2list2 (ilist_tl Bs) (ilist_tl Bs')
      | nil => fun _ _ _ => unit
    end Bs Bs' i2l :=
    match i2l with
      | i2cons2 a As Bs Bs' c i2l' => i2l'
      | i2nil2 Bs Bs' => tt
    end.

  (* Membership in a doubly-indexed list. *)
  Inductive i2list2_In
  : forall {a : A} {b : B a} {b' : B' a}
           (c : C b b') (As : list A)
           (il : ilist B As)
           (il' : ilist B' As)
           (i2l : i2list2 il il'), Prop :=
  | In2_hd : forall a' As
                    (Bs : ilist B (a' :: As))
                    (Bs' : ilist B' (a' :: As))
                    (i2l : i2list2 (ilist_tl Bs) (ilist_tl Bs')) c,
               i2list2_In c (i2cons2 Bs Bs' c i2l)
  | In2_tl : forall a a' As
                    (Bs : ilist B (a' :: As))
                    (Bs' : ilist B' (a' :: As))
                    (b : B a) (b' : B' a) c'
                    (i2l : i2list2 (ilist_tl Bs) (ilist_tl Bs'))
                    (c : C b b'),
               i2list2_In c i2l ->
               i2list2_In c (i2cons2 Bs Bs' c' i2l).

  (* Looking up the ith value, returning None for indices not in the list *)
  (* A doubly-dependent option. *)

  Fixpoint i2th_error2'
          (As : list A)
          (Bs : ilist B As)
          (Bs' : ilist B' As)
          (i2l : i2list2 Bs Bs')
          (n : nat)
          {struct n}
  : Dep_Option_elim_T2 C (ith_error Bs n) (ith_error Bs' n) :=
    match n as n' return
          forall (Bs : ilist B As)
                 (Bs' : ilist B' As),
            i2list2 Bs Bs'
            -> Dep_Option_elim_T2 C (ith_error Bs n') (ith_error Bs' n')
    with
      | 0 =>
        fun Bs Bs' i2l =>
          match i2l as i2l' in i2list2 Bss Bss' return
                Dep_Option_elim_T2 C (ith_error Bss 0) (ith_error Bss' 0) with
            | i2nil2 _ _ => tt
            | i2cons2 a As' Bss Bss' c i2l' => c
          end
      | S n => fun Bs Bs' i2l =>
                 match i2l as i2l' in i2list2 Bss Bss' return
                       Dep_Option_elim_T2 C (ith_error Bss (S n))
                                          (ith_error Bss' (S n)) with
                   | i2nil2 _ _ => tt
                   | i2cons2 a As' Bss Bss' c i2l' => i2th_error2' i2l' n
                 end
    end Bs Bs' i2l.

  (* Looking up the ith value, returning a default value
     for indices not in the list.
  Fixpoint i2th_default2
          (default_A : A)
          (default_B : B default_A)
          (default_C : C default_B)
          (As : list A)
          (Bs : ilist B As)
          (i2l : i2list2 Bs)
          (n : nat)
          {struct As}
  : C (ith2_default default_A default_B Bs n) :=
    match As as As', n as n' return
          forall (Bs' : ilist B As'),
            i2list2 Bs'
            -> C (ith2_default default_A default_B Bs' n') with
      | a :: As', 0    => @i2list2_hd (a :: As')
      | a :: As', S n' => fun il i2l => i2th_default2 default_C (i2list2_tl i2l) n'
      | nil      , 0    => fun il i2l => default_C
      | nil      , S n' => fun il i2l => default_C
    end Bs i2l.

  Lemma i2list2_invert (As : list A) (Bs : ilist B As) (Cs : i2list2 Bs):
    match Bs as Bs' return i2list2 Bs' -> Prop with
      | icons2 a As b Bs' => fun Cs =>
                           exists (c : C b) (Cs' : i2list2 Bs'),
                             Cs = i2cons2 (icons2 a b Bs') c Cs'
      | inil2 => fun Cs => Cs = i2nil2 (inil2 _)
    end Cs.
  Proof.
    destruct Cs.
    - destruct (ilist_invert Bs) as [b [Bs' Bs'_eq]]; subst.
      eexists; eauto.
    - pose (ilist_invert Bs) as Bs_eq; simpl in Bs_eq; subst; eauto.
  Qed.

  Lemma i2th_default2_In :
    forall (n : nat)
           (As : list A)
           (Bs : ilist B As)
           (Cs : i2list2 Bs)
           (default_A : A)
           (default_B : B default_A)
           (default_C : C default_B),
      n < List.length As ->
      i2list2_In (i2th_default2 default_C Cs n) Cs.
  Proof.
    ith2_induction n As; simpl;
    destruct (i2list2_invert Cs) as [c [Cs' Cs_eq]]; subst; simpl;
    [apply (In2_hd (icons2 a b il) Cs' c) |  constructor 2];
    eauto with arith.
  Qed.

  Lemma i2th_default2_indep :
    forall (n : nat)
           (As : list A)
           (Bs : ilist B As)
           (Cs : i2list2 Bs)
           (default_A : A)
           (default_B : B default_A)
           (default_C default_C' : C default_B),
      n < List.length As ->
      i2th_default2 default_C Cs n = i2th_default2 default_C' Cs n.
  Proof.
    ith_induction n As; simpl; eauto with arith.
  Qed. *)

End i2list2.
(*
Section i2list2_replace.

  (* Replacing an element of an indexed list. *)
  Variable A : Type. (* The indexing type. *)
  Variable B : A -> Type. (* The two types of indexed elements. *)
  Variable C : forall a, B a -> Type. (* The type of doubly-indexed elements. *)

  Program Fixpoint replace_2Index2
           (n : nat)
           (As : list A)
           (Bs : ilist B As)
           (Cs : i2list2 C Bs)
           (new_c : Dep_Option_elim_P C (ith2_error Bs n))
           {struct Bs} : i2list2 C Bs :=
    match n return
            i2list2 C Bs
            -> Dep_Option_elim_P C (ith2_error Bs n)
            -> i2list2 C Bs with
      | 0 => match Bs return
                     i2list2 C Bs
                     -> Dep_Option_elim_P C (ith2_error Bs 0)
                     -> i2list2 C Bs with
                 | inil2 =>
                   fun il _ => i2nil2 _ _
                 | icons2 a b As' Bs' =>
                   fun Cs' new_c =>
                     i2cons2 _ new_c (i2list2_tl Cs')
               end
      | S n => match Bs return
                     i2list2 C Bs
                     -> Dep_Option_elim_P C (ith2_error Bs (S n))
                     -> i2list2 C Bs with
                 | inil2 => fun il _ => i2nil2 _ _
                 | icons2 a As' b Bs' =>
                   fun Cs' new_c =>
                     i2cons2 _ (i2list2_hd Cs')
                            (@replace_2Index2 n As' Bs'
                                             (i2list2_tl Cs') new_c)
               end
    end Cs new_c.

  Lemma i2th_replace2_Index_neq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i2list2 C Bs)
      (n' : nat)
      (new_c : Dep_Option_elim_P C (ith2_error Bs n')),
      n <> n'
      -> i2th_error2 (replace_2Index2 n' Cs new_c) n =
         i2th_error2 Cs n.
  Proof.
    induction n; simpl; destruct Bs; intros; icons2_invert;
    simpl in *; auto;
    destruct n'; simpl; try congruence.
    eapply IHn; congruence.
  Qed.

  Lemma i2th_replace2_Index_eq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i2list2 C Bs)
      (new_c : Dep_Option_elim_P C (ith2_error Bs n)),
      i2th_error2 (replace_2Index2 n Cs new_c) n = new_c.
  Proof.
    induction n; destruct Bs; simpl; auto; intros;
    destruct new_c; eauto.
  Qed.

  Program Fixpoint replace_2Index2'
           (n : nat)
           (As : list A)
           (Bs : ilist B As)
           (Cs : i2list2 C Bs)
           (new_c : Dep_Option_elim_P C (ith2_error Bs n))
           {struct Cs} : i2list2 C Bs :=
    match n return
          Dep_Option_elim_P C (ith2_error Bs n)
            -> i2list2 C Bs with
      | 0 => match Cs in i2list2 _ Bs return
                   Dep_Option_elim_P C (ith2_error Bs 0)
                   -> i2list2 C Bs with
                 | i2nil2 Bs =>
                   fun _ => i2nil2 _ Bs
                 | i2cons2 a As' Bs' c i2l' =>
                   fun new_c =>
                     i2cons2 Bs' new_c i2l'
               end
      | S n => match Cs in i2list2 _ Bs return
                     Dep_Option_elim_P C (ith2_error Bs (S n))
                     -> i2list2 C Bs with
                 | i2nil2 Bs => fun _ => i2nil2 _ Bs
                 | i2cons2 a As' Bs' c i2l' =>
                   fun new_c =>
                     i2cons2 Bs' c (@replace_2Index2' n As' (ilist_tl Bs') i2l' new_c)
               end
    end new_c.

  Lemma i2th_replace_2Index2'_neq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i2list2 C Bs)
      (n' : nat)
      (new_c : Dep_Option_elim_P C (ith2_error Bs n')),
      n <> n'
      -> i2th_error2' (replace_2Index2' n' Cs new_c) n =
         i2th_error2' Cs n.
  Proof.
    induction n; simpl; destruct Cs; intros; icons2_invert;
    simpl in *; auto;
    destruct n'; simpl; try congruence.
    unfold replace_2Index2.
    eapply IHn; congruence.
  Qed.

  Lemma i2th_replace_2Index2'_eq
  : forall
      (n : nat)
      (As : list A)
      (Bs : ilist _ As)
      (Cs : i2list2 C Bs)
      (new_c : Dep_Option_elim_P C (ith2_error Bs n)),
      i2th_error2' (replace_2Index2' n Cs new_c) n = new_c.
  Proof.
    induction n; destruct Cs; simpl; auto; intros;
    destruct new_c; eauto.
  Qed.

End i2list2_replace. *)
