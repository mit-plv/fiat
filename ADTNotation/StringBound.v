Require Import List String Arith ilist.

(* Typeclasses for ensuring that a string is included
   in a list (i.e. a set of method names). This allows
   us to omit a default case (method not found) for method
   lookups. *)

Section IndexBound.

  Context {A : Type}.

  Class IndexBound (a : A) (Bound : list A) :=
    { ibound :> nat;
      boundi : nth_error Bound ibound = Some a}.

  Global Instance IndexBound_head (a : A) (Bound : list A)
  : IndexBound a (a :: Bound) :=
    {| ibound := 0;
       boundi := eq_refl|}.

  Global Instance IndexBound_tail
           (a a' : A) (Bound : list A)
           {sB' : IndexBound a Bound}
  : IndexBound a (a' :: Bound) :=
    {| ibound := S ibound;
       boundi := boundi |}.

  Definition tail_IndexBound
           (a : A) (Bound : list A)
           (n : nat)
           (nth_n : nth_error Bound n = Some a)
  : IndexBound a Bound :=
    {| ibound := n;
       boundi := nth_n |}.

  Global Arguments ibound [a Bound] _ .
  Global Arguments boundi [a Bound] _.

  Record BoundedIndex (Bound : list A) :=
    { bindex :> A;
      indexb :> IndexBound bindex Bound }.

  Global Arguments bindex [Bound] _ .
  Global Arguments indexb [Bound] _ .

  Lemma lt_nth :
    forall n As (a : A),
      nth_error As n = Some a
      -> n < List.length As.
  Proof.
    induction n; destruct As; simpl; intros;
    try auto with arith; try discriminate.
    apply lt_n_S; eauto with arith.
  Qed.

  Definition BoundedIndex_nil
             (AnyT : Type)
             (idx : BoundedIndex nil)
  : AnyT.
  Proof.
    destruct idx as [idx [n nth_n]].
    elimtype False; eapply lt_n_0.
    apply (lt_nth _ _ nth_n).
  Qed.

  Lemma indexb_ibound_eq :
    forall Bound (bidx bidx' : BoundedIndex Bound),
      ibound (indexb bidx) = ibound (indexb bidx') ->
      bindex bidx = bindex bidx'.
  Proof.
    intros; induction Bound; simpl in *.
    - apply BoundedIndex_nil; auto.
    - destruct bidx as [bindex [n nth_n]];
      destruct bidx' as [bindex' [n' nth_n']]; simpl in *; subst.
      congruence.
  Qed.

End IndexBound.

Definition BoundedString := @BoundedIndex string.
Definition BoundedString_eq {Bound} (bidx bidx' : BoundedString Bound) :=
  string_dec (bindex bidx) (bindex bidx').

Section ithIndexBound.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A C : Type}.
  Variable (projAC : A -> C).

  Lemma None_neq_Some
  : forall (AnyT AnyT' : Type) (a : AnyT),
      None = Some a -> AnyT'.
  Proof.
    intros; discriminate.
  Qed.

  (* Given a [BoundedIndex] for a list, we can always return an element. *)
  Definition nth_Bounded'
             (Bound : list A)
             (c : C)
             (a_opt : option A)
             (nth_n : option_map projAC a_opt = Some c)
  : A := match a_opt as x
               return (option_map projAC x = Some c) -> A with
             | Some a => fun _ => a
             | None => fun f => None_neq_Some _ f
         end nth_n.

  Lemma nth_error_map :
    forall n As c_opt,
      nth_error (map projAC As) n = c_opt
      -> option_map projAC (nth_error As n) = c_opt.
  Proof.
    induction n; destruct As; simpl; eauto.
  Defined.

  Definition nth_Bounded
             (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
  : A := nth_Bounded' Bound (nth_error Bound (ibound idx))
                      (nth_error_map _ _ (boundi idx)).

  (* We can lift [B (nth_Bounded idx)] to a dependent option. *)
  Definition Some_Dep_Option
             {B : A -> Type}
             (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
  : B (nth_Bounded Bound idx) ->
    Dep_Option B (nth_error Bound (ibound idx)) :=
    match (nth_error Bound (ibound idx)) as e return
           forall c,
             B (@nth_Bounded' _ _ e c) ->
              Dep_Option B e with
       | Some a => fun c => Dep_Some _ _
       | None => fun c => None_neq_Some _ c
     end (nth_error_map _ _ (boundi idx)).

  (* [nth_Bounded_rect] builds a function whose type depends
     on [nth_Bounded] by reducing to a case with [nth_error],
     which is easier to work/reason with. *)

  Definition nth_Bounded_rect
        (P : forall As, BoundedIndex (map projAC As) -> A -> Type)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound)),
      Dep_Option (P Bound idx) (nth_error Bound (ibound idx))
      -> P Bound idx (nth_Bounded Bound idx) :=
    fun Bound idx =>
      match (nth_error Bound (ibound idx)) as e
            return
            (forall (f : option_map _ e = Some (bindex idx)),
               (Dep_Option (P Bound idx) e) ->
               P _ _
                 (match e as e' return
                        option_map _ e' = Some (bindex idx)
                        -> A
                  with
                    | Some a => fun _ => a
                    | None => fun f => _
                  end f)) with
        | Some a => fun _ H => Dep_Option_elim H
        | None => fun f => None_neq_Some _ f
      end (nth_error_map _ _ (boundi idx)).

  (* [nth_Bounded_ind2] builds a function whose type depends
     on *two* occurences of [nth_Bounded] by reducing to a case
     with [nth_error], which is easier to reason with. *)

  Program Definition nth_Bounded_ind2
             (P : forall As, BoundedIndex (map projAC As)
                             -> BoundedIndex (map projAC As)
                             -> A -> A -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (idx' : BoundedIndex (map projAC Bound)),
      match nth_error Bound (ibound idx), nth_error Bound (ibound idx') with
          | Some a, Some a' => P Bound idx idx' a a'
          | _, _ => True
      end
      -> P Bound idx idx' (nth_Bounded _ idx) (nth_Bounded _ idx'):=
    fun Bound idx idx' =>
      match (nth_error Bound (ibound idx)) as e, (nth_error Bound (ibound idx')) as e'
            return
            (forall (f : option_map _ e = Some (bindex idx))
                    (f' : option_map _ e' = Some (bindex idx')),
               (match e, e' with
                  | Some a, Some a' => P Bound idx idx' a a'
                  | _, _ => True
                end)
               -> P Bound idx idx'
                 (match e as e'' return
                        option_map _ e'' = Some (bindex idx)
                        -> A
                  with
                    | Some a => fun _ => a
                    | _ => fun f => _
                  end f)
                 (match e' as e'' return
                        option_map _ e'' = Some (bindex idx')
                        -> A
                  with
                    | Some a => fun _ => a
                    | _ => fun f => _
                  end f')) with
        | Some a, Some a' => fun _ _ H => _
        | _, _ => fun f => _
      end (nth_error_map _ _ (boundi idx))
          (nth_error_map _ _ (boundi idx')).

  (* [nth_Bounded] returns the same elements as [nth_default] *)

  Lemma nth_Bounded_eq_nth_default
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (default_A : A),
      nth_Bounded Bound idx = nth (ibound idx) Bound default_A.
  Proof.
    intros Bound idx; eapply nth_Bounded_rect.
    case_eq (nth_error Bound (ibound idx)); econstructor; auto.
    intros; rewrite <- nth_default_eq; unfold nth_default;
    rewrite H; reflexivity.
  Qed.

  (* The result of [nth_Bounded] doesn't depend on the proof
     that [ibound] is a valid index. *)
  Lemma nth_Bounded_eq
  : forall (Bound : list A)
           (idx idx' : BoundedIndex (map projAC Bound)),
      ibound idx = ibound idx'
      -> nth_Bounded Bound idx = nth_Bounded Bound idx'.
  Proof.
    intros.
    eapply nth_Bounded_ind2 with (idx := idx) (idx' := idx').
    simpl.
    case_eq (nth_error Bound (ibound idx'));
      case_eq (nth_error Bound (ibound idx)); auto.
    congruence.
  Qed.

  (* Given a [BoundedIndex] for a list [Bound], we can always return
     an element of a list indexed by [Bound]. *)
  Definition ith_Bounded
          {B : A -> Type}
          {Bound}
          (il : ilist B Bound)
          (idx : BoundedIndex (map projAC Bound))
  : B (nth_Bounded Bound idx) :=
    match (nth_error Bound (ibound idx)) as a'
                  return
                  Dep_Option B a' ->
                  forall (f : option_map _ a' = Some (bindex idx)),
                    B (nth_Bounded' Bound _ f) with
        | Some a => fun b _ => Dep_Option_elim b
        | None => fun _ f => None_neq_Some _ f
    end (ith_error il (ibound idx)) (nth_error_map _ _ (boundi idx)).

  (* To build a reasoning principle for ith_Bounded, we need to
     show that option types are shuffled around by [Dep_Option_elim] *)
    Definition ith_error_eq_P
               {B : A -> Type}
               (Bound : list A)
               (idx : BoundedIndex (map projAC Bound))
               e' b c d :=
      match e' as e'
        return
        (Dep_Option B e' ->
         forall c : option_map _ e' = Some (bindex idx),
           B (nth_Bounded' Bound _ c) -> Type)
      with
        | Some e =>
          fun b c d => Dep_Option_elim b = d
        | None => fun b c d => True
      end b c d.

    Lemma ith_error_eq
          {B : A -> Type}
    : forall (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
              (il : ilist B Bound),
        ith_error_eq_P Bound idx
        (ith_error il (ibound idx))
        (nth_error_map _ _ (boundi idx))
        (ith_Bounded il idx).
    Proof.
      unfold ith_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert n In_n; induction Bound; destruct n;
      simpl; eauto; intros.
      eapply IHBound.
    Qed.

  Definition Dep_Option_elim_P
             {B : A -> Type}
             (P : forall a, B a -> Type)
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
      := match a_opt as a' return
               Dep_Option_elimT B a' -> Type with
           | Some a => P a
           | None => fun _ => True
         end (Dep_Option_elim b_opt).

    (* [ith_Bounded_rect] builds a function whose type depends
     on [ith_Bounded] by reducing to a case with [ith_error],
     which is easier to work/reason with. *)

    Program Definition ith_Bounded_rect
            {B : A -> Type}
        (P : forall As, BoundedIndex (map projAC As)
                        -> ilist B As -> forall a : A, B a -> Type)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound),
      Dep_Option_elim_P (P Bound idx il) (ith_error il (ibound idx))
      -> P Bound idx il _ (ith_Bounded il idx) :=
    fun Bound idx il =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (c : option_map _ e = Some (bindex idx))
                        d,
                   (ith_error_eq_P Bound idx b c d)
                   -> Dep_Option_elim_P (P Bound idx il) b ->
                   P _ _ _ (@nth_Bounded' _ _ e c) d with
          | Some a => _
          | None => _
           end (ith_error il (ibound idx))
               _
               (ith_Bounded il idx)
               (ith_error_eq idx il).

    (* [ith_Bounded_ind] builds a proof whose type depends
     on both [nth_Bounded] and an occurence of [ith_Bounded] by reducing
     it to a case with an [ith_error], which is easier to reason with. *)

    Program Definition ith_Bounded_ind
            {B B' : A -> Type}
            (P : forall As, BoundedIndex (map projAC As)
                        -> ilist B As
                        -> forall a : A, B a -> B' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (b : B' (nth_Bounded Bound idx)),
      Dep_Option_elim_P2 (P Bound idx il) (ith_error il (ibound idx))
                      (Some_Dep_Option Bound idx b)
      -> P Bound idx il _ (ith_Bounded il idx) b :=
      fun Bound idx il b =>
        match (nth_error Bound (ibound idx)) as e
              return
              forall (b : Dep_Option B e)
                     (b' : Dep_Option B' e)
                     (c : option_map _ e = Some (bindex idx))
                     d d',
                (ith_error_eq_P Bound idx b c d)
                -> (ith_error_eq_P Bound idx b' c d')
                -> Dep_Option_elim_P2 (P Bound idx il) b b' ->
                P _ _ _ (@nth_Bounded' _ _ _ c) d d' with
          | Some a => _
          | None => _
        end (ith_error il (ibound idx))
            (Some_Dep_Option Bound idx b)
            _ 
            (ith_Bounded il idx)
            b
            (ith_error_eq idx il)
            _.
    Next Obligation.
      unfold ith_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert n In_n b; clear.
      induction Bound; destruct n; simpl; intros; eauto.
      unfold Some_Dep_Option; simpl.
      intros; eapply IHBound.
    Qed.

    (* [ith_Bounded_ind2] builds a proof whose type depends
     on *two* occurences of [ith_Bounded] by reducing  it to a case
     with two [ith_error]s, which is easier to reason with. *)

    Program Definition ith_Bounded_ind2
            {B B' : A -> Type}
            (P : forall As, BoundedIndex (map projAC As)
                        -> ilist B As
                        -> forall a : A, B a -> B' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (il' : ilist B' Bound),
      Dep_Option_elim_P2 (P Bound idx il)
                      (ith_error il (ibound idx))
                      (ith_error il' (ibound idx) )
      -> P Bound idx il _ (ith_Bounded il idx) (ith_Bounded il' idx) :=
    fun Bound idx il il' =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d',
                   (ith_error_eq_P Bound idx b c d)
                   -> (ith_error_eq_P Bound idx b' c d')
                   -> Dep_Option_elim_P2 (P Bound idx il) b b' ->
                   P _ _ _ (@nth_Bounded' _ _ _ c) d d' with
          | Some a => _
          | None => _
           end (ith_error il (ibound idx))
               (ith_error il' (ibound idx) )
               _
               (ith_Bounded il idx)
               (ith_Bounded il' idx)
               (ith_error_eq idx il)
               (ith_error_eq idx il').

  Definition Dep_Option_elim_P3
             {B B' B'' : A -> Type}
             (P : forall a, B a -> B' a -> B'' a -> Prop)
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (b'_opt : Dep_Option B' a_opt)
             (b''_opt : Dep_Option B'' a_opt)
      := match a_opt as a' return
               Dep_Option_elimT B a' 
               -> Dep_Option_elimT B' a' 
               -> Dep_Option_elimT B'' a' 
               -> Prop with
           | Some a => P a
           | None => fun _ _ _ => True
         end (Dep_Option_elim b_opt) 
             (Dep_Option_elim b'_opt)
             (Dep_Option_elim b''_opt).

    Program Definition ith_Bounded_ind3
            {B B' B'' : A -> Type}
            (P : forall As, BoundedIndex (map projAC As)
                        -> ilist B As
                        -> forall a : A, B a -> B' a -> B'' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (il' : ilist B' Bound)
           (il'' : ilist B'' Bound),
      Dep_Option_elim_P3 (P Bound idx il)
                      (ith_error il (ibound idx))
                      (ith_error il' (ibound idx))
                      (ith_error il'' (ibound idx))
      -> P Bound idx il _ 
           (ith_Bounded il idx) 
           (ith_Bounded il' idx)
           (ith_Bounded il'' idx):=
    fun Bound idx il il' il'' =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (b'' : Dep_Option B'' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d' d'',
                   (ith_error_eq_P Bound idx b c d)
                   -> (ith_error_eq_P Bound idx b' c d')
                   -> (ith_error_eq_P Bound idx b'' c d'')
                   -> Dep_Option_elim_P3 (P Bound idx il) b b' b'' ->
                   P _ _ _ (@nth_Bounded' _ _ _ c) d d' d'' with
          | Some a => _
          | None => _
           end (ith_error il (ibound idx))
               (ith_error il' (ibound idx) )
               (ith_error il'' (ibound idx) )
               _
               (ith_Bounded il idx)
               (ith_Bounded il' idx)
               (ith_Bounded il'' idx)
               (ith_error_eq idx il)
               (ith_error_eq idx il')
               (ith_error_eq idx il'').

  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    intros.
    eapply ith_Bounded_ind2 with (idx0 := idx) (il0 := il) (il' := imap B' f il).
    destruct idx as [idx [n nth_n] ]; simpl in *; subst.
    revert Bound nth_n il;
      induction n; destruct Bound; simpl; eauto;
    intros; icons_invert; simpl; auto.
  Qed.

  Definition replace_BoundedIndex
           {B : A -> Type}
           (Bound : list A)
           (il : ilist B Bound)
           (idx : BoundedIndex (map projAC Bound))
           (new_b : B (nth_Bounded Bound idx))
  : ilist B Bound :=
    replace_Index (ibound idx) il (Dep_Option_elim (Some_Dep_Option _ _ new_b)).

  Lemma ith_replace_BoundIndex_neq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx idx' : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx)),
      ibound idx <> ibound idx'
      -> ith_Bounded (replace_BoundedIndex il idx new_b) idx' =
         ith_Bounded il idx'.
  Proof.
    intros.
    eapply ith_Bounded_ind2 with (idx0 := idx') (il0 := replace_BoundedIndex il idx new_b)
                                                (il' := il).
    eapply ith_replace_Index_neq; eauto.
  Qed.

  Lemma ith_replace_BoundedIndex_ind
        {B : A -> Type}
        (P : forall a : A, B a -> B a -> Prop)
  : forall (Bound : list A)
           (idx idx' : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (new_b : B (nth_Bounded Bound idx')),
      (forall idx :  BoundedIndex (map projAC Bound),
         ibound idx <> ibound idx'
         -> P (nth_Bounded Bound idx)
              (ith_Bounded il idx)
              (ith_Bounded il idx))
      -> P  _ (ith_Bounded il idx') new_b
      -> P _
           (ith_Bounded il idx)
           (ith_Bounded (replace_BoundedIndex il idx' new_b) idx).
  Proof.
    intros.
    destruct (eq_nat_dec (ibound idx) (ibound idx')).
    {
      eapply ith_Bounded_ind2 with
      (idx0 := idx)
        (il0 := il)
        (il' := replace_BoundedIndex il idx' new_b).
      rewrite e.
      unfold replace_BoundedIndex.
      clear idx H e.
      destruct idx' as [idx' [n nth_n ] ]; simpl in *; subst.
      generalize n il idx' nth_n  new_b H0; clear.
      induction Bound; simpl;
      destruct n; simpl; auto; intros.
      unfold Some_Dep_Option; simpl in *.
      eapply IHBound; eauto.
    }
    erewrite ith_replace_BoundIndex_neq; eauto.
  Qed.

  Lemma ith_Bounded_izip 
        {B B' D : A -> Type}
        (f : forall a, B a -> B' a -> D a)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (il' : ilist B' Bound),
      ith_Bounded (izip _ f il il') idx =
      f _ (ith_Bounded il idx) (ith_Bounded il' idx).
  Proof.
    intros.
    eapply ith_Bounded_ind3 with 
    (idx0 := idx)
      (il0 := il)
      (il'0 := il').
      destruct idx as [idx [n nth_n ] ]; simpl in *; subst.
      generalize n il idx nth_n; clear.
      induction Bound; simpl;
      destruct n; simpl; auto; intros.
      eapply IHBound; eauto.
  Qed.

End ithIndexBound.

  (* Lemma ith_Bounded_lt
          {B : A -> Type}
  : forall (n : nat)
           (Bound : list A)
           (lt_n lt_n' : n < Datatypes.length Bound)
           (il : ilist B Bound),
      ith_error lt_n il =
      ith_error lt_n' il .
  Proof.
    induction n;
    (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption |
      simpl ]); auto.
  Qed.

  Program Definition ith_Bounded
          {B : A -> Type}
          {Bound}
          (il : ilist B Bound)
          (idx : BoundedIndex Bound)
  : B (nth_Bounded Bound idx) :=
    @ith_error B (ibound idx) Bound _ _.

  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           {As}
           (idx : BoundedIndex (map projAC As))
           (il : ilist B As),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    destruct idx as [idx [n nth_n lt_n]]; subst; simpl.
    revert As nth_n lt_n; unfold nth_Bounded; simpl; induction n; intros;
    (destruct As; [intros; elimtype False; eapply lt_n_0; eassumption
                  | generalize (ilist_invert il);
                    intros; subst; simpl; destruct H as [b [il' il_eq]]; subst;
                    simpl; auto]).
    simpl in lt_n.
    unfold ith_Bounded, ith_error; simpl.
    simpl.
    unfold ith_Bounded; simpl.
      simpl.
      unfold nth_Bounded; simpl.
      Set Printing All.
      idtac.
      case_eq ( @ibound C (@bindex C (projAC a :: @map A C projAC As) idx)
         (projAC a :: @map A C projAC As) idx); intros.
      simpl in *.
      rewrite H.
      destruct (ibound idx).
case_eq (ibound idx); simpl;
      intros; subst.

      rewrite H.
      unfold ith_Bounded_obligation_1; auto.
      destruct idx as [idx [[idx_eq | idx_In]]]; subst; simpl.
      + destruct (AC_eq a (projAC a));  congruence.
      + destruct (AC_eq a idx); try congruence.
        rewrite <- IHAs; reflexivity.
  Qed.

  Lemma ith_Bounded_Sn :
    forall (a : A) b il idx n
           (nth_n : forall a' : C, nth (S n) (map projAC (a :: b)) a' = idx)
           (lt_n : S n < Datatypes.length (map projAC (a :: b))),
      (ith_Bounded (icons a b il)
                   {| bindex := idx;
                      indexb := {| ibound := S n; boundi := nth_n; ibound_lt := lt_n |} |}) =
      ith_Bounded il {| bindex := idx;
                        indexb := (tail_IndexBound idx _ n nth_n lt_n) |}.
  Proof.
    simpl; unfold ith_Bounded. simpl; intros.
    unfold nth_Bounded_obligation_1; simpl.
    unfold ith_Bounded_obligation_1.
    f_equal.
    revert lt_n; clear; induction b; simpl; auto.
    intros.
    unfold map_length_obligation_1; simpl.
    unfold eq_ind, eq_rect; simpl.

    unfold nth_Bounded_obligation_1; destruct b; simpl.
    unfold ith_Bounded_obligation_2, ith_Bounded_obligation_1; simpl.
    unfold map_length_obligation_1, f_equal; simpl.
    unfold ith_error at 1; simpl.
    unfold map_length, list_ind, list_rect, f_equal; simpl.
    destruct b; simpl; unfold map_length_obligation_1, f_equal; simpl.


    simpl.


  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           {As}
           (idx : BoundedIndex (map projAC As))
           (il : ilist B As),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    destruct idx as [idx [n nth_n lt_n]]; subst; simpl.
    revert As nth_n lt_n; unfold nth_Bounded; simpl; induction n; intros;
    (destruct As; [intros; elimtype False; eapply lt_n_0; eassumption
                  | generalize (ilist_invert il);
                    intros; subst; simpl; destruct H as [b [il' il_eq]]; subst;
                    simpl; auto]).
    simpl in lt_n.
    unfold ith_Bounded, ith_error; simpl.
    simpl.
    unfold ith_Bounded; simpl.
      simpl.
      unfold nth_Bounded; simpl.
      Set Printing All.
      idtac.
      case_eq ( @ibound C (@bindex C (projAC a :: @map A C projAC As) idx)
         (projAC a :: @map A C projAC As) idx); intros.
      simpl in *.
      rewrite H.
      destruct (ibound idx).
case_eq (ibound idx); simpl;
      intros; subst.

      rewrite H.
      unfold ith_Bounded_obligation_1; auto.
      destruct idx as [idx [[idx_eq | idx_In]]]; subst; simpl.
      + destruct (AC_eq a (projAC a));  congruence.
      + destruct (AC_eq a idx); try congruence.
        rewrite <- IHAs; reflexivity.
  Qed.

  Fixpoint replace_BoundIndex
           {B : A -> Type}
           (As : list A)
           (il : ilist B As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx))
           {struct As} : ilist B As.
  Proof.
    refine (match As as As' return
                  forall (idx : BoundedIndex (map projAC As')),
                    ilist B As'
                  -> B (nth_Bounded As' idx)
                  -> ilist B As' with
              | a :: As' => (fun idx il' new_b' => _)
              | _ => fun idx il' new_b' => inil _
            end idx il new_b).
    simpl in *.
    destruct (AC_eq a (bindex (projAC a :: map projAC As') idx0)).
    exact (icons _ new_b' (ilist_tail il')).
    exact (icons _ (ilist_hd il')
                 (replace_BoundIndex B As' (ilist_tail il')
                                     (BoundIndex_tail idx0 n) new_b')).
  Defined.

  Lemma ith_replace_BoundIndex_neq
        {B : A -> Type}
  : forall (As : list A)
           (il : ilist _ As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx))
           (idx' : BoundedIndex (map projAC As))
           c_neq,
      AC_eq (nth_Bounded As idx) (bindex _ idx') = right c_neq
      -> ith_Bounded (replace_BoundIndex il idx new_b) idx' =
      ith_Bounded il idx'.
  Proof.
    induction As; intros; subst; auto.
    simpl in *.
    destruct (AC_eq a (bindex (projAC a :: map projAC As) idx));
      try rewrite H in *; simpl; auto.
    destruct (AC_eq a (bindex (projAC a :: map projAC As) idx')); eauto.
  Qed.

  Lemma ith_replace_BoundIndex_eq
        {B : A -> Type}
  : forall (As : list A)
           (il : ilist _ As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx)),
      ith_Bounded (replace_BoundIndex il idx new_b) idx = new_b.
  Proof.
    induction As; intros; subst.
    - exact (Not_BoundedIndex_nil idx).
    - simpl in *;
      destruct (AC_eq a (bindex (projAC a :: map projAC As) idx));
      simpl; eauto.
  Qed.

End ithIndexBound.


  Fixpoint nth_Bounded'
          (n : nat)
          (Bound : list A)
          (lt_n : n < List.length Bound)
          {struct n}
  : A :=
    match n as n' return
          n' < List.length Bound -> A with
      | 0 => match Bound as Bound' return
                   0 < List.length Bound' -> A with
               | nil => fun lt_0 => match (lt_n_0 _ lt_0) with end
               | cons a Bound' => fun lt_0 => a
             end
      | S n => match Bound as Bound' return
                     S n < List.length Bound' -> A with
                 | nil =>
                   fun lt_Sn => match (lt_n_0 _ lt_Sn) with end
                 | cons a Bound' =>
                   fun lt_Sn => @nth_Bounded' n Bound' (lt_S_n _ _ lt_Sn)
               end
    end lt_n.

  Program Fixpoint map_length
          (A B : Type) (f : A -> B) (l : list A)
  : Datatypes.length (map f l) = Datatypes.length l :=
    match l as l' return
          Datatypes.length (map f l') = Datatypes.length l' with
        | nil => eq_refl
        | cons a l' => (fun H => _) (map_length f l')
    end.

  Lemma nth_Bounded_lt_agnostic
  : forall (n : nat)
           (Bound : list A)
           lt lt',
      @nth_Bounded' n Bound lt =
      @nth_Bounded' n Bound lt' .
    induction n;
    (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption
     | simpl; intros]); auto.
  Qed.

  (* Local Obligation Tactic := intros.

  Program Fixpoint map_length_lt
          (As : list A)
          (n : nat)
  : n < List.length (map projAC As) ->
    n < List.length As :=
    match As as As' return
          n < List.length (map projAC As') ->
          n < List.length As' with
      | nil => fun len_n => len_n
      | cons a As' =>
        match n with
          | 0 => (fun HInd len_n => _) (@map_length_lt As' 0)
          | S n => (fun HInd len_n => _ ) (@map_length_lt As' (S n))
        end
    end.
  Next Obligation.
    simpl in *.
    econstructor.
    e
    auto with arith. *)

  Program Definition nth_Bounded
          (Bound : list A)
          (idx : BoundedIndex Bound)
  : A := @nth_Bounded' (ibound idx) Bound _.
  Next Obligation.
    generalize (ibound_lt idx); clear.
    rewrite map_length; auto.
  Defined.

  Lemma nth_Bounded_eq
  : forall (n : nat)
           (default_A : A)
           (Bound : list A)
           (lt_n : n < List.length Bound),
      nth_Bounded' Bound lt_n = nth n Bound default_A.
  Proof.
    induction n; (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption
     | simpl; intros]); auto.
  Qed.

  (* Lemma nth_Bounded_eq_nth :
    forall (default_A : A)
           (As : list A)
           (idx : BoundedIndex (map projAC As)),
      nth_Bounded As idx =
      nth (findIndex AC_eq_bool As (bindex _ idx)) As default_A .
  Proof.
    induction As; simpl; intros.
    - eapply Not_BoundedIndex_nil; eauto.
    - unfold AC_eq_bool.
      destruct (AC_eq a (bindex (projAC a :: map projAC As) idx)); auto.
      eapply IHAs.
  Qed.

  Global Arguments nth_Bounded_obligation_1 _ _ _ _ _ _ _ / . *)

  Fixpoint ith_error
          {B : A -> Type}
          (n : nat)
          (Bound : list A)
          (lt_n : n < Datatypes.length Bound)
          (il : ilist B Bound)
          {struct n}
  : B (nth_Bounded' Bound lt_n) :=
    match n as n' return
          forall (lt_n : n' < Datatypes.length Bound),
            ilist B Bound
            -> B (nth_Bounded' Bound lt_n)
    with
      | 0 => match Bound as Bound' return
                   forall lt_0 : 0 < Datatypes.length Bound',
                     ilist B Bound'
                     -> B (nth_Bounded' Bound' lt_0) with
               | nil => fun lt_0 il =>
                          match (lt_n_0 _ lt_0) with end
               | cons a Bound' => fun lt_0 il => ilist_hd il
             end
      | S n => match Bound as Bound' return
                     forall (lt_Sn : (S n) < Datatypes.length Bound'),
                       ilist B Bound'
                       -> B (nth_Bounded' Bound' lt_Sn) with
                 | nil =>
                   fun lt_Sn il =>
                     match (lt_n_0 _ lt_Sn) with end
                 | cons a Bound' =>
                   fun lt_Sn il =>
                     @ith_error B n _
                                   (lt_S_n _ _ lt_Sn) (ilist_tail il)
             end
    end lt_n il.

  (* Lemma ith_Bounded_lt
          {B : A -> Type}
  : forall (n : nat)
           (Bound : list A)
           (lt_n lt_n' : n < Datatypes.length Bound)
           (il : ilist B Bound),
      ith_error lt_n il =
      ith_error lt_n' il .
  Proof.
    induction n;
    (destruct Bound;
     [intros; elimtype False; eapply lt_n_0; eassumption |
      simpl ]); auto.
  Qed. *)

  Program Definition ith_Bounded
          {B : A -> Type}
          {Bound}
          (il : ilist B Bound)
          (idx : BoundedIndex Bound)
  : B (nth_Bounded Bound idx) :=
    @ith_error B (ibound idx) Bound _ _.

  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           {As}
           (idx : BoundedIndex (map projAC As))
           (il : ilist B As),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    destruct idx as [idx [n nth_n lt_n]]; subst; simpl.
    revert As nth_n lt_n; unfold nth_Bounded; simpl; induction n; intros;
    (destruct As; [intros; elimtype False; eapply lt_n_0; eassumption
                  | generalize (ilist_invert il);
                    intros; subst; simpl; destruct H as [b [il' il_eq]]; subst;
                    simpl; auto]).
    simpl in lt_n.
    unfold ith_Bounded, ith_error; simpl.
    simpl.
    unfold ith_Bounded; simpl.
      simpl.
      unfold nth_Bounded; simpl.
      Set Printing All.
      idtac.
      case_eq ( @ibound C (@bindex C (projAC a :: @map A C projAC As) idx)
         (projAC a :: @map A C projAC As) idx); intros.
      simpl in *.
      rewrite H.
      destruct (ibound idx).
case_eq (ibound idx); simpl;
      intros; subst.

      rewrite H.
      unfold ith_Bounded_obligation_1; auto.
      destruct idx as [idx [[idx_eq | idx_In]]]; subst; simpl.
      + destruct (AC_eq a (projAC a));  congruence.
      + destruct (AC_eq a idx); try congruence.
        rewrite <- IHAs; reflexivity.
  Qed.

  Lemma ith_Bounded_Sn :
    forall (a : A) b il idx n
           (nth_n : forall a' : C, nth (S n) (map projAC (a :: b)) a' = idx)
           (lt_n : S n < Datatypes.length (map projAC (a :: b))),
      (ith_Bounded (icons a b il)
                   {| bindex := idx;
                      indexb := {| ibound := S n; boundi := nth_n; ibound_lt := lt_n |} |}) =
      ith_Bounded il {| bindex := idx;
                        indexb := (tail_IndexBound idx _ n nth_n lt_n) |}.
  Proof.
    simpl; unfold ith_Bounded. simpl; intros.
    unfold nth_Bounded_obligation_1; simpl.
    unfold ith_Bounded_obligation_1.
    f_equal.
    revert lt_n; clear; induction b; simpl; auto.
    intros.
    unfold map_length_obligation_1; simpl.
    unfold eq_ind, eq_rect; simpl.

    unfold nth_Bounded_obligation_1; destruct b; simpl.
    unfold ith_Bounded_obligation_2, ith_Bounded_obligation_1; simpl.
    unfold map_length_obligation_1, f_equal; simpl.
    unfold ith_error at 1; simpl.
    unfold map_length, list_ind, list_rect, f_equal; simpl.
    destruct b; simpl; unfold map_length_obligation_1, f_equal; simpl.


    simpl.


  Lemma ith_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           {As}
           (idx : BoundedIndex (map projAC As))
           (il : ilist B As),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap B' f il) idx.
  Proof.
    destruct idx as [idx [n nth_n lt_n]]; subst; simpl.
    revert As nth_n lt_n; unfold nth_Bounded; simpl; induction n; intros;
    (destruct As; [intros; elimtype False; eapply lt_n_0; eassumption
                  | generalize (ilist_invert il);
                    intros; subst; simpl; destruct H as [b [il' il_eq]]; subst;
                    simpl; auto]).
    simpl in lt_n.
    unfold ith_Bounded, ith_error; simpl.
    simpl.
    unfold ith_Bounded; simpl.
      simpl.
      unfold nth_Bounded; simpl.
      Set Printing All.
      idtac.
      case_eq ( @ibound C (@bindex C (projAC a :: @map A C projAC As) idx)
         (projAC a :: @map A C projAC As) idx); intros.
      simpl in *.
      rewrite H.
      destruct (ibound idx).
case_eq (ibound idx); simpl;
      intros; subst.

      rewrite H.
      unfold ith_Bounded_obligation_1; auto.
      destruct idx as [idx [[idx_eq | idx_In]]]; subst; simpl.
      + destruct (AC_eq a (projAC a));  congruence.
      + destruct (AC_eq a idx); try congruence.
        rewrite <- IHAs; reflexivity.
  Qed.

  Fixpoint replace_BoundIndex
           {B : A -> Type}
           (As : list A)
           (il : ilist B As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx))
           {struct As} : ilist B As.
  Proof.
    refine (match As as As' return
                  forall (idx : BoundedIndex (map projAC As')),
                    ilist B As'
                  -> B (nth_Bounded As' idx)
                  -> ilist B As' with
              | a :: As' => (fun idx il' new_b' => _)
              | _ => fun idx il' new_b' => inil _
            end idx il new_b).
    simpl in *.
    destruct (AC_eq a (bindex (projAC a :: map projAC As') idx0)).
    exact (icons _ new_b' (ilist_tail il')).
    exact (icons _ (ilist_hd il')
                 (replace_BoundIndex B As' (ilist_tail il')
                                     (BoundIndex_tail idx0 n) new_b')).
  Defined.

  Lemma ith_replace_BoundIndex_neq
        {B : A -> Type}
  : forall (As : list A)
           (il : ilist _ As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx))
           (idx' : BoundedIndex (map projAC As))
           c_neq,
      AC_eq (nth_Bounded As idx) (bindex _ idx') = right c_neq
      -> ith_Bounded (replace_BoundIndex il idx new_b) idx' =
      ith_Bounded il idx'.
  Proof.
    induction As; intros; subst; auto.
    simpl in *.
    destruct (AC_eq a (bindex (projAC a :: map projAC As) idx));
      try rewrite H in *; simpl; auto.
    destruct (AC_eq a (bindex (projAC a :: map projAC As) idx')); eauto.
  Qed.

  Lemma ith_replace_BoundIndex_eq
        {B : A -> Type}
  : forall (As : list A)
           (il : ilist _ As)
           (idx : BoundedIndex (map projAC As))
           (new_b : B (nth_Bounded As idx)),
      ith_Bounded (replace_BoundIndex il idx new_b) idx = new_b.
  Proof.
    induction As; intros; subst.
    - exact (Not_BoundedIndex_nil idx).
    - simpl in *;
      destruct (AC_eq a (bindex (projAC a :: map projAC As) idx));
      simpl; eauto.
  Qed.

End ithIndexBound. *)
