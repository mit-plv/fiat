Require Import List String Arith ilist.

(* Typeclasses for ensuring that a string is included
   in a list (i.e. a set of method names). This allows
   us to omit a default case (method not found) for method
   lookups. *)

Section IndexBound.

  Context {A : Set}.

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

  Section Bounded_Index_Dec_Eq.
  (* If equality on A is decideable, so is equality
     on bounded indices in in A. *)
    Variable A_eq_dec :
      forall a a' : A, {a = a'} + {a <> a'}.

    Require Import Eqdep_dec.

    Program Definition Opt_A_eq_dec (a a' : option A):
      {a = a'} + {a <> a'} :=
      match a as a, a' as a' return {a = a'} + {a <> a'} with
          | Some a, Some a' => if A_eq_dec a a' then left _ else right _
          | None, None => left _
          | _, _ => right _
      end.

    Definition K_Opt_A :
      forall (a : option A) (P: a = a -> Prop),
          P (refl_equal a) -> forall p : a = a, P p :=
      K_dec_set Opt_A_eq_dec.

    Definition UIP_Opt_A  :
      forall (a : option A) (Q : option A -> Type)
             (x : Q a) (h : a = a),
        x = eq_rect a Q x a h.
      intros; eapply K_Opt_A with (p := h); reflexivity.
    Defined.

    Lemma eq_proofs_unicity_Opt_A
      : forall (a a' : option A) (p1 p2 : a = a'), p1 = p2.
      apply eq_proofs_unicity; intros.
      destruct (Opt_A_eq_dec x y); auto.
    Qed.

    Corollary idx_ibound_eq
    : forall Bound (idx idx' : BoundedIndex Bound),
        ibound (indexb idx) = ibound (indexb idx') ->
        idx = idx'.
    Proof.
      intros; generalize (indexb_ibound_eq idx idx' H);
      destruct idx as [idx [n' In_n' ]];
        destruct idx' as [idx' [n'' In_n'' ]]; intros;
        simpl in *; subst; f_equal.
      rewrite (eq_proofs_unicity_Opt_A In_n' In_n''); auto.
    Qed.

    Corollary idx_ibound_neq
    : forall Bound (idx idx' : BoundedIndex Bound),
        ibound (indexb idx) <> ibound (indexb idx') ->
        idx <> idx'.
    Proof.
      intros; destruct idx as [idx [n' In_n' ]];
        destruct idx' as [idx' [n'' In_n'' ]]; intros;
        simpl in *; subst.
      unfold not; intros; apply H; injection H0; auto.
    Qed.

    Corollary BoundedIndex_eq_dec Bound :
      forall idx idx' : (BoundedIndex Bound),
        {idx = idx'} + {idx <> idx'}.
    Proof.
      intros; destruct (eq_nat_dec (ibound idx) (ibound idx')).
      - left; auto using idx_ibound_eq.
      - right; auto using idx_ibound_neq.
    Defined.

    End Bounded_Index_Dec_Eq.

End IndexBound.

Definition BoundedString := @BoundedIndex string.
Definition BoundedString_eq_dec
           {Bound}
           (bidx bidx' : BoundedString Bound)
: {bidx = bidx'} + {bidx <> bidx'} :=
  BoundedIndex_eq_dec string_dec  bidx bidx'.

Notation "` A ´" :=
  ({| bindex := A%string |}) (at level 0,
                              format "` A ´").

Section ithIndexBound.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type} {C : Set}.
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
  Defined.

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
             (P : forall a,
                    B a
                    -> B' a
                    -> B'' a
                    -> Prop)
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (b'_opt : Dep_Option B' a_opt)
             (b''_opt : Dep_Option B'' a_opt)
      := match a_opt as a return
               Dep_Option_elimT B a
               -> Dep_Option_elimT B' a
               -> Dep_Option_elimT B'' a
               -> Prop with
           | Some a => P a
           | _ => fun _ _ _ => True
         end (Dep_Option_elim b_opt)
             (Dep_Option_elim b'_opt)
             (Dep_Option_elim b''_opt).

    Program Definition ith_Bounded_ind3
            {B B' B'' : A -> Type}
            (P : forall As,
                   BoundedIndex (map projAC As)
                   -> ilist B As
                   -> ilist B' As
                   -> ilist B'' As
                   -> forall a : A,
                        B a -> B' a -> B'' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (il' : ilist B' Bound)
           (il'' : ilist B'' Bound),
      Dep_Option_elim_P3 (P Bound idx il il' il'')
                      (ith_error il (ibound idx))
                      (ith_error il' (ibound idx))
                      (ith_error il'' (ibound idx))
      -> P Bound idx il il' il'' _
           (ith_Bounded il idx)
           (ith_Bounded il' idx)
           (ith_Bounded il'' idx) :=
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
                   -> Dep_Option_elim_P3 (P Bound idx il il' il'') b b' b'' ->
                   P Bound idx il il' il''
                     (@nth_Bounded' _ _ _ c)
                     d d' d'' with
          | Some a => _
          | _  => _
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

  Variable C_eq_dec : forall c c' : C, {c = c'} + {c <> c'}.

  Lemma ith_replace_BoundIndex_neq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx idx' : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx')),
      idx <> idx'
      -> ith_Bounded (replace_BoundedIndex il idx' new_b) idx =
         ith_Bounded il idx.
  Proof.
    intros.
    eapply ith_Bounded_ind2 with (idx0 := idx) (il0 := replace_BoundedIndex il idx' new_b)
                                                (il' := il).
    eapply ith_replace_Index_neq; eauto using idx_ibound_eq.
  Qed.

  Lemma ith_replace_BoundIndex_eq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx)),
      ith_Bounded (replace_BoundedIndex il idx new_b) idx = new_b.
  Proof.
    intros.
    eapply ith_Bounded_ind with (idx0 := idx)
                                  (il0 := replace_BoundedIndex il idx new_b)
                                  (P := fun Bound idx il a il' b => il' = b).
    eapply ith_replace_Index_eq; eauto.
  Qed.

  Lemma ith_replace_BoundedIndex_ind
        {B : A -> Type}
        (P : forall As (idx : BoundedIndex (map projAC As)),
               B (nth_Bounded As idx)
               -> B (nth_Bounded As idx) -> Prop)
  : forall (Bound : list A)
           (idx idx' : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           (new_b : B (nth_Bounded Bound idx')),
      (forall idx :  BoundedIndex (map projAC Bound),
         ibound idx <> ibound idx'
         -> P _ idx (ith_Bounded il idx)
              (ith_Bounded il idx))
      -> P _ idx' (ith_Bounded il idx') new_b
      -> P _ idx
           (ith_Bounded il idx)
           (ith_Bounded (replace_BoundedIndex il idx' new_b) idx).
  Proof.
    intros.
    destruct (BoundedIndex_eq_dec C_eq_dec idx idx'); subst.
    + rewrite ith_replace_BoundIndex_eq; assumption.
    + rewrite ith_replace_BoundIndex_neq;
      unfold not; eauto using idx_ibound_eq.
  Qed.

  (*Definition transport_B
             {B : A -> Type}
             (a : A)
             (new_b : B a)
             (a' : A)
             (idx_eq_idx' : a = a')
  : B a'.
    rewrite idx_eq_idx' in new_b; eauto.
  Defined.

  Definition transport_P_B
             {B : A -> Type}
             (P : forall a, B a -> Prop)
  : forall (a a' : A)
      (a_eq_a' : a = a')
      (b : B a),
      P a b -> P a' (transport_B b a_eq_a').
  Proof.
    unfold transport_B; destruct a_eq_a'; unfold eq_rect;
    auto.
  Qed.

  Definition transport_P_B'
             {B : A -> Type}
             (P : forall a, B a -> Prop)
  : forall (a a' : A)
      (a_eq_a' : a = a')
      (b : B a),
      P a' (transport_B b a_eq_a') -> P a b.
  Proof.
    unfold transport_B; destruct a_eq_a'; unfold eq_rect;
    auto.
  Qed.

  Lemma ith_replace_BoundIndex_eq'
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx idx' : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx'))
      (idx'_eq_idx : ibound idx' = ibound idx),
      ith_Bounded (replace_BoundedIndex il idx' new_b) idx =
      transport_B new_b (nth_Bounded_eq Bound _ _ idx'_eq_idx).
  Proof.
    intros.
    assert (replace_BoundedIndex il idx' new_b =
            replace_BoundedIndex il idx
                                 (transport_B new_b (nth_Bounded_eq Bound _ _ idx'_eq_idx))).
    generalize (indexb_ibound_eq _ _ idx'_eq_idx).
    destruct idx as [idx [n nth_n ] ];
      destruct idx' as [idx' [n' nth_n' ] ];
      simpl in *; intros; subst.
    unfold transport_B, eq_rect.
    revert Bound il idx nth_n nth_n' new_b.
    induction n; destruct Bound; simpl; intros;
    try discriminate; icons_invert; simpl in *;
    unfold replace_BoundedIndex; simpl in *; f_equal.
    {

      unfold nth_Bounded in new_b; simpl in new_b.
      unfold nth_Bounded_eq; simpl.
      unfold nth_Bounded_ind2; simpl.
      unfold nth_Bounded_ind2_obligation_3; simpl.
      unfold value in *.
      injection nth_n; injection nth_n'; intros; subst.
      destruct nth_n.
      assert (forall (o : option C) (nth_n' : o = o),
                new_b =
                match
                  match nth_n' in (_ = y) return (y = o -> a = a) with
                    | eq_refl => fun _ : o = o => eq_refl
                  end eq_refl in (_ = y) return (B y)
                with
                  | eq_refl => new_b
                end) by (clear; destruct nth_n'; auto); auto. }
    f_equal.

    assert (forall n Bound idx nth_n nth_n' (b : B _),
              Dep_Option_elim (Some_Dep_Option Bound
                                               {| bindex := idx; indexb := {| ibound := n; boundi := nth_n |} |} b) =
              Dep_Option_elim
                (Some_Dep_Option Bound
                                 {| bindex := idx; indexb := {| ibound := n; boundi := nth_n' |} |}

(transport_B b ((nth_Bounded_eq Bound
{| bindex := idx; indexb := {| ibound := n; boundi := nth_n |} |}
{| bindex := idx; indexb := {| ibound := n; boundi := nth_n' |} |}
eq_refl))))).
    clear.
    intros.
    f_equal.
    unfold Some_Dep_Option; simpl.

    refine (match (nth_error Bound n) as e return
             forall (c : option_map projAC e = Some idx)
                    c' c''
                    (b' : B (nth_Bounded' Bound e c)),
               (*match e as e return
                      forall (c : option_map projAC e = Some idx)
                             (c' : option_map projAC e = Some idx),
                        B (nth_Bounded' Bound e c)
                        -> Prop with
                   | Some a => fun c c' b b' =>
                                 b = transport b'
                   | None => fun _ _ _ _ => True
                end c c' b'
               -> *) (*ith_error_eq_P Bound {| bindex := idx; indexb := {| ibound := n; boundi := nth_n' |} |} d' c' (transport_B b c') *)


 match
   e as e0
   return
     (forall c : option_map projAC e0 = Some idx,
      B (nth_Bounded' Bound e0 c) -> Dep_Option B e0)
 with
 | Some a => fun _ : Some (projAC a) = Some idx => Dep_Some B a
 | None =>
     fun c : None = Some idx =>
     None_neq_Some (B (None_neq_Some A c) -> Dep_Option B None) c
 end c b' =
 match
   e as e0
   return
     (forall c : option_map projAC e0 = Some idx,
      B (nth_Bounded' Bound e0 c) -> Dep_Option B e0)
 with
 | Some a => fun _ : Some (projAC a) = Some idx => Dep_Some B a
 | None =>
     fun c : None = Some idx =>
     None_neq_Some (B (None_neq_Some A c) -> Dep_Option B None) c
 end c' (transport_B b' c'') with
              | Some a => _
              | None => _
            end
              (nth_error_map n Bound nth_n)
              _ _
              b).
    simpl.
    intros; f_equal.
    unfold transport_B.



              (Some_Dep_Option _ _ b) _).
    cut (nth_error_map n Bound nth_n =
         nth_error_map n Bound nth_n').
    intro.
    rewrite H.
    f_equal.

              (Some_Dep_Option _ _
(match
     nth_Bounded_eq Bound
       {| bindex := idx; indexb := {| ibound := n; boundi := nth_n |} |}
       {| bindex := idx; indexb := {| ibound := n; boundi := nth_n' |} |}
       eq_refl in (_ = y) return (B y)
   with
   | eq_refl => b
   end)

) _ _ _); simpl; try discriminate; auto.
    intros; subst; eauto.
    unfold nth_Bounded, nth_Bounded' in b; simpl in b.
    refine (match (nth_error Bound n) as e return
             forall c c' c''
                    (b : B
         (match e as x return (option_map projAC x = Some idx -> A) with
          | Some a => fun _ : Some (projAC a) = Some idx => a
          | None => fun f : None = Some idx => None_neq_Some A f
          end c)),
 match
   e as e0
   return
     (forall c c' : option_map projAC e0 = Some idx,
      B (nth_Bounded' Bound e0 c) -> B (nth_Bounded' Bound e0 c') -> Prop)
 with
 | Some a => fun (_ _ : Some (projAC a) = Some idx) (b0 b' : B a) => b0 = b'
 | None =>
     fun (c c' : None = Some idx) (_ : B (None_neq_Some A c))
       (_ : B (None_neq_Some A c')) => True
 end c c' b
   match
     c'' in (_ = y) return (B y)
   with
   | eq_refl => b
   end with
              | Some a => _
              | None => _
            end _ _ _ _).
    simpl.
    intros; clear.
    destruct c''.
    revert b'; rewrite c''.
    destruct (nth_error Bound n).
    clear; intros; clear c c'.
    rewrite <- H, <- H0; clear H H0 b' b''.
    f_equal.
    unfold Dep_Option_elim.
    inversion d.
    Check (fun (o : option A) (d : Dep_Option B o) =>
 forall (d' : Dep_Option B o) (b'' b' : B a),
   Dep_Option_elim d = b' ->
   Dep_Option_elim d' = b'' -> Dep_Some B a b' = Dep_Some B a b'').
    destruct d.
    Check (fun (o : option A) (d : Dep_Option B o) =>
 forall d' : Dep_Option B o,
   Dep_Option_elim d = b' ->
   Dep_Option_elim d' = b'' -> Dep_Some B a b' = Dep_Some B a b').

    destruct d.
    inversion d.

    { intros; congruence. }
    { clear; unfold ith_error_eq_P; simpl.
      revert n nth_n nth_n' b; clear.
      induction Bound; destruct n; simpl; intros; eauto.
      unfold Some_Dep_Option; simpl.
      intros; eapply IHBound; auto.
    }
    { clear; unfold ith_error_eq_P; simpl.
      revert n nth_n nth_n' b; clear.
      induction Bound; destruct n; simpl; intros; eauto.
      unfold Some_Dep_Option; simpl.
      intros; eapply IHBound; auto.
    }
    { unfold Dep_Option_elim_P2; simpl.
      unfold nth_Bounded, nth_Bounded' in b; simpl in b.
      refine (match (nth_error Bound n) as e return
               forall b' b'', b' = b'' ->
 match
   e as a' return (Dep_Option_elimT B a' -> Dep_Option_elimT B a' -> Prop)
 with
 | Some a => fun b b' : B a => b = b'
 | None => fun _ _ : unit => True
 end b' b'' with
                | Some a => _
                | None => _
              end _ _ _)

   (Dep_Option_elim
      (Some_Dep_Option Bound
         {| bindex := idx; indexb := {| ibound := n; boundi := nth_n' |} |}
         match
           nth_Bounded_eq Bound
             {|
             bindex := idx;
             indexb := {| ibound := n; boundi := nth_n |} |}
             {|
             bindex := idx;
             indexb := {| ibound := n; boundi := nth_n' |} |} eq_refl
           in (_ = y) return (B y)
         with
         | eq_refl => b
         end))).

      destruct (nth_error Bound n).

 assert (forall eq_pf,
Dep_Option_elim_P2 (fun (a : A) (b0 b' : B a) => b0 = b')
     (Some_Dep_Option Bound
        {| bindex := idx; indexb := {| ibound := n; boundi := nth_n |} |} b)
     (Some_Dep_Option Bound
        {| bindex := idx; indexb := {| ibound := n; boundi := nth_n' |} |}
        match eq_pf in (_ = y) return (B y)
        with
        | eq_refl => b
        end)).
      unfold Dep_Option_elim_P2; simpl.
      revert n nth_n nth_n' b; clear.
      induction Bound; destruct n; simpl; intros; eauto.
      Focus 2.
      unfold Some_Dep_Option, Dep_Option_elim; simpl.

      -
        unfold nth_Bounded_eq, nth_Bounded_ind2,
        nth_Bounded_ind2_obligation_3; unfold nth_Bounded in *; simpl in *.
        clear; destruct nth_n'; destruct nth_n; auto.
      - unfold nth_Bounded in b; simpl in *.
        unfold Some_Dep_Option; simpl.
        unfold nth_Bounded_eq, nth_Bounded_ind2,
        nth_Bounded_ind2_obligation_3; simpl.
    }




    unfold ith_error_eq_P.
_ _ _).
    simpl.
    destruct (nth_error Bound n).
    { Focus 2.
      rewrite H.
      apply ith_replace_BoundIndex_eq. }.

    assert (forall n Bound idx nth_n nth_n' (b : B _),
              Dep_Option_elim (Some_Dep_Option Bound
                                               {| bindex := idx; indexb := {| ibound := n; boundi := nth_n |} |} b) =
              Dep_Option_elim
                (Some_Dep_Option Bound
                                 {| bindex := idx; indexb := {| ibound := n; boundi := nth_n' |} |}

(transport_B b ((nth_Bounded_eq Bound
{| bindex := idx; indexb := {| ibound := n; boundi := nth_n |} |}
{| bindex := idx; indexb := {| ibound := n; boundi := nth_n' |} |}
eq_refl))))).
    clear.
    unfold transport_B, eq_rect; simpl.
    unfold Some_Dep_Option, Dep_Option_elim, nth_Bounded; simpl.
    intros n Bound.
    unfold nth_error_map.
    unfold nth_Bounded'.
    destruct (nth_error Bound n).
    Check (fun e : option A =>
 forall (idx : C) (nth_n nth_n' : nth_error (map projAC Bound) n = Some idx)
   (b : B (nth_Bounded' Bound e (nth_error_map n Bound nth_n))),
 match
   match
     e as e0
     return
       (forall c : option_map projAC e0 = Some idx,
        B (nth_Bounded' Bound e0 c) -> Dep_Option B e0)
   with
   | Some a => fun _ : Some (projAC a) = Some idx => Dep_Some B a
   | None =>
       fun c : None = Some idx =>
       None_neq_Some (B (None_neq_Some A c) -> Dep_Option B None) c
   end (nth_error_map n Bound nth_n) b in (Dep_Option _ a_opt')
   return (Dep_Option_elimT B a_opt')
 with
 | Dep_Some _ b0 => b0
 | Dep_None => tt
 end =
 match
   match
     e as e0
     return
       (forall c : option_map projAC e0 = Some idx,
        B (nth_Bounded' Bound e0 c) -> Dep_Option B e0)
   with
   | Some a => fun _ : Some (projAC a) = Some idx => Dep_Some B a
   | None =>
       fun c : None = Some idx =>
       None_neq_Some (B (None_neq_Some A c) -> Dep_Option B None) c
   end (nth_error_map n Bound nth_n')
     match
       nth_Bounded_eq Bound
         {| bindex := idx; indexb := {| ibound := n; boundi := nth_n |} |}
         {| bindex := idx; indexb := {| ibound := n; boundi := nth_n' |} |}
         eq_refl in (_ = y) return (B y)
     with
     | eq_refl => b
     end in (Dep_Option _ a_opt') return (Dep_Option_elimT B a_opt')
 with
 | Dep_Some _ b0 => b0
 | Dep_None => tt
 end).

    intros n Bound; destruct (nth_error Bound n).
    induction n; destruct Bound; simpl; intro; try discriminate.
    intros.
    unfold nth_Bounded_eq; simpl.
    unfold nth_Bounded_ind2, nth_Bounded_ind2_obligation_3; simpl.
    unfold transport_B, eq_rect.
    unfold value in *; destruct nth_n'; destruct nth_n; auto.
    intros.
    unfold nth_Bounded' in b.
    unfold nth_Bounded_eq, transport_B, eq_rect; simpl.
    unfold nth_Bounded_ind2, nth_Bounded_ind2_obligation_5; simpl.


    unfold f_equal, eq_trans.
    destruct (idx_eq_idx').
    simpl.
    clear nth_n nth_n'.
    unfold transport_B.
    revert b; destruct idx'_eq_idx.
    unfold value.
    unfold


    simpl.
    intros.
    Check (Dep_Option_elim (Some_Dep_Option Bound0 idx0 b0)).

    Check    Dep_Option_elim.
     (Some_Dep_Option (a :: Bound)
        {| bindex := idx; indexb := {| ibound := S n; boundi := nth_n' |} |}
        new_b)

                refine (fun (o : Exc C) (nth_n' : o = o) =>
                          new_b =
 match
   match nth_n' in (_ = y) return (y = o -> a = a) with
   | eq_refl => fun _ : o = o => eq_refl
   end eq_refl in (_ = y) return (B y)
 with
 | eq_refl => new_b
 end).
    destruct nth_n'.
        unfold o in *.
    destruct nth_n'.
    Check (fun (o : Exc C) (nth_n :  = o) =>
             forall nth_n' : o = o,
 new_b =
 match
   match nth_n in (_ = y) return (y = o -> a = a) with
     | eq_refl =>
       fun _ : o = o =>
         match nth_n' in (_ = y) return (y = o -> a = a) with
       | eq_refl => fun _ : o = o => eq_refl
         end eq_refl
   end eq_refl in (_ = y) return (B y)
 with
   | eq_refl => new_b
 end).


    unfold nth_Bounded_eq; simpl.
    Focus 2.

    unfold replace_BoundedIndex; simpl; f_equal.
    unfold Some_Dep_Option; simpl.
    unfold nth_Bounded_eq; simpl
    eapply IHn.
    unfold nth_Bounded in new_b; simpl in new_b.
    unfold nth_Bounded_eq; simpl.
c    eapply
    induction n; simpl.

    destruct (nth_Bounded_eq Bound
    destruct idx'
    destruct idx; simpl in *.

    eapply transport_P_B with
    (P := fun idx'' new_b' =>
            replace_BoundedIndex il idx' new_b =
            replace_BoundedIndex il idx'' new_b').
            repla
    eapply transport_P_B with
    (P := fun idx' new_b =>
            ith_Bounded (replace_BoundedIndex il idx' new_b) idx =
            new_b).
            transport_B new_b (nth_Bounded_eq Bound idx' idx idx'_eq_idx)).

    intros.
    ith_Bounded (replace_BoundedIndex il idx' new_b) idx =

    eapply ith_Bounded_ind with (idx0 := idx)
                                  (il0 := replace_BoundedIndex il idx' new_b)
                                  (P := fun Bound idx il a il' b => il' = b).
    Check Some_Dep_Option.

    assert (Some_Dep_Option Bound idx
                            (transport_B new_b (nth_Bounded_eq Bound idx' idx idx'_eq_idx)) = Some_Dep_Option Bound idx' )

    unfold Dep_Option_elim_P2, Dep_Option_elim, Some_Dep_Option.

    rewrite <- idx'_eq_idx.

    eapply transport_P_B'.
    eapply ith_replace_Index_eq; eauto.
  Qed.

    eapply ith_Bounded_ind with (idx0 := idx)
                                  (il0 := replace_BoundedIndex il idx new_b)
                                  (P := fun Bound idx il a il' b => il' = b).
    eapply ith_replace_Index_eq; eauto.
  Qed.

  Lemma ith_replace_BoundIndex_agnostic
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist _ Bound)
      (idx idx'  idx'': BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded Bound idx'))
      (idx'_eq_idx'' : ibound idx' = ibound idx''),
      ith_Bounded (replace_BoundedIndex il idx' new_b) idx =
      ith_Bounded (replace_BoundedIndex
                     il idx''
                     (transport_B _ _ _ new_b idx'_eq_idx'')) idx.
  Proof.
    intros.

    destruct (eq_nat_dec (ibound idx) (ibound idx')).
    Focus 2.
    exists (transport_B _ H


    intros.
    eapply ith_Bounded_ind with (idx0 := idx)
                                  (il0 := replace_BoundedIndex il idx new_b)
                                  (P := fun Bound idx il a il' b => il' = b).
    eapply ith_replace_Index_eq; eauto.
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
    eapply (@ith_Bounded_ind3
              B B' D
              (fun As idx il il' il'' a b b' b'' => b'' = f a b b')
              Bound idx il il' (izip D f il il')).
    destruct idx as [idx [n nth_n ] ]; simpl in *; subst.
    generalize n il idx nth_n; clear.
    induction Bound; simpl;
    destruct n; simpl; auto; intros.
    eapply IHBound; eauto.
  Qed. *)

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
