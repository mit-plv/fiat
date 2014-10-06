Require Import List String Arith ilist i2list StringBound.

(* Typeclasses for ensuring that a string is included
   in a list (i.e. a set of method names). This allows
   us to omit a default case (method not found) for method
   lookups. *)

Section i2thIndexBound.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type} {D : Set}.
  Variable (projAD : A -> D).

  (* Given a [BoundedIndex] for a list [Bound], we can always return
     an element of a list indexed by [Bound]. *)

  Definition i2th_Bounded
          {B : A -> Type}
          {C : forall a, B a -> Type}
          {As}
          (Bs : ilist B As)
          (Cs : i2list C Bs)
          (idx : BoundedIndex (map projAD As))
  : C (nth_Bounded _ As idx) (ith_Bounded projAD Bs idx) :=
    ith_Bounded_rect projAD (fun _ _ _ => C) idx Bs
                           (i2th_error Cs (ibound idx)).

  (*Lemma ith_Bounded_imap
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
  Qed. *)

  (* We can lift [B (nth_Bounded idx)] to a dependent option. *)
  Definition Some_Dep_Option_elim_P
             {B : A -> Type}
             {C : forall a, B a -> Type}
             {As}
             (Bs : ilist B As)
             (Cs : i2list C Bs)
             (idx : BoundedIndex (map projAD As))
  : C _ (ith_Bounded _ Bs idx) ->
    Dep_Option_elim_P C (ith_error Bs (ibound idx)).
    unfold Dep_Option_elim_P, nth_Bounded, ith_Bounded.
    destruct (nth_error As (ibound idx)).
    unfold ith_Bounded.
    refine (match (ith_error Bound (ibound idx)) as e return
                  | Some a => fun c => Dep_Some _ _
              | None => fun c => None_neq_Some _ c
            end (nth_error_map _ _ (boundi idx))).

  Definition replace_BoundedIndex2
           {B : A -> Type}
           {C : forall a, B a -> Type}
           {As}
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (idx : BoundedIndex (map projAD As))
           (new_c : C _ (ith_Bounded projAD Bs idx))
  : i2list _ Bs :=
    replace_Index2 (ibound idx) Cs new_c.

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

  Lemma ilist_eq {B : A -> Type}
  : forall (Bound : list A)
           (il il' : ilist B Bound),
      (forall idx, ith_Bounded il idx = ith_Bounded il' idx) -> il = il'.
  Proof.
    induction Bound; intros.
    - rewrite (ilist_invert il), (ilist_invert il'); reflexivity.
    - icons_invert; f_equal.
      generalize (H {| bindex := projAC a |}).
      unfold ith_Bounded; simpl; auto.
      apply IHBound; intros.
      generalize (H  {| bindex := bindex idx;
                       indexb := @IndexBound_tail _ _ _ _ (indexb idx) |}).
      unfold ith_Bounded; simpl; auto.
  Qed.

  Lemma imap_replace_BoundedIndex
        {B B' : A -> Type}
  : forall (f : forall idx'', B idx'' -> B' idx'')
           (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist B Bound)
           b,
      imap B' f (replace_BoundedIndex il idx b) =
      replace_BoundedIndex (imap B' f il) idx (f _ b).
  Proof.
    intros; apply ilist_eq; intros.
    destruct (BoundedIndex_eq_dec C_eq_dec idx idx0); subst;
    rewrite <- ith_Bounded_imap.
    - repeat rewrite ith_replace_BoundIndex_eq; reflexivity.
    - repeat rewrite ith_replace_BoundIndex_neq; auto.
      rewrite <- ith_Bounded_imap; auto.
  Qed.

End ithIndexBound.

Arguments BoundedString [_].
