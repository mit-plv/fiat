Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Arith.Arith.
Require Coq.Vectors.Vector.
Global Set Asymmetric Patterns.

(* Typeclasses for ensuring that a string is included
   in a list (i.e. a set of method names). This allows
   us to omit a default case (method not found) for method
   lookups. *)

Section BoundedIndex.

  Context {A : Type}.

  Class IndexBound n
        (a : A)
        (Bound : Vector.t A n)
    :=
      { ibound : Fin.t n;
        boundi : Vector.nth Bound ibound = a
      }.

  Global Arguments ibound {n a Bound} IndexBound.
  Global Arguments IndexBound {n} a Bound.

  Record BoundedIndex
         (n : nat)
         (Bound : Vector.t A n) :=
    { bindex : A;
      indexb : IndexBound bindex Bound
    }.

  Import Vectors.VectorDef.VectorNotations.

  Definition BoundedIndex_nil
             (AnyT : Type)
             (idx : BoundedIndex 0 [])
  : AnyT.
  Proof.
    destruct idx as [idx [n] nth_n].
    inversion n.
  Qed.

  Global Arguments indexb {n Bound} b.
  Global Arguments bindex {n Bound} b.
  Global Arguments BoundedIndex {n} Bound%vector_scope.

  Lemma indexb_ibound_eq :
    forall n Bound (bidx bidx' : BoundedIndex (n := n) Bound),
      ibound (indexb bidx) = ibound (indexb bidx') ->
      bindex bidx = bindex bidx'.
  Proof.
    intros; induction Bound; simpl in *.
    - apply BoundedIndex_nil; auto.
    - destruct bidx as [bindex [n'] nth_n];
      destruct bidx' as [bindex' [n''] nth_n']; simpl in *; subst.
      congruence.
  Qed.

  Section Bounded_Index_Dec_Eq.
  (* If equality on A is decideable, so is equality
     on bounded indices in A. *)
    Variable A_eq_dec :
      forall a a' : A, {a = a'} + {a <> a'}.

    Require Import Coq.Logic.Eqdep_dec.

    Program Definition Opt_A_eq_dec (a a' : option A) :
      {a = a'} + {a <> a'} :=
      match a as a, a' as a' return {a = a'} + {a <> a'} with
          | Some a, Some a' => if A_eq_dec a a' then left _ else right _
          | None, None => left _
          | _, _ => right _
      end.

    (*Definition K_Opt_A :
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
    Defined. *)

    Corollary idx_ibound_eq
    : forall n Bound (idx idx' : BoundedIndex (n := n) Bound),
        ibound (indexb idx) = ibound (indexb idx') ->
        idx = idx'.
    Proof.
      intros; generalize (indexb_ibound_eq _ _ idx idx' H);
      destruct idx as [idx [n'] In_n'];
        destruct idx' as [idx' [n''] In_n'' ]; intros;
        simpl in *; subst; f_equal.
    Qed.

    Corollary idx_ibound_neq
    : forall n Bound (idx idx' : BoundedIndex (n := n) Bound),
        ibound (indexb idx) <> ibound (indexb idx') ->
        idx <> idx'.
    Proof.
      intros; destruct idx as [idx [n'] In_n' ];
        destruct idx' as [idx' [n''] In_n'' ]; intros;
        simpl in *; subst.
      unfold not; intros; apply H; injection H0; auto.
    Qed.

    Definition fin_eq_dec {m} (n n' : Fin.t m)
      : {n = n'} + {n <> n'}.
    Proof.
      eapply Fin.rect2 with (P := fun m (n n' : Fin.t m)
                                  => {n = n'} + {n <> n'}).
      - left; reflexivity.
      - right; intro; discriminate.
      - right; intro; discriminate.
      - destruct 1; subst.
        + left; reflexivity.
        + right; intro H; apply Fin.FS_inj in H; eauto.
    Defined.

    Corollary BoundedIndex_eq_dec n Bound :
      forall idx idx' : BoundedIndex (n := n) Bound,
        {idx = idx'} + {idx <> idx'}.
    Proof.
      intros; destruct (fin_eq_dec (ibound (indexb idx)) (ibound (indexb idx'))).
      - left; auto using idx_ibound_eq.
      - right; auto using idx_ibound_neq.
    Defined.

    Fixpoint fin_beq {m n} (p : Fin.t m) (q : Fin.t n) :=
      match p, q with
      | @Fin.F1 m', @Fin.F1 n' => EqNat.beq_nat m' n'
      | Fin.FS _ _, Fin.F1 _ => false
      | Fin.F1 _, Fin.FS _ _ => false
      | Fin.FS _ p', Fin.FS _ q' => fin_beq p' q'
      end.

    Lemma fin_beq_dec {n}
      : forall (p : Fin.t n) (q : Fin.t n),
        fin_beq p q = true <-> p = q.
    Proof.
      intros; pattern n, p, q; eapply Fin.rect2; simpl;
        intuition; try (congruence || discriminate).
      - symmetry; eapply beq_nat_refl.
      - eauto using Fin.FS_inj.
    Qed.

    Corollary fin_beq_neq_dec {n}
      : forall (p : Fin.t n) (q : Fin.t n),
        fin_beq p q = false <-> p <> q.
    Proof.
      intros; setoid_rewrite <- fin_beq_dec; split;
        intros; destruct (fin_beq p q); congruence.
    Qed.

    Corollary fin_beq_refl {m}
      : forall (p : Fin.t m),
        fin_beq p p = true.
    Proof.
      intros; eapply fin_beq_dec; reflexivity.
    Qed.

    Corollary fin_beq_sym {n}
      : forall (p : Fin.t n) (q : Fin.t n),
        fin_beq p q = fin_beq q p.
    Proof.
      intros; case_eq (fin_beq p q); case_eq (fin_beq q p);
        intros; eauto.
      - apply fin_beq_neq_dec in H; apply fin_beq_dec in H0;
          congruence.
      - apply fin_beq_neq_dec in H0; apply fin_beq_dec in H;
          congruence.
    Qed.

    Corollary fin_beq_trans {n}
      : forall (p q r : Fin.t n),
        fin_beq p q = true ->
        fin_beq q r = true ->
        fin_beq p q = true.
    Proof.
      repeat setoid_rewrite fin_beq_dec; congruence.
    Qed.

    Definition BoundedIndex_beq {n Bound}
               (idx idx' : BoundedIndex (n := n) Bound)
      : bool := fin_beq (ibound (indexb idx)) (ibound (indexb idx')).

    Corollary BoundedIndex_beq_dec {n Bound}
      : forall (idx idx' : BoundedIndex (n := n) Bound),
        BoundedIndex_beq idx idx' = true <-> idx = idx'.
    Proof.
      intros; setoid_rewrite fin_beq_dec; split; intros.
      - eauto using idx_ibound_eq.
      - subst; reflexivity.
    Qed.

    Corollary BoundedIndex_beq_neq_dec {n Bound}
      : forall (idx idx' : BoundedIndex (n := n) Bound),
        BoundedIndex_beq idx idx' = false <-> idx <> idx'.
    Proof.
      intros; setoid_rewrite <- BoundedIndex_beq_dec; split;
        intros; destruct (BoundedIndex_beq idx idx'); congruence.
    Qed.

    Corollary BoundedIndex_beq_refl {m Bound}
      : forall (p : BoundedIndex (n := m) Bound),
        BoundedIndex_beq p p = true.
    Proof.
      intros; eapply BoundedIndex_beq_dec; reflexivity.
    Qed.

    Corollary BoundedIndex_beq_sym {n Bound}
      : forall (p q : BoundedIndex (n := n) Bound),
        BoundedIndex_beq p q = BoundedIndex_beq q p.
    Proof.
      intros; case_eq (BoundedIndex_beq p q); case_eq (BoundedIndex_beq q p);
        intros; eauto.
      - apply BoundedIndex_beq_neq_dec in H; apply BoundedIndex_beq_dec in H0;
          congruence.
      - apply BoundedIndex_beq_neq_dec in H0; apply BoundedIndex_beq_dec in H;
          congruence.
    Qed.

    Corollary BoundedIndex_beq_trans {n Bound}
      : forall (p q r : BoundedIndex (n := n) Bound),
        BoundedIndex_beq p q = true ->
        BoundedIndex_beq q r = true ->
        BoundedIndex_beq p q = true.
    Proof.
      repeat setoid_rewrite BoundedIndex_beq_dec; congruence.
    Qed.

  End Bounded_Index_Dec_Eq.

End BoundedIndex.

Section BoundedIndexExtensions.
  (* Helper functions for extending the set of Bounded Indexes *)

  Lemma IndexBound_AppendR {A n m}
  : forall (Bound : Vector.t A n)
           (Bound' : Vector.t A m)
           (idx : Fin.t n),
    Vector.nth (Vector.append Bound Bound') (Fin.L m idx) =
    Vector.nth Bound idx.
  Proof.
    induction Bound; intros.
    - inversion idx.
    - revert Bound IHBound; pattern n, idx; apply Fin.caseS;
        simpl; intros; eauto.
  Qed.

  Definition BoundedIndex_injR {A n Bound m Bound'}
             (idx : BoundedIndex (A := A) (n := n) Bound)
    : BoundedIndex (n := n + m) (Vector.append Bound Bound').
    refine {| bindex := bindex idx;
              indexb :=  {| ibound := Fin.L _ (ibound (indexb idx))|}
           |}.
    (* Abstract Proof Term. *)
    abstract (rewrite <- (boundi (IndexBound := indexb idx));
              eapply IndexBound_AppendR).
  Defined.

  Lemma IndexBound_AppendL {A n m}
    : forall (Bound : Vector.t A n)
             (Bound' : Vector.t A m)
             (idx : Fin.t n),
      Vector.nth (Vector.append Bound' Bound) (Fin.R m idx) =
      Vector.nth Bound idx.
  Proof.
    induction Bound'; intros.
    - reflexivity.
    - simpl; eauto.
  Qed.

  Definition BoundedIndex_injL {A n Bound m Bound'}
             (idx : BoundedIndex (A := A) (n := n) Bound)
    : BoundedIndex (n := m + n) (Vector.append Bound' Bound).
    refine {| bindex := bindex idx;
              indexb :=  {| ibound := Fin.R _ (ibound (indexb idx))|}
           |}.
    (* Abstract Proof Term. *)
    abstract (rewrite <- (boundi (IndexBound := indexb idx));
              eapply IndexBound_AppendL).
  Defined.

End BoundedIndexExtensions.

Ltac Build_nth_IndexBound n A a As As' m :=
  match n with
  | S ?n' =>
    (let check := constr:(eq_refl : a = Vector.hd As') in (* Check if the terms match *)
     exact (@Build_IndexBound A _ a As (Fin.R m (@Fin.F1 n'))
                              (@eq_refl A a)))
      ||
      let As'' := eval simpl in (Vector.tl As') in
          Build_nth_IndexBound n' A a As As'' (S m)
  end.

Hint Extern 0 (@IndexBound ?A ?n ?a ?As) =>
let n' := eval compute in n in
    Build_nth_IndexBound n' A a As As 0 : typeclass_instances.

(*
Import Vectors.VectorDef.VectorNotations.

Fixpoint foo (n : nat) : Vector.t nat (S n) :=
  match n with
  | 0 => 0 :: []
  | S n' => (S n') * (S n') * (S n') :: (foo n')
  end.

Definition foo100 := Eval simpl in foo 20.

Definition baz := Eval simpl in 3 * 3 * 3.

Definition bar : IndexBound baz foo100.
Proof.
  Unset Ltac Debug.
  Time eauto with typeclass_instances.
Defined. *)

Definition BoundedString {n} := @BoundedIndex string n.
Definition BoundedString_eq_dec
           {n}
           {Bound}
           (bidx bidx' : BoundedString Bound)
: {bidx = bidx'} + {bidx <> bidx'} :=
  BoundedIndex_eq_dec n Bound bidx bidx'.

Notation "x ++ y" := (Vector.append x y) : vector_scope.

Notation "`` A" :=
  ({| bindex := A%string |}) (at level 0, format "`` A").

Arguments BoundedString {n} _%vector_scope.

Section ithIndexBound.

  Require Import Fiat.Common.ilist.
  Import Vectors.VectorDef.VectorNotations.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type}.

  Lemma None_neq_Some
  : forall (AnyT AnyT' : Type) (a : AnyT),
      None = Some a -> AnyT'.
  Proof.
    intros; discriminate.
  Qed.

  Definition nth_Bounded
             {n}
             (Bound : Vector.t A n)
             (idx : BoundedIndex Bound)
    : A := Vector.nth Bound (ibound (indexb idx)).

  Definition ith_Bounded
             {m}
             {B : A -> Type}
             {Bound : Vector.t A m}
             (il : ilist Bound)
             (idx : BoundedIndex Bound)
    : B (Vector.nth Bound (ibound (indexb idx))) :=
    ith il (ibound (indexb idx)) .

  Lemma ith_Bounded_imap
        {m}
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           (Bound : Vector.t A m)
           (idx : BoundedIndex Bound)
           (il : ilist Bound),
      f _ (ith_Bounded il idx) =
      ith_Bounded (imap _ _ f Bound il) idx.
  Proof.
    unfold ith_Bounded; simpl; intros; eapply ith_imap.
  Qed.

  Definition replace_BoundedIndex
             {m}
           {B : A -> Type}
           (Bound : Vector.t A m)
           (il : ilist Bound)
           (idx : BoundedIndex Bound)
           (new_b : B (nth_Bounded idx))
  : ilist Bound :=
    replace_Index Bound il (ibound (indexb idx)) new_b.

  Lemma ith_replace_BoundIndex_neq
        {m}
        {B : A -> Type}
  : forall
      (Bound : Vector.t A m)
      (il : ilist Bound)
      (idx idx' : BoundedIndex Bound)
      (new_b : B (nth_Bounded idx')),
      idx <> idx'
      -> ith_Bounded (replace_BoundedIndex il idx' new_b) idx =
         ith_Bounded il idx.
  Proof.
    unfold ith_Bounded; simpl; intros; eapply ith_replace_Index_neq.
    eauto using idx_ibound_eq.
  Qed.

  Lemma ith_replace_BoundIndex_eq
        {m}
        {B : A -> Type}
  : forall
      (Bound : Vector.t A m)
      (il : ilist Bound)
      (idx : BoundedIndex Bound)
      (new_b : B (nth_Bounded idx)),
      ith_Bounded (replace_BoundedIndex il idx new_b) idx = new_b.
  Proof.
    unfold ith_Bounded; simpl; intros; eapply ith_replace_Index_eq.
  Qed.

  Lemma ilist_eq {m} {B : A -> Type}
  : forall (Bound : Vector.t A m)
           (il il' : ilist (B := B) Bound),
      (forall idx, ith_Bounded il idx = ith_Bounded il' idx) -> il = il'.
  Proof.
    induction Bound; intros.
    - rewrite (ilist_invert _ il), (ilist_invert _ il'); reflexivity.
    - destruct il; destruct il'; simpl in *.
      f_equal.
      + generalize (H {| bindex := h |});
        unfold ith_Bounded; simpl; auto.
      + apply IHBound; intros.
        exact (H {| bindex := bindex idx;
                   indexb := @Build_IndexBound
                               _
                               (S n)
                               (bindex idx)
                               (h :: Bound)
                               (Fin.FS (ibound (indexb idx)))
                               (@boundi _ _ _ _ (indexb idx))
                |}).
  Qed.

  Global Arguments imap {A B B'} f {n} {As} il.
  Global Arguments BoundedIndex_eq_dec {_ _ _} _ _.

  Lemma imap_replace_BoundedIndex
        {m}
        {B B' : A -> Type}
  : forall (f : forall idx'', B idx'' -> B' idx'')
           (Bound : Vector.t A m)
           (idx : BoundedIndex Bound)
           (il : ilist Bound)
           b,
      imap f (replace_BoundedIndex il idx b) =
      replace_BoundedIndex (imap f il) idx (f _ b).
  Proof.
    intros; apply ilist_eq; intros.
    destruct (BoundedIndex_eq_dec idx idx0); subst;
    rewrite <- ith_Bounded_imap.
    - repeat rewrite ith_replace_BoundIndex_eq; reflexivity.
    - repeat rewrite ith_replace_BoundIndex_neq; auto.
      rewrite <- ith_Bounded_imap; auto.
  Qed.

End ithIndexBound.

Section ithIndexBound2.

  Require Import Fiat.Common.ilist2.
  Import Vectors.VectorDef.VectorNotations.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type}.

  Definition ith_Bounded2
             {m}
             {B : A -> Type}
             {Bound : Vector.t A m}
             (il : ilist2 Bound)
             (idx : BoundedIndex Bound)
    : B (Vector.nth Bound (ibound (indexb idx))) :=
    ith2 il (ibound (indexb idx)) .

  Lemma ith_Bounded_imap2
        {m}
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           (Bound : Vector.t A m)
           (idx : BoundedIndex Bound)
           (il : ilist2 Bound),
      f _ (ith_Bounded2 il idx) =
      ith_Bounded2 (imap2 _ _ f Bound il) idx.
  Proof.
    unfold ith_Bounded2; simpl; intros; eapply ith_imap2.
  Qed.

  Definition replace_BoundedIndex2
             {m}
           {B : A -> Type}
           (Bound : Vector.t A m)
           (il : ilist2 Bound)
           (idx : BoundedIndex Bound)
           (new_b : B (nth_Bounded idx))
  : ilist2 Bound :=
    replace_Index2 Bound il (ibound (indexb idx)) new_b.

  Lemma ith_replace_BoundIndex2_neq
        {m}
        {B : A -> Type}
  : forall
      (Bound : Vector.t A m)
      (il : ilist2 Bound)
      (idx idx' : BoundedIndex Bound)
      (new_b : B (nth_Bounded idx')),
      idx <> idx'
      -> ith_Bounded2 (replace_BoundedIndex2 il idx' new_b) idx =
         ith_Bounded2 il idx.
  Proof.
    unfold ith_Bounded2; simpl; intros; eapply ith_replace2_Index_neq.
    eauto using idx_ibound_eq.
  Qed.

  Lemma ith_replace_BoundIndex2_eq
        {m}
        {B : A -> Type}
  : forall
      (Bound : Vector.t A m)
      (il : ilist2 Bound)
      (idx : BoundedIndex Bound)
      (new_b : B (nth_Bounded idx)),
      ith_Bounded2 (replace_BoundedIndex2 il idx new_b) idx = new_b.
  Proof.
    unfold ith_Bounded2; simpl; intros; eapply ith_replace2_Index_eq.
  Qed.

  Lemma ilist2_eq {m} {B : A -> Type}
  : forall (Bound : Vector.t A m)
           (il il' : ilist2 (B := B) Bound),
      (forall idx, ith_Bounded2 il idx = ith_Bounded2 il' idx) -> il = il'.
  Proof.
    induction Bound; intros.
    - rewrite (ilist2_invert _ il), (ilist2_invert _ il'); reflexivity.
    - destruct il; destruct il'; simpl in *.
      f_equal.
      + generalize (H {| bindex := h |});
        unfold ith_Bounded2; simpl; auto.
      + apply IHBound; intros.
        exact (H {| bindex := bindex idx;
                   indexb := @Build_IndexBound
                               _
                               (S n)
                               (bindex idx)
                               (h :: Bound)
                               (Fin.FS (ibound (indexb idx)))
                               (@boundi _ _ _ _ (indexb idx))
                |}).
  Qed.

  Global Arguments imap2 {A B B'} f {n} {As} il.

  Lemma imap_replace2_BoundedIndex
        {m}
        {B B' : A -> Type}
  : forall (f : forall idx'', B idx'' -> B' idx'')
           (Bound : Vector.t A m)
           (idx : BoundedIndex Bound)
           (il : ilist2 Bound)
           b,
      imap2 f (replace_BoundedIndex2 il idx b) =
      replace_BoundedIndex2 (imap2 f il) idx (f _ b).
  Proof.
    intros; apply ilist2_eq; intros.
    destruct (BoundedIndex_eq_dec idx idx0); subst;
    rewrite <- ith_Bounded_imap2.
    - repeat rewrite ith_replace_BoundIndex2_eq; reflexivity.
    - repeat rewrite ith_replace_BoundIndex2_neq; auto.
      rewrite <- ith_Bounded_imap2; auto.
  Qed.

End ithIndexBound2.

(*Section i2thIndexBound.

  Require Import Fiat.Common.i2list.

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
                           (i2th_error' Cs (ibound idx)).

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

  (* We can lift [C (ith_Bounded idx)] to a dependent option. *)
  Definition Some_Dep_Option_elim_P
             {B : A -> Type}
             {C : forall a, B a -> Type}
             (As : list A)
             (Bs : ilist B As)
             (idx : BoundedIndex (map projAD As))
             (c_opt : C (nth_Bounded projAD As idx) (ith_Bounded projAD Bs idx))
  : Dep_Option_elim_P C (ith_error Bs (ibound idx)) :=
    match (nth_error As (ibound idx)) as e return
          forall nth_n
                 (b : B (@nth_Bounded' _ _ _ _ _ e nth_n))
                 b_opt,
            ith_error_eq_P projAD As idx
                           b_opt
                           nth_n
                           b
            -> C _ b
            -> Dep_Option_elim_P C (a_opt := e) b_opt with
      | Some a => fun nth_n b b_opt b_eq c =>
                    match b_eq in _ = b'
                          return C _ b' -> _ with
                      | eq_refl => fun c => c
                    end c
      | None => fun nth_n b b_opt b_eq c => I
    end (nth_error_map _ _ _ (boundi idx))
        _ _ (ith_error_eq _ _ _) c_opt.

  Definition replace_BoundedIndex2
           {B : A -> Type}
           {C : forall a, B a -> Type}
           {As}
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (idx : BoundedIndex (map projAD As))
           (new_c : C _ (ith_Bounded projAD Bs idx))
  : i2list C Bs :=
    replace_Index2' (ibound idx) Cs
                   (Some_Dep_Option_elim_P Bs idx new_c).

  Definition Dep_Option_elim2_P2
             {B : A -> Type}
             {C C' : forall a, B a -> Type}
             (P : forall a b, C a b -> C' a b -> Prop)
             (a_opt : option A)
    := match a_opt return
             forall (b : Dep_Option B a_opt),
               Dep_Option_elim_P C (a_opt := a_opt) b
               -> Dep_Option_elim_P C' (a_opt := a_opt) b -> Prop with
         | Some a => fun b => P a (Dep_Option_elim b)
         | None => fun _ _ _ => True
       end .

  Lemma Dep_Option_elim2_P2_refl
        {B : A -> Type}
        {C : forall a, B a -> Type}
  : forall a_opt b_opt c_opt,
      Dep_Option_elim2_P2 (fun (a : A) (b : B a) (c c' : C a b) => c = c')
                          (a_opt := a_opt) b_opt c_opt c_opt.
    unfold Dep_Option_elim2_P2; destruct a_opt; eauto.
  Qed.

  Definition i2th_error_eq_P
             {B : A -> Type}
             {C : forall a, B a -> Type}
             (As : list A)
             (idx : BoundedIndex (map projAD As))
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (c_opt : Dep_Option_elim_P C b_opt)
             (e_eq : option_map projAD a_opt = Some (bindex idx))
             (c_opt' : C (nth_Bounded' projAD As a_opt e_eq)
                         (ith_Bounded' projAD As e_eq b_opt))
  : Type :=
      match a_opt as a_opt'
        return
        forall (b_opt : Dep_Option B a_opt')
               (e_eq : option_map projAD a_opt' = Some (bindex idx)),
          Dep_Option_elim_P C b_opt ->
          C (nth_Bounded' projAD As a_opt' e_eq)
            (ith_Bounded' projAD As e_eq b_opt)
          -> Type
      with
        | Some a =>
          fun b_opt e_eq c_opt c_opt' => c_opt = c_opt'
        | None => fun b_opt e_eq c_opt c_opt' => True
      end b_opt e_eq c_opt c_opt'.

    Lemma ilist_invert' {B} (As : list A) (il : ilist B As) :
      match As as As' return ilist B As' -> Type with
        | a :: As' => fun il => { b : _ & {il' : _ & il = icons a b il'}}
        | nil => fun il => il = inil _
      end il.
    Proof.
      destruct il; eauto.
    Qed.

    Lemma i2th_error_eq
          {B : A -> Type}
          {C : forall a, B a -> Type}
    : forall (As : list A)
             (idx : BoundedIndex (map projAD As))
             (Bs : ilist B As)
             (Cs : i2list C Bs),
        i2th_error_eq_P As idx
        (ith_error Bs (ibound idx))
        (i2th_error' Cs (ibound idx))
        (nth_error_map _ _ _ (boundi idx))
        (i2th_Bounded Cs idx).
    Proof.
      unfold i2th_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert As idx In_n.
      induction n; destruct Cs; simpl; eauto.
      intros; generalize (IHn As idx In_n (ilist_tl Bs) Cs); intro H';
      unfold i2th_Bounded, ith_Bounded_rect; simpl; eauto.
    Qed.

    Definition i2th_error_eq'
               {B : A -> Type}
               {C : forall a, B a -> Type}
    : forall (As : list A)
             (idx : BoundedIndex (map projAD As))
             (Bs : ilist B As)
             (c : C (nth_Bounded _ As idx) (ith_Bounded _ Bs idx)),
        i2th_error_eq_P As idx (ith_error Bs (ibound idx))
                        (Some_Dep_Option_elim_P Bs idx c)
                        (nth_error_map projAD (ibound idx) As (boundi idx)) c.
    Proof.
      unfold i2th_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert As idx In_n.
      induction n; destruct Bs; simpl; eauto.
      generalize (IHn As idx In_n Bs);
      unfold i2th_Bounded, ith_Bounded_rect; simpl; eauto.
    Qed.

    Program Definition i2th_Bounded_ind
            {B : A -> Type}
            {C C' : forall a, B a -> Type}
            (P : forall As (Bs : ilist B As) (Cs : i2list C Bs),
                   BoundedIndex (map projAD As)
                   -> forall (a : A) (b : B a), C a b -> C' a b -> Prop)
    : forall (As : list A)
           (idx : BoundedIndex (map projAD As))
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (c : C' (nth_Bounded _ As idx) (ith_Bounded _ Bs idx)),
        Dep_Option_elim2_P2 (P As Bs Cs idx)
                          (ith_error Bs (ibound idx))
                          (i2th_error' Cs (ibound idx))
                          (Some_Dep_Option_elim_P Bs idx c)
        -> P As Bs Cs idx _ (ith_Bounded _ Bs idx) (i2th_Bounded Cs idx) c
      := fun As idx Bs Cs c H =>
         match (nth_error As (ibound idx)) as e
               return
               forall (b_opt : Dep_Option B e) (c_opt : Dep_Option_elim_P C b_opt)
                       (c'_opt : Dep_Option_elim_P C' b_opt)
                       (e_eq : option_map projAD e = Some (bindex idx))
                       (d : C (nth_Bounded' projAD As e e_eq)
                              (ith_Bounded' projAD As e_eq b_opt))
                       (d' : C' (nth_Bounded' projAD As e e_eq)
                                (ith_Bounded' projAD As e_eq b_opt)),
                 i2th_error_eq_P As idx b_opt c_opt e_eq d ->
                 i2th_error_eq_P As idx b_opt c'_opt e_eq d' ->
                 Dep_Option_elim2_P2 (P As Bs Cs idx) b_opt c_opt c'_opt ->
                  P As Bs Cs idx (nth_Bounded' projAD _ e e_eq)
                    (ith_Bounded' projAD _ e_eq _) d d'
         with
           | Some a => fun b_opt c_opt c'_opt e_eq d d' c_eq c_eq' => _
           | None => fun b_opt c_opt c'_opt e_eq d d' => None_neq_Some _ e_eq
         end (ith_error Bs (ibound idx))
             (i2th_error' Cs (ibound idx))
             (Some_Dep_Option_elim_P _ _ c)
             (nth_error_map projAD (ibound idx) As (boundi idx))
             _ _ (i2th_error_eq _ _) (i2th_error_eq' _ _ _) H.

    Program Definition i2th_Bounded_ind2
            {B : A -> Type}
            {C C' : forall a, B a -> Type}
            (P : forall As (Bs : ilist B As) (Cs : i2list C Bs),
                   BoundedIndex (map projAD As)
                   -> forall (a : A) (b : B a), C a b -> C' a b -> Prop)
  : forall (As : list A)
           (idx : BoundedIndex (map projAD As))
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (Cs' : i2list C' Bs),
      Dep_Option_elim2_P2 (P As Bs Cs idx)
                          (ith_error Bs (ibound idx))
                          (i2th_error' Cs (ibound idx))
                          (i2th_error' Cs' (ibound idx))
      -> P As Bs Cs idx _ (ith_Bounded _ Bs idx)
           (i2th_Bounded Cs idx)
           (i2th_Bounded Cs' idx)
      := fun As idx Bs Cs Cs' H =>
         match (nth_error As (ibound idx)) as e
               return
               forall (b_opt : Dep_Option B e) (c_opt : Dep_Option_elim_P C b_opt)
                       (c'_opt : Dep_Option_elim_P C' b_opt)
                       (e_eq : option_map projAD e = Some (bindex idx))
                       (d : C (nth_Bounded' projAD As e e_eq)
                              (ith_Bounded' projAD As e_eq b_opt))
                       (d' : C' (nth_Bounded' projAD As e e_eq)
                                (ith_Bounded' projAD As e_eq b_opt)),
                 i2th_error_eq_P As idx b_opt c_opt e_eq d ->
                 i2th_error_eq_P As idx b_opt c'_opt e_eq d' ->
                 Dep_Option_elim2_P2 (P As Bs Cs idx) b_opt c_opt c'_opt ->
                  P As Bs Cs idx (nth_Bounded' projAD _ e e_eq)
                    (ith_Bounded' projAD _ e_eq _) d d'
         with
           | Some a => fun b_opt c_opt c'_opt e_eq d d' c_eq c_eq' => _
           | None => fun b_opt c_opt c'_opt e_eq d d' => None_neq_Some _ e_eq
         end (ith_error Bs (ibound idx))
             (i2th_error' Cs (ibound idx))
             (i2th_error' Cs' (ibound idx))
             (nth_error_map projAD (ibound idx) As (boundi idx))
             _ _ (i2th_error_eq _ _) (i2th_error_eq _ _) H.

    Definition Dep_Option_elim2_T2
             {B : A -> Type}
             {C C' : forall a, B a -> Type}
             (P : forall a b, C a b -> C' a b -> Type)
             (a_opt : option A)
    := match a_opt return
             forall (b : Dep_Option B a_opt),
               Dep_Option_elim_P C (a_opt := a_opt) b
               -> Dep_Option_elim_P C' (a_opt := a_opt) b -> Type with
         | Some a => fun b => P a (Dep_Option_elim b)
         | None => fun _ _ _ => True
       end .

    Program Definition i2th_Bounded_rect
            {B : A -> Type}
            {C C' : forall a, B a -> Type}
            (P : forall As (Bs : ilist B As) (Cs : i2list C Bs),
                   BoundedIndex (map projAD As)
                   -> forall (a : A) (b : B a), C a b -> C' a b -> Type)
    : forall (As : list A)
           (idx : BoundedIndex (map projAD As))
           (Bs : ilist B As)
           (Cs : i2list C Bs)
           (c : C' (nth_Bounded _ As idx) (ith_Bounded _ Bs idx)),
        Dep_Option_elim2_T2 (P As Bs Cs idx)
                          (ith_error Bs (ibound idx))
                          (i2th_error' Cs (ibound idx))
                          (Some_Dep_Option_elim_P Bs idx c)
        -> P As Bs Cs idx _ (ith_Bounded _ Bs idx) (i2th_Bounded Cs idx) c
      := fun As idx Bs Cs c H =>
         match (nth_error As (ibound idx)) as e
               return
               forall (b_opt : Dep_Option B e) (c_opt : Dep_Option_elim_P C b_opt)
                       (c'_opt : Dep_Option_elim_P C' b_opt)
                       (e_eq : option_map projAD e = Some (bindex idx))
                       (d : C (nth_Bounded' projAD As e e_eq)
                              (ith_Bounded' projAD As e_eq b_opt))
                       (d' : C' (nth_Bounded' projAD As e e_eq)
                                (ith_Bounded' projAD As e_eq b_opt)),
                 i2th_error_eq_P As idx b_opt c_opt e_eq d ->
                 i2th_error_eq_P As idx b_opt c'_opt e_eq d' ->
                 Dep_Option_elim2_T2 (P As Bs Cs idx) b_opt c_opt c'_opt ->
                  P As Bs Cs idx (nth_Bounded' projAD _ e e_eq)
                    (ith_Bounded' projAD _ e_eq _) d d'
         with
           | Some a => fun b_opt c_opt c'_opt e_eq d d' c_eq c_eq' => _
           | None => fun b_opt c_opt c'_opt e_eq d d' => None_neq_Some _ e_eq
         end (ith_error Bs (ibound idx))
             (i2th_error' Cs (ibound idx))
             (Some_Dep_Option_elim_P _ _ c)
             (nth_error_map projAD (ibound idx) As (boundi idx))
             _ _ (i2th_error_eq _ _) (i2th_error_eq' _ _ _) H.

  Variable D_eq_dec : forall d d' : D, {d = d'} + {d <> d'}.

  Lemma i2th_replace_BoundIndex_neq
        {B : A -> Type}
        {C : forall a, B a -> Type}
  : forall
      {As}
      (Bs : ilist B As)
      (Cs : i2list C Bs)
      (idx idx' : BoundedIndex (map projAD As))
      (new_c : C _ (ith_Bounded projAD Bs idx')),
      idx <> idx'
      -> i2th_Bounded (replace_BoundedIndex2 Cs idx' new_c) idx =
         i2th_Bounded Cs idx.
  Proof.
    intros.
    eapply (i2th_Bounded_ind2
              (fun As Bs Cs idx a b c c' => c = c')).
    unfold replace_BoundedIndex2.
    rewrite i2th_replace_Index'_neq; eauto using idx_ibound_eq, Dep_Option_elim2_P2_refl.
  Qed.

  Lemma i2th_replace_BoundIndex_eq
        {B : A -> Type}
        {C : forall a, B a -> Type}
  : forall
      {As}
      (Bs : ilist B As)
      (Cs : i2list C Bs)
      (idx : BoundedIndex (map projAD As))
      (new_c : C _ (ith_Bounded projAD Bs idx)),
      i2th_Bounded (replace_BoundedIndex2 Cs idx new_c) idx =
      new_c.
  Proof.
    intros.
    eapply (i2th_Bounded_ind
              (fun As Bs Cs idx a b c c' => c = c')).
    unfold replace_BoundedIndex2.
    rewrite i2th_replace_Index'_eq; eauto using idx_ibound_eq, Dep_Option_elim2_P2_refl.
  Qed.

End i2thIndexBound.

Section ith2IndexBound.

  Require Import Fiat.Common.ilist2.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type} {C : Set}.
  Variable (projAC : A -> C).

  (* Given a [BoundedIndex] for a list [Bound], we can always return
     an element of a list indexed by [Bound]. *)

  Definition ith2_Bounded'
          {B : A -> Type}
          (As : list A)
          (d : C)
          (a_opt : option A)
  : forall (nth_n : option_map projAC a_opt = Some d),
      Dep_Option B a_opt
      -> B (nth_Bounded' projAC As a_opt nth_n) :=
    match a_opt as a'
          return
          forall (f : option_map projAC a' = Some d),
            Dep_Option B a' ->
            B (nth_Bounded' projAC As _ f) with
      | Some a => fun nth_n b => Dep_Option_elim b
      | None => fun nth_n b => None_neq_Some _ nth_n
    end.

  Definition ith2_Bounded
          {B : A -> Type}
          {Bound}
          (il : ilist2 B Bound)
          (idx : BoundedIndex (map projAC Bound))
  : B (nth_Bounded projAC Bound idx) :=
    ith2_Bounded' Bound (nth_error_map _ _ _ (boundi idx))
                 (ith2_error il (ibound idx)).

  (*match (nth_error Bound (ibound idx)) as a'
                  return
                  Dep_Option B a' ->
                  forall (f : option_map _ a' = Some (bindex idx)),
                    B (nth_Bounded' Bound _ f) with
        | Some a => fun b _ => Dep_Option_elim b
        | None => fun _ f => None_neq_Some _ f
    end (ith2_error il (ibound idx)) (nth_error_map _ _ (boundi idx)). *)

  (* To build a reasoning principle for ith2_Bounded, we need to
     show that option types are shuffled around by [Dep_Option_elim] *)
    Definition ith2_error_eq_P
               {B : A -> Type}
               (Bound : list A)
               (idx : BoundedIndex (map projAC Bound))
               e' b c d :=
      match e' as e'
        return
        (Dep_Option B e' ->
         forall c : option_map _ e' = Some (bindex idx),
           B (nth_Bounded' projAC Bound _ c) -> Type)
      with
        | Some e =>
          fun b c d => Dep_Option_elim b = d
        | None => fun b c d => True
      end b c d.

    Lemma ith2_error_eq
          {B : A -> Type}
    : forall (Bound : list A)
             (idx : BoundedIndex (map projAC Bound))
              (il : ilist2 B Bound),
        ith2_error_eq_P Bound idx
        (ith2_error il (ibound idx))
        (nth_error_map _ _ _ (boundi idx))
        (ith2_Bounded il idx).
    Proof.
      unfold ith2_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert n In_n; induction Bound; destruct n;
      simpl; eauto; intros.
      eapply IHBound.
    Defined.

    (* [ith2_Bounded_rect] builds a function whose type depends
     on [ith2_Bounded] by reducing to a case with [ith2_error],
     which is easier to work/reason with. *)

    Definition ith2_Bounded_rect
            {B : A -> Type}
        (P : forall As, BoundedIndex (map projAC As)
                        -> ilist2 B As -> forall a : A, B a -> Type)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound),
      Dep_Option_elim_P (P Bound idx il) (ith2_error il (ibound idx))
      -> P Bound idx il _ (ith2_Bounded il idx) :=
      fun Bound idx il =>
                match (nth_error Bound (ibound idx)) as e
                      return
                      forall (b : Dep_Option B e)
                             (c : option_map _ e = Some (bindex idx))
                             d,
                        (ith2_error_eq_P Bound idx b c d)
                        -> Dep_Option_elim_P (P Bound idx il) b ->
                        P _ _ _ (@nth_Bounded' _ _ projAC _ _ e c) d with
                  | Some a => fun b e_eq d c_eq =>
                                match c_eq with
                                  | eq_refl => fun b_opt => b_opt
                                end
                  | None => fun _ e_eq _ _ _ => None_neq_Some _ e_eq
                end (ith2_error il (ibound idx))
                    _
                    (ith2_Bounded il idx)
                    (ith2_error_eq idx il).

    Definition ith2_Bounded_rect2
               {B B' : A -> Type}
        (P : forall As, BoundedIndex (map projAC As)
                        -> ilist2 B As
                        -> ilist2 B' As
                        -> forall a : A, B a -> B' a -> Type)
        (Bound : list A)
        (idx : BoundedIndex (map projAC Bound))
        (il : ilist2 B Bound)
        (il' : ilist2 B' Bound)
    : Dep_Option_elim_T2 (P Bound idx il il')
                         (ith2_error il (ibound idx))
                         (ith2_error il' (ibound idx))
      -> P Bound idx il il' _
           (ith2_Bounded il idx)
           (ith2_Bounded il' idx) :=
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d',
                   (ith2_error_eq_P Bound idx b c d)
                   -> (ith2_error_eq_P Bound idx b' c d')
                   -> Dep_Option_elim_T2 (P Bound idx il il') b b' ->
                   P _ _ _ _ (@nth_Bounded' _ _ projAC _ _ _ c) d d' with
        | Some a => fun b b' e_eq d d' d_eq d'_eq =>
                      match d_eq, d'_eq with
                        | eq_refl, eq_refl => fun b_opt => b_opt
                      end
        | None => fun b b' e_eq d d' d_eq d'_eq => None_neq_Some _ e_eq
           end (ith2_error il (ibound idx))
               (ith2_error il' (ibound idx) )
               _
               (ith2_Bounded il idx)
               (ith2_Bounded il' idx)
               (ith2_error_eq idx il)
               (ith2_error_eq idx il').

    (* [ith2_Bounded_ind] builds a proof whose type depends
     on both [nth_Bounded] and an occurence of [ith2_Bounded] by reducing
     it to a case with an [ith2_error], which is easier to reason with. *)

    Program Definition ith2_Bounded_ind
            {B B' : A -> Type}
            (P : forall As, BoundedIndex (map projAC As)
                        -> ilist2 B As
                        -> forall a : A, B a -> B' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound)
           (b : B' (nth_Bounded projAC Bound idx)),
      Dep_Option_elim_P2 (P Bound idx il) (ith2_error il (ibound idx))
                      (Some_Dep_Option projAC Bound idx b)
      -> P Bound idx il _ (ith2_Bounded il idx) b :=
      fun Bound idx il b =>
        match (nth_error Bound (ibound idx)) as e
              return
              forall (b : Dep_Option B e)
                     (b' : Dep_Option B' e)
                     (c : option_map _ e = Some (bindex idx))
                     d d',
                (ith2_error_eq_P Bound idx b c d)
                -> (ith2_error_eq_P Bound idx b' c d')
                -> Dep_Option_elim_P2 (P Bound idx il) b b' ->
                P _ _ _ (@nth_Bounded' _ _ projAC _ _ _ c) d d' with
          | Some a => _
          | None => _
        end (ith2_error il (ibound idx))
            (Some_Dep_Option projAC Bound idx b)
            _
            (ith2_Bounded il idx)
            b
            (ith2_error_eq idx il)
            _.
    Next Obligation.
      unfold ith2_error_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert n In_n b; clear.
      induction Bound; destruct n; simpl; intros; eauto.
      unfold Some_Dep_Option; simpl.
      intros; eapply IHBound.
    Qed.

    (* [ith2_Bounded_ind2] builds a proof whose type depends
     on *two* occurences of [ith2_Bounded] by reducing  it to a case
     with two [ith2_error]s, which is easier to reason with. *)

    Program Definition ith2_Bounded_ind2
            {B B' : A -> Type}
            (P : forall As, BoundedIndex (map projAC As)
                        -> ilist2 B As
                        -> forall a : A, B a -> B' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound)
           (il' : ilist2 B' Bound),
      Dep_Option_elim_P2 (P Bound idx il)
                      (ith2_error il (ibound idx))
                      (ith2_error il' (ibound idx) )
      -> P Bound idx il _ (ith2_Bounded il idx) (ith2_Bounded il' idx) :=
    fun Bound idx il il' =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d',
                   (ith2_error_eq_P Bound idx b c d)
                   -> (ith2_error_eq_P Bound idx b' c d')
                   -> Dep_Option_elim_P2 (P Bound idx il) b b' ->
                   P _ _ _ (@nth_Bounded' _ _ projAC _ _ _ c) d d' with
          | Some a => _
          | None => _
           end (ith2_error il (ibound idx))
               (ith2_error il' (ibound idx) )
               _
               (ith2_Bounded il idx)
               (ith2_Bounded il' idx)
               (ith2_error_eq idx il)
               (ith2_error_eq idx il').

    Program Definition ith2_Bounded_ind3
            {B B' B'' : A -> Type}
            (P : forall As,
                   BoundedIndex (map projAC As)
                   -> ilist2 B As
                   -> ilist2 B' As
                   -> ilist2 B'' As
                   -> forall a : A,
                        B a -> B' a -> B'' a -> Prop)
  : forall (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound)
           (il' : ilist2 B' Bound)
           (il'' : ilist2 B'' Bound),
      Dep_Option_elim_P3 (P Bound idx il il' il'')
                      (ith2_error il (ibound idx))
                      (ith2_error il' (ibound idx))
                      (ith2_error il'' (ibound idx))
      -> P Bound idx il il' il'' _
           (ith2_Bounded il idx)
           (ith2_Bounded il' idx)
           (ith2_Bounded il'' idx) :=
    fun Bound idx il il' il'' =>
      match (nth_error Bound (ibound idx)) as e
                 return
                 forall (b : Dep_Option B e)
                        (b' : Dep_Option B' e)
                        (b'' : Dep_Option B'' e)
                        (c : option_map _ e = Some (bindex idx))
                        d d' d'',
                   (ith2_error_eq_P Bound idx b c d)
                   -> (ith2_error_eq_P Bound idx b' c d')
                   -> (ith2_error_eq_P Bound idx b'' c d'')
                   -> Dep_Option_elim_P3 (P Bound idx il il' il'') b b' b'' ->
                   P Bound idx il il' il''
                     (@nth_Bounded' _ _ _ _ _ _ c)
                     d d' d'' with
          | Some a => _
          | _  => _
           end (ith2_error il (ibound idx))
               (ith2_error il' (ibound idx) )
               (ith2_error il'' (ibound idx) )
               _
               (ith2_Bounded il idx)
               (ith2_Bounded il' idx)
               (ith2_Bounded il'' idx)
               (ith2_error_eq idx il)
               (ith2_error_eq idx il')
               (ith2_error_eq idx il'').

  Lemma ith2_Bounded_imap
        {B B' : A -> Type}
  : forall (f : forall idx, B idx -> B' idx)
           (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound),
      f _ (ith2_Bounded il idx) =
      ith2_Bounded (imap2 B' f il) idx.
  Proof.
    intros.
    eapply ith2_Bounded_ind2 with (idx0 := idx) (il0 := il) (il' := imap2 B' f il).
    destruct idx as [idx [n nth_n] ]; simpl in *; subst.
    revert Bound nth_n il;
      induction n; destruct Bound; simpl; eauto;
    intros; icons2_invert; simpl; auto.
  Qed.

  Definition replace2_BoundedIndex
           {B : A -> Type}
           (Bound : list A)
           (il : ilist2 B Bound)
           (idx : BoundedIndex (map projAC Bound))
           (new_b : B (nth_Bounded projAC Bound idx))
  : ilist2 B Bound :=
    replace_Index2 (ibound idx) il (Dep_Option_elim (Some_Dep_Option _ _ _ new_b)).

  Variable C_eq_dec : forall c c' : C, {c = c'} + {c <> c'}.

  Lemma ith2_replace_BoundIndex_neq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist2 _ Bound)
      (idx idx' : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded projAC Bound idx')),
      idx <> idx'
      -> ith2_Bounded (replace2_BoundedIndex il idx' new_b) idx =
         ith2_Bounded il idx.
  Proof.
    intros.
    eapply ith2_Bounded_ind2 with (idx0 := idx) (il0 := replace2_BoundedIndex il idx' new_b)
                                                (il' := il).
    eapply ith2_replace_Index2_neq; eauto using idx_ibound_eq.
  Qed.

  Lemma ith2_replace_BoundIndex_eq
        {B : A -> Type}
  : forall
      (Bound : list A)
      (il : ilist2 _ Bound)
      (idx : BoundedIndex (map projAC Bound))
      (new_b : B (nth_Bounded projAC Bound idx)),
      ith2_Bounded (replace2_BoundedIndex il idx new_b) idx = new_b.
  Proof.
    intros.
    eapply ith2_Bounded_ind with (idx0 := idx)
                                  (il0 := replace2_BoundedIndex il idx new_b)
                                  (P := fun Bound idx il a il' b => il' = b).
    eapply ith2_replace_Index2_eq; eauto.
  Qed.

  Lemma ith2_replace_BoundedIndex_ind
        {B : A -> Type}
        (P : forall As (idx : BoundedIndex (map projAC As)),
               B (nth_Bounded projAC As idx)
               -> B (nth_Bounded projAC As idx) -> Prop)
  : forall (Bound : list A)
           (idx idx' : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound)
           (new_b : B (nth_Bounded projAC Bound idx')),
      (forall idx :  BoundedIndex (map projAC Bound),
         ibound idx <> ibound idx'
         -> P _ idx (ith2_Bounded il idx)
              (ith2_Bounded il idx))
      -> P _ idx' (ith2_Bounded il idx') new_b
      -> P _ idx
           (ith2_Bounded il idx)
           (ith2_Bounded (replace2_BoundedIndex il idx' new_b) idx).
  Proof.
    intros.
    destruct (BoundedIndex_eq_dec C_eq_dec idx idx'); subst.
    + rewrite ith2_replace_BoundIndex_eq; assumption.
    + rewrite ith2_replace_BoundIndex_neq;
      unfold not; eauto using idx_ibound_eq.
  Qed.

  Lemma ilist2_eq {B : A -> Type}
  : forall (Bound : list A)
           (il il' : ilist2 B Bound),
      (forall idx, ith2_Bounded il idx = ith2_Bounded il' idx) -> il = il'.
  Proof.
    induction Bound; intros.
    - rewrite (ilist2_invert il), (ilist2_invert il'); reflexivity.
    - icons2_invert; f_equal.
      generalize (H {| bindex := projAC a;
                       indexb := IndexBound_head _ _  |}).
      unfold ith2_Bounded; simpl; auto.
      apply IHBound; intros.
      generalize (H  {| bindex := bindex idx;
                       indexb := @IndexBound_tail _ _ _ _ (indexb idx) |}).
      unfold ith2_Bounded; simpl; auto.
  Qed.

  Lemma imap2_replace2_BoundedIndex
        {B B' : A -> Type}
  : forall (f : forall idx'', B idx'' -> B' idx'')
           (Bound : list A)
           (idx : BoundedIndex (map projAC Bound))
           (il : ilist2 B Bound)
           b,
      imap2 B' f (replace2_BoundedIndex il idx b) =
      replace2_BoundedIndex (imap2 B' f il) idx (f _ b).
  Proof.
    intros; apply ilist2_eq; intros.
    destruct (BoundedIndex_eq_dec C_eq_dec idx idx0); subst;
    rewrite <- ith2_Bounded_imap.
    - repeat rewrite ith2_replace_BoundIndex_eq; reflexivity.
    - repeat rewrite ith2_replace_BoundIndex_neq; auto.
      rewrite <- ith2_Bounded_imap; auto.
  Qed.

End ith2IndexBound.

Section i2th2IndexBound.

  Require Import Fiat.Common.i2list2.

  (* Given a bounded index [BoundedIndex Bound], we can wrap
     various lookup functions over lists indexed over [Bound].
   *)

  Context {A : Type} {D : Set}.
  Variable (projAD : A -> D).

  (* Given a [BoundedIndex] for a list [Bound], we can always return
     an element of a list indexed by [Bound]. *)

  Definition i2th2_Bounded
          {B B' : A -> Type}
          {C : forall a, B a -> B' a -> Type}
          {As}
          (Bs : ilist B As)
          (Bs' : ilist B' As)
          (Cs : i2list2 C Bs Bs')
          (idx : BoundedIndex (map projAD As))
  : C (nth_Bounded _ As idx)
      (ith_Bounded projAD Bs idx)
      (ith_Bounded projAD Bs' idx) :=
    ith_Bounded_rect2 projAD (fun _ _ _ _ => C) idx Bs Bs'
                       (i2th_error2' Cs (ibound idx)).

  (*Definition Some_Dep_Option_elim_P2
             {B : A -> Type}
             {C : forall a, B a -> Type}
             (As : list A)
             (Bs : ilist2 B As)
             (idx : BoundedIndex (map projAD As))
             (c_opt : C (nth_Bounded projAD As idx) (ith2_Bounded projAD Bs idx))
  : Dep_Option_elim_P C (ith2_error Bs (ibound idx)) :=
    match (nth_error As (ibound idx)) as e return
          forall nth_n
                 (b : B (@nth_Bounded' _ _ _ _ _ e nth_n))
                 b_opt,
            ith_error_eq_P projAD As idx
                           b_opt
                           nth_n
                           b
            -> C _ b
            -> Dep_Option_elim_P C (a_opt := e) b_opt with
      | Some a => fun nth_n b b_opt b_eq c =>
                    match b_eq in _ = b'
                          return C _ b' -> _ with
                      | eq_refl => fun c => c
                    end c
      | None => fun nth_n b b_opt b_eq c => I
    end (nth_error_map _ _ _ (boundi idx))
        _ _ (ith2_error_eq _ _ _) c_opt.

  Definition replace2_BoundedIndex2
           {B : A -> Type}
           {C : forall a, B a -> Type}
           {As}
           (Bs : ilist2 B As)
           (Cs : i2list2 C Bs)
           (idx : BoundedIndex (map projAD As))
           (new_c : C _ (ith2_Bounded projAD Bs idx))
  : i2list2 C Bs :=
    replace_2Index2' (ibound idx) Cs
                   (Some_Dep_Option_elim_P2 Bs idx new_c).

  Definition Dep_Option_2elim2_P2
             {B : A -> Type}
             {C C' : forall a, B a -> Type}
             (P : forall a b, C a b -> C' a b -> Prop)
             (a_opt : option A)
    := match a_opt return
             forall (b : Dep_Option B a_opt),
               Dep_Option_elim_P C (a_opt := a_opt) b
               -> Dep_Option_elim_P C' (a_opt := a_opt) b -> Prop with
         | Some a => fun b => P a (Dep_Option_elim b)
         | None => fun _ _ _ => True
       end .

  Lemma Dep_Option_2elim2_P2_refl
        {B : A -> Type}
        {C C' : forall a, B a -> Type}
  : forall a_opt b_opt c_opt,
      Dep_Option_2elim2_P2 (fun (a : A) (b : B a) (c c' : C a b) => c = c')
                          (a_opt := a_opt) b_opt c_opt c_opt.
    unfold Dep_Option_2elim2_P2; destruct a_opt; eauto.
  Qed.

  Definition i2th_error2_eq_P
             {B : A -> Type}
             {C : forall a, B a -> Type}
             (As : list A)
             (idx : BoundedIndex (map projAD As))
             (a_opt : option A)
             (b_opt : Dep_Option B a_opt)
             (c_opt : Dep_Option_elim_P C b_opt)
             (e_eq : option_map projAD a_opt = Some (bindex idx))
             (c_opt' : C (nth_Bounded' projAD As a_opt e_eq)
                         (ith2_Bounded' projAD As e_eq b_opt))
  : Type :=
      match a_opt as a_opt'
        return
        forall (b_opt : Dep_Option B a_opt')
               (e_eq : option_map projAD a_opt' = Some (bindex idx)),
          Dep_Option_elim_P C b_opt ->
          C (nth_Bounded' projAD As a_opt' e_eq)
            (ith2_Bounded' projAD As e_eq b_opt)
          -> Type
      with
        | Some a =>
          fun b_opt e_eq c_opt c_opt' => c_opt = c_opt'
        | None => fun b_opt e_eq c_opt c_opt' => True
      end b_opt e_eq c_opt c_opt'.

    Lemma i2th_error2_eq
          {B : A -> Type}
          {C : forall a, B a -> Type}
    : forall (As : list A)
             (idx : BoundedIndex (map projAD As))
             (Bs : ilist2 B As)
             (Cs : i2list2 C Bs),
        i2th_error2_eq_P As idx
        (ith2_error Bs (ibound idx))
        (i2th_error2' Cs (ibound idx))
        (nth_error_map _ _ _ (boundi idx))
        (i2th2_Bounded Cs idx).
    Proof.
      unfold i2th_error2_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert As idx In_n.
      induction n; destruct Cs; simpl; eauto.
      intros; generalize (IHn As idx In_n (ilist2_tl Bs) Cs); intro H';
      unfold i2th_Bounded, ith2_Bounded_rect; simpl; eauto.
    Qed.

    Definition i2th_error2_eq'
               {B : A -> Type}
               {C : forall a, B a -> Type}
    : forall (As : list A)
             (idx : BoundedIndex (map projAD As))
             (Bs : ilist2 B As)
             (c : C (nth_Bounded _ As idx) (ith2_Bounded _ Bs idx)),
        i2th_error2_eq_P As idx (ith2_error Bs (ibound idx))
                        (Some_Dep_Option_elim_P2 Bs idx c)
                        (nth_error_map projAD (ibound idx) As (boundi idx)) c.
    Proof.
      unfold i2th_error2_eq_P; simpl.
      destruct idx as [idx [n In_n ]]; simpl in *.
      revert As idx In_n.
      induction n; destruct Bs; simpl; eauto.
      generalize (IHn As idx In_n Bs);
      unfold i2th_Bounded, ith2_Bounded_rect; simpl; eauto.
    Qed.

    Program Definition i2th_Bounded2_ind
            {B : A -> Type}
            {C C' : forall a, B a -> Type}
            (P : forall As (Bs : ilist2 B As) (Cs : i2list2 C Bs),
                   BoundedIndex (map projAD As)
                   -> forall (a : A) (b : B a), C a b -> C' a b -> Prop)
    : forall (As : list A)
           (idx : BoundedIndex (map projAD As))
           (Bs : ilist2 B As)
           (Cs : i2list2 C Bs)
           (c : C' (nth_Bounded _ As idx) (ith2_Bounded _ Bs idx)),
        Dep_Option_elim2_P2 (P As Bs Cs idx)
                          (ith2_error Bs (ibound idx))
                          (i2th_error2' Cs (ibound idx))
                          (Some_Dep_Option_elim_P2 Bs idx c)
        -> P As Bs Cs idx _ (ith2_Bounded _ Bs idx) (i2th2_Bounded Cs idx) c
      := fun As idx Bs Cs c H =>
         match (nth_error As (ibound idx)) as e
               return
               forall (b_opt : Dep_Option B e) (c_opt : Dep_Option_elim_P C b_opt)
                       (c'_opt : Dep_Option_elim_P C' b_opt)
                       (e_eq : option_map projAD e = Some (bindex idx))
                       (d : C (nth_Bounded' projAD As e e_eq)
                              (ith2_Bounded' projAD As e_eq b_opt))
                       (d' : C' (nth_Bounded' projAD As e e_eq)
                                (ith2_Bounded' projAD As e_eq b_opt)),
                 i2th_error2_eq_P As idx b_opt c_opt e_eq d ->
                 i2th_error2_eq_P As idx b_opt c'_opt e_eq d' ->
                 Dep_Option_elim2_P2 (P As Bs Cs idx) b_opt c_opt c'_opt ->
                  P As Bs Cs idx (nth_Bounded' projAD _ e e_eq)
                    (ith2_Bounded' projAD _ e_eq _) d d'
         with
           | Some a => fun b_opt c_opt c'_opt e_eq d d' c_eq c_eq' => _
           | None => fun b_opt c_opt c'_opt e_eq d d' => None_neq_Some _ e_eq
         end (ith2_error Bs (ibound idx))
             (i2th_error2' Cs (ibound idx))
             (Some_Dep_Option_elim_P2 _ _ c)
             (nth_error_map projAD (ibound idx) As (boundi idx))
             _ _ (i2th_error2_eq _ _) (i2th_error2_eq' _ _ _) H.

    Program Definition i2th_Bounded2_ind2
            {B : A -> Type}
            {C C' : forall a, B a -> Type}
            (P : forall As (Bs : ilist2 B As) (Cs : i2list2 C Bs),
                   BoundedIndex (map projAD As)
                   -> forall (a : A) (b : B a), C a b -> C' a b -> Prop)
  : forall (As : list A)
           (idx : BoundedIndex (map projAD As))
           (Bs : ilist2 B As)
           (Cs : i2list2 C Bs)
           (Cs' : i2list2 C' Bs),
      Dep_Option_elim2_P2 (P As Bs Cs idx)
                          (ith2_error Bs (ibound idx))
                          (i2th_error2' Cs (ibound idx))
                          (i2th_error2' Cs' (ibound idx))
      -> P As Bs Cs idx _ (ith2_Bounded _ Bs idx)
           (i2th2_Bounded Cs idx)
           (i2th2_Bounded Cs' idx)
      := fun As idx Bs Cs Cs' H =>
         match (nth_error As (ibound idx)) as e
               return
               forall (b_opt : Dep_Option B e) (c_opt : Dep_Option_elim_P C b_opt)
                       (c'_opt : Dep_Option_elim_P C' b_opt)
                       (e_eq : option_map projAD e = Some (bindex idx))
                       (d : C (nth_Bounded' projAD As e e_eq)
                              (ith2_Bounded' projAD As e_eq b_opt))
                       (d' : C' (nth_Bounded' projAD As e e_eq)
                                (ith2_Bounded' projAD As e_eq b_opt)),
                 i2th_error2_eq_P As idx b_opt c_opt e_eq d ->
                 i2th_error2_eq_P As idx b_opt c'_opt e_eq d' ->
                 Dep_Option_elim2_P2 (P As Bs Cs idx) b_opt c_opt c'_opt ->
                  P As Bs Cs idx (nth_Bounded' projAD _ e e_eq)
                    (ith2_Bounded' projAD _ e_eq _) d d'
         with
           | Some a => fun b_opt c_opt c'_opt e_eq d d' c_eq c_eq' => _
           | None => fun b_opt c_opt c'_opt e_eq d d' => None_neq_Some _ e_eq
         end (ith2_error Bs (ibound idx))
             (i2th_error2' Cs (ibound idx))
             (i2th_error2' Cs' (ibound idx))
             (nth_error_map projAD (ibound idx) As (boundi idx))
             _ _ (i2th_error2_eq _ _) (i2th_error2_eq _ _) H.

  Variable D_eq_dec : forall d d' : D, {d = d'} + {d <> d'}.

  Lemma i2th_replace2_BoundIndex_neq
        {B : A -> Type}
        {C : forall a, B a -> Type}
  : forall
      {As}
      (Bs : ilist2 B As)
      (Cs : i2list2 C Bs)
      (idx idx' : BoundedIndex (map projAD As))
      (new_c : C _ (ith2_Bounded projAD Bs idx')),
      idx <> idx'
      -> i2th2_Bounded (replace2_BoundedIndex2 Cs idx' new_c) idx =
         i2th2_Bounded Cs idx.
  Proof.
    intros.
    pose (i2th_Bounded2_ind2 (B := B) (C' := C)
              (fun As Bs Cs idx a b c c' => c = c')).
    unfold replace2_BoundedIndex2.
    unfold i2th2_Bounded.
    rewrite i2th_replace_2Index2'_neq; eauto using idx_ibound_eq, Dep_Option_elim2_P2_refl.
  Qed.

  Lemma i2th_replace2_BoundIndex_eq
        {B : A -> Type}
        {C : forall a, B a -> Type}
  : forall
      {As}
      (Bs : ilist2 B As)
      (Cs : i2list2 C Bs)
      (idx : BoundedIndex (map projAD As))
      (new_c : C _ (ith2_Bounded projAD Bs idx)),
      i2th2_Bounded (replace2_BoundedIndex2 Cs idx new_c) idx =
      new_c.
  Proof.
    intros.
    eapply (i2th_Bounded2_ind
              (fun As Bs Cs idx a b c c' => c = c')).
    unfold replace2_BoundedIndex2.
    rewrite i2th_replace_2Index2'_eq; eauto using idx_ibound_eq, Dep_Option_elim2_P2_refl.
  Qed. *)

End i2th2IndexBound. *)

Ltac subst_strings :=
  repeat match goal with
           | [ H : string |- _ ] => subst H
           | [ H : BoundedIndex _ |- _ ] => subst H
         end.

Ltac pose_string_ids :=
  subst_strings;
  repeat match goal with
           | |- context [String ?R ?R'] =>
             let str := fresh "StringId" in
             set (String R R') as str in *
           (*| |- context [ ``(?R) ] =>
             let idx := fresh in
             set ``(R) as fresh in * *)
         end.

Arguments BoundedString [_] _.
