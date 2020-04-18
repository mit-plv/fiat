Require Import Fiat.QueryStructure.Implementation.DataStructures.Bags.CachingBags.

Unset Implicit Arguments.
(* This also needs to be adapted with update and delete.
Section Generalities.
  Require Import Morphisms.

  Lemma comm_cacheable_aux :
    forall {TValue TCachedValue}
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (f: TValue -> TCachedValue -> TCachedValue),
      Equivalence eqA ->
      Proper (eq ==> eqA ==> eqA) f ->
      Proper (eqA ==> eq ==> eqA) (RecomputeCachedValue f).
  Proof.
    intros;
    unfold RecomputeCachedValue, Morphisms.Proper, Morphisms.respectful;
    intros ** seq seq';
    subst;
    induction seq;
      simpl;
      trivial;
      try rewrite IHseq;
      reflexivity.
  Qed.

  Lemma comm_cacheable :
    forall {TValue TCachedValue}
           (eqA: TCachedValue -> TCachedValue -> Prop)
           (f: TValue -> TCachedValue -> TCachedValue),
      (Equivalence eqA) ->
      (Proper (eq ==> eqA ==> eqA) f) ->
      (forall x y default, eqA (f x (f y default)) (f y (f x default))) ->
      (IsCacheable eqA f).
  Proof.
    unfold IsCacheable;
    intros * equiv proper comm;
    unfold Morphisms.Proper, Morphisms.respectful;
    intros * is_eqA * perm;
      induction perm as [ | | x1 x2 l | ];
      simpl.

    trivial.
    rewrite IHperm; reflexivity.
    rewrite comm; rewrite comm_cacheable_aux; eauto; reflexivity.
    etransitivity; try apply IHperm1; rewrite comm_cacheable_aux; eauto; symmetry; assumption.
  Qed.
End Generalities.

Section Aggregates.
  Require Import RelationClasses.
  Require Import ArithRing NArith ZArith QArith Qminmax.

  Ltac all_rewrites :=
    repeat progress match goal with
      | [ H: ?f ?a ?b |- _ ] => setoid_rewrite H; clear H
    end.

  Ltac t :=
    intros;
    apply comm_cacheable; intros; simpl;
    [ try solve [ first [ apply eq_equivalence | intuition ] ] |
      try solve [ unfold Proper, respectful; intros; all_rewrites; intuition ] | ].

  Section Counts.
    Definition count A (_: A) acc := S acc.

    Lemma count_cacheable :
      forall A,
        IsCacheable eq (count A).
    Proof.
      t; reflexivity.
    Qed.
  End Counts.

  Section Sums.
    Lemma plus_cacheable :
      IsCacheable eq plus.
    Proof.
      t; ring.
    Qed.

    Lemma Nadd_cacheable :
      IsCacheable eq N.add.
    Proof.
      t; ring.
    Qed.

    Lemma Zadd_cacheable :
      IsCacheable eq Z.add.
    Proof.
      t; ring.
    Qed.

    Lemma Qplus_cacheable :
      IsCacheable Qeq Qplus.
    Proof.
      t; ring.
    Qed.

    Definition squared {T} (add: T -> T -> T) (mul: T -> T -> T) :=
      fun x acc => add (mul x x) acc.

    Lemma plus_sq_cacheable :
      IsCacheable eq (squared plus mult).
    Proof.
      t. unfold squared; ring.
    Qed.

    Lemma Nadd_sq_cacheable :
      IsCacheable eq (squared N.add N.mul).
    Proof.
      t; unfold squared; ring.
    Qed.

    Lemma Zadd_sq_cacheable :
      IsCacheable eq (squared Z.add Z.mul).
    Proof.
      t; unfold squared; ring.
    Qed.

    Lemma Qplus_eq_cacheable :
      IsCacheable Qeq (squared Qplus Qmult).
    Proof.
      t; unfold squared; try ring.
      unfold Proper, respectful.
      intros.
      subst.
      setoid_rewrite H0.
      reflexivity.
    Qed.
  End Sums.

  Section Extrema.
    Ltac prove_extremum assoc comm :=
      solve [t; repeat rewrite assoc;
             f_equiv; eauto using comm].

    Lemma max_cacheable :
      IsCacheable eq max.
    Proof.
      prove_extremum Max.max_assoc Max.max_comm.
    Qed.

    Lemma min_cacheable :
      IsCacheable eq min.
    Proof.
      prove_extremum Min.min_assoc Min.min_comm.
    Qed.

    Lemma Nmax_cacheable :
      IsCacheable eq N.max.
    Proof.
      prove_extremum N.max_assoc N.max_comm.
    Qed.

    Lemma Nmin_cacheable :
      IsCacheable eq N.min.
    Proof.
      prove_extremum N.min_assoc N.min_comm.
    Qed.

    Lemma Zmax_cacheable :
      IsCacheable eq Z.max.
    Proof.
      prove_extremum Z.max_assoc Z.max_comm.
    Qed.

    Lemma Zmin_cacheable :
      IsCacheable eq Z.min.
    Proof.
      prove_extremum Z.min_assoc Z.min_comm.
    Qed.

    Lemma Qmax_cacheable :
      IsCacheable Qeq Qmax.
    Proof.
      prove_extremum Q.max_assoc Q.max_comm.
    Qed.

    Lemma Qmin_cacheable :
      IsCacheable Qeq Qmin.
    Proof.
      prove_extremum Q.min_assoc Q.min_comm.
    Qed.
  End Extrema.

  Section Statistics.
    Require Import Rbase R_sqrt.

    Definition Zsq z := Z.mul z z.
    Definition Rsq r := Rmult r r.

    Record VarianceStore :=
      { stored_sum: Z; stored_sum_sq: Z; stored_count: nat }.

    Definition UpdateVarianceStore x store :=
      {| stored_sum    := Z.add (stored_sum    store) (x);
         stored_sum_sq := Z.add (stored_sum_sq store) (Zsq x);
         stored_count  := plus  (stored_count  store) (1) |}.

    Definition avg sum n := Rdiv (IZR sum) (INR n).

    Definition GetAvg projection variance_store :=
      match stored_count variance_store with
        | 0%nat => 0%R
        | n     => avg (projection variance_store) n
      end.

    Definition GetSampleAvg projection variance_store :=
      match stored_count variance_store with
        | 0%nat => 0%R
        | 1%nat => 0%R
        | S n   => avg (projection variance_store) n
      end.

    Definition GetAverage        := GetAvg stored_sum.
    Definition GetAverageSq      := GetAvg stored_sum_sq.
    Definition GetVariance store := Rminus (GetAverageSq store)
                                           (Rsq (GetAverage store)).
    Definition GetStdDev   store := sqrt   (GetVariance store).

    Definition GetSampleAverage        := GetSampleAvg stored_sum.
    Definition GetSampleAverageSq      := GetSampleAvg stored_sum_sq.
    Definition GetSampleVariance store := Rminus (GetSampleAverageSq store)
                                                 (Rsq (GetSampleAverage store)).
    Definition GetSampleStdDev   store := sqrt   (GetSampleVariance store).

    Lemma variance_store_cacheable :
      IsCacheable eq UpdateVarianceStore.
    Proof.
      t; unfold UpdateVarianceStore; simpl; f_equal; ring.
    Qed.
  End Statistics.

  (* Missing:
     BIT_AND()		Return bitwise and
     BIT_OR()		Return bitwise or
     BIT_XOR()		Return bitwise xor
     COUNT(DISTINCT)	Return the count of a number of different values
     GROUP_CONCAT()	Return a concatenated string *)
End Aggregates.

*)
