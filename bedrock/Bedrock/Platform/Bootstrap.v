Require Import Coq.omega.Omega.
Require Import Bedrock.DepList Bedrock.Platform.AutoSep Bedrock.Platform.Malloc.

Set Implicit Arguments.

Lemma hlist_eta' : forall A (B : A -> Type) b (h : hlist B b),
  match b return hlist B b -> Prop with
    | nil => fun _ => True
    | a :: b => fun h => h = HCons (hlist_hd h) (hlist_tl h)
  end h.
  destruct h; auto.
Qed.

Theorem hlist_eta : forall A (B : A -> Type) a b (h : hlist B (a :: b)),
  h = HCons (hlist_hd h) (hlist_tl h).
  intros; apply (hlist_eta' h).
Qed.

Lemma smem_eta : forall ls (sm sm' : smem' ls),
  NoDup ls
  -> List.Forall (fun w => smem_get' ls w sm = smem_get' ls w sm') ls
  -> sm = sm'.
  induction sm; simpl; intuition.
  rewrite hlist_nil; auto.
  inversion H0; clear H0; subst.
  inversion H; clear H; subst.
  destruct (H.addr_dec x x); intuition idtac; subst.
  rewrite (hlist_eta sm'); f_equal.
  apply IHsm; auto.
  eapply Forall_weaken'; eauto.
  simpl; intros.
  destruct (H.addr_dec x x0); subst; tauto.
Qed.

Lemma get_emp' : forall w ls,
  smem_get' ls w (smem_emp' ls) = None.
  induction ls; simpl; intuition.
  destruct (H.addr_dec a w); auto.
Qed.

Lemma get_emp : forall w,
  smem_get w smem_emp = None.
  intros.
  apply get_emp'.
Qed.

Lemma empty_mem : forall (sm : smem),
  (forall w, smem_get w sm = None)
  -> sm = smem_emp.
  intros.
  apply smem_eta.
  apply NoDup_allWords.
  apply Forall_forall; intros.
  rewrite H.
  symmetry; apply get_emp.
Qed.

Fixpoint smem_clear ls (sm : smem' ls) (w : W) : smem' ls :=
  match sm with
    | HNil => HNil
    | HCons w' _ v sm' =>
      HCons (if H.addr_dec w w' then None else v) (smem_clear sm' w)
  end.

Fixpoint smem_put ls (sm : smem' ls) (w : W) (v : B) : smem' ls :=
  match sm with
    | HNil => HNil
    | HCons w' _ v' sm' =>
      HCons (if H.addr_dec w w' then Some v else v') (smem_put sm' w v)
  end.

Lemma disjoint_get' : forall ls sm1 sm2,
  NoDup ls
  -> List.Forall (fun w => smem_get' ls w sm1 <> None -> smem_get' ls w sm2 <> None -> False) ls
  -> disjoint' ls sm1 sm2.
  induction sm1; simpl; intuition; rewrite (hlist_eta sm2) in *; simpl in *.
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  destruct (H.addr_dec x x); try tauto.
  destruct b; auto.
  destruct (hlist_hd sm2); auto.
  intuition discriminate.
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  apply IHsm1; intros; auto.
  eapply Forall_weaken'; eauto.
  simpl; intros.
  destruct (H.addr_dec x x0); subst; tauto.
Qed.

Lemma disjoint_get : forall sm1 sm2,
  (forall w, smem_get w sm1 <> None -> smem_get w sm2 <> None -> False)
  -> disjoint sm1 sm2.
  intros; apply disjoint_get'.
  apply BedrockHeap.NoDup_all_addr.
  apply Forall_forall; intros.
  eauto.
Qed.

Lemma disjoint_get_fwd' : forall ls sm1 sm2,
  disjoint' ls sm1 sm2
  -> NoDup ls
  -> List.Forall (fun w => smem_get' ls w sm1 <> None -> smem_get' ls w sm2 <> None -> False) ls.
  induction sm1; simpl; intuition; rewrite (hlist_eta sm2) in *; simpl in *;
    subst; constructor; simpl.
  destruct (H.addr_dec x x); tauto.
  inversion H0; clear H0; subst.
  eapply Forall_weaken'; try apply IHsm1.
  eauto.
  auto.
  simpl; intros.
  destruct (H.addr_dec x x0); subst; tauto.
  destruct (H.addr_dec x x); tauto.
  inversion H0; clear H0; subst.
  eapply Forall_weaken'; try apply IHsm1.
  eauto.
  auto.
  simpl; intros.
  destruct (H.addr_dec x x0); subst; tauto.
Qed.

Lemma allWordsUpto_universal : forall width init w,
  (wordToNat w < init)%nat
  -> (init <= pow2 width)%nat
  -> In w (allWordsUpto width init).
  induction init; simpl; intuition.
  destruct (weq w $ (init)); subst; auto; right.
  assert (wordToNat w <> init).
  intro; apply n.
  subst.
  symmetry; apply natToWord_wordToNat.
  auto.
Qed.

Lemma allWords_universal : forall sz w,
  In w (allWords sz).
  rewrite allWords_eq; intros; apply allWordsUpto_universal.
  apply wordToNat_bound.
  auto.
Qed.

Lemma disjoint_get_fwd : forall sm1 sm2,
  disjoint sm1 sm2
  -> (forall w, smem_get w sm1 <> None -> smem_get w sm2 <> None -> False).
  intros; eapply disjoint_get_fwd' in H; try apply BedrockHeap.NoDup_all_addr.
  assert (In w H.all_addr) by apply allWords_universal.
  generalize (proj1 (Forall_forall _ _) H _ H2); tauto.
Qed.

Lemma get_clear_ne' : forall a a' ls (sm : smem' ls),
  a <> a'
  -> smem_get' ls a (smem_clear sm a') = smem_get' ls a sm.
  induction sm; simpl; intuition.
  destruct (H.addr_dec x a); auto.
  destruct (H.addr_dec a' x); congruence.
Qed.

Lemma get_clear_ne : forall a a' sm,
  a <> a'
  -> smem_get a (smem_clear sm a') = smem_get a sm.
  intros; apply get_clear_ne'; auto.
Qed.

Lemma get_clear_eq' : forall a ls (sm : smem' ls),
  smem_get' ls a (smem_clear sm a) = None.
  induction sm; simpl; intuition.
  destruct (H.addr_dec x a); auto.
  destruct (H.addr_dec a x); congruence.
Qed.

Lemma get_clear_eq : forall a sm,
  smem_get a (smem_clear sm a) = None.
  intros; apply get_clear_eq'.
Qed.

Hint Rewrite get_clear_eq get_clear_ne
  using solve [ assumption | W_neq ] : get.

Lemma get_put_eq' : forall a v ls (sm : smem' ls),
  In a ls
  -> smem_get' ls a (smem_put sm a v) = Some v.
  induction sm; simpl; intuition.
  subst.
  destruct (H.addr_dec a a); intuition idtac.
  destruct (H.addr_dec x a); intuition idtac.
  subst.
  destruct (H.addr_dec a a); intuition idtac.
Qed.

Lemma get_put_eq : forall a v sm,
  smem_get a (smem_put sm a v) = Some v.
  intros; apply get_put_eq'.
  apply allWords_universal.
Qed.

Lemma get_put_ne' : forall a a' v ls (sm : smem' ls),
  a <> a'
  -> smem_get' ls a (smem_put sm a' v) = smem_get' ls a sm.
  induction sm; simpl; intuition.
  destruct (H.addr_dec a' x); intuition idtac.
  destruct (H.addr_dec x a); intuition idtac.
  congruence.
  destruct (H.addr_dec x a); intuition idtac.
Qed.

Lemma get_put_ne : forall a a' v sm,
  a <> a'
  -> smem_get a (smem_put sm a' v) = smem_get a sm.
  intros; apply get_put_ne'; auto.
Qed.

Hint Rewrite get_emp get_put_eq get_put_ne
  using solve [ assumption | W_neq ] : get.

Lemma join_None' : forall a ls sm1 sm2,
  smem_get' ls a sm1 = None
  -> smem_get' ls a (join' ls sm1 sm2) = smem_get' ls a sm2.
  induction sm1; simpl; intuition.
  destruct (H.addr_dec x a); subst; auto.
Qed.

Lemma join_None : forall a sm1 sm2,
  smem_get a sm1 = None
  -> smem_get a (join sm1 sm2) = smem_get a sm2.
  intros; apply join_None'; auto.
Qed.

Lemma join_Some' : forall a v ls sm1 sm2,
  smem_get' ls a sm1 = Some v
  -> smem_get' ls a (join' ls sm1 sm2) = Some v.
  induction sm1; simpl; intuition.
  destruct (H.addr_dec x a); subst; auto.
Qed.

Lemma join_Some : forall a v sm1 sm2,
  smem_get a sm1 = Some v
  -> smem_get a (join sm1 sm2) = Some v.
  intros; apply join_Some'; auto.
Qed.

Lemma split_put_clear : forall sm sm1 sm2 a v,
  split sm sm1 sm2
  -> smem_get a sm2 = Some v
  -> split sm (smem_put sm1 a v) (smem_clear sm2 a).
  unfold split; intuition subst.
  apply disjoint_get; intros.
  destruct (weq w a); subst.
  autorewrite with get in *; tauto.
  autorewrite with get in *.
  eapply disjoint_get_fwd in H1; eassumption.

  apply smem_eta; try apply BedrockHeap.NoDup_all_addr.
  apply Forall_forall; intros.
  destruct (weq x a); subst.
  rewrite join_None.
  erewrite join_Some.
  eauto.
  autorewrite with get; reflexivity.
  case_eq (smem_get a sm1); auto; intros.
  eapply disjoint_get_fwd in H1; try eassumption.
  tauto.
  instantiate (1 := a); congruence.
  congruence.

  case_eq (smem_get x sm1); intros.
  erewrite join_Some.
  erewrite join_Some.
  2: autorewrite with get; eassumption.
  2: eassumption.
  reflexivity.

  rewrite join_None.
  rewrite join_None.
  autorewrite with get; reflexivity.
  autorewrite with get; assumption.
  assumption.
Qed.

Lemma wordToNat_ninj : forall sz (u v : word sz),
  u <> v
  -> wordToNat u <> wordToNat v.
  intros; intro; apply H.
  assert (natToWord sz (wordToNat u) = natToWord sz (wordToNat v)) by congruence.
  repeat rewrite natToWord_wordToNat in H1.
  assumption.
Qed.

Lemma wordToNat_ninj' : forall sz (u v : word sz),
  wordToNat u <> wordToNat v
  -> u <> v.
  congruence.
Qed.

Theorem materialize_allocated' : forall specs stn size base sm,
  (forall w, w < base -> smem_get w sm = None)
  -> (forall n, (n < 4 * size)%nat -> smem_get (base ^+ $ (n)) sm <> None)
  -> (forall w, base ^+ $ (4 * size) <= w -> smem_get w sm = None)
  -> goodSize (wordToNat base + 4 * size)%nat
  -> interp specs ((base =?> size)%Sep stn sm).
  induction size.

  propxFo.
  apply empty_mem; intros.
  destruct (wlt_dec w base); auto.
  replace w with (base ^+ $ (wordToNat (w ^- base))); auto.
  rewrite natToWord_wordToNat.
  replace (base ^+ (w ^- base)) with w.
  apply H1.
  intros.
  replace (base ^+ $ (4 * 0)) with base in H3.
  tauto.
  simpl.
  W_eq.
  rewrite wminus_def.
  rewrite wplus_comm.
  rewrite <- wplus_assoc.
  rewrite (wplus_comm (^~ base)).
  rewrite wminus_inv.
  rewrite wplus_comm.
  rewrite wplus_unit.
  reflexivity.
  rewrite natToWord_wordToNat.
  W_eq.

  intros.
  generalize (H0 0).
  generalize (H0 1).
  generalize (H0 2).
  generalize (H0 3).
  intros.
  case_eq (smem_get (base ^+ $0) sm); intros.
  2: elimtype False; apply H6; eauto.
  case_eq (smem_get (base ^+ $1) sm); intros.
  2: elimtype False; apply H5; eauto.
  case_eq (smem_get (base ^+ $2) sm); intros.
  2: elimtype False; apply H4; eauto.
  case_eq (smem_get (base ^+ $3) sm); intros.
  2: elimtype False; apply H3; eauto.

  propxFo.

  exists (smem_put (smem_put (smem_put (smem_put smem_emp base b)
    (base ^+ $1) b0) (base ^+ $2) b1) (base ^+ $3) b2).
  exists (smem_clear (smem_clear (smem_clear (smem_clear sm base)
    (base ^+ $1)) (base ^+ $2)) (base ^+ $3)).
  split.

  repeat apply split_put_clear.
  apply split_a_semp_a.
  replace (base ^+ $0) with base in H7 by words.
  congruence.

  autorewrite with get; assumption.
  autorewrite with get; assumption.
  autorewrite with get; assumption.

  split.
  exists (implode stn (b, b0, b1, b2)).
  split.
  unfold smem_get_word.

  unfold H.footprint_w.
  autorewrite with get.
  reflexivity.

  intuition idtac.
  autorewrite with get.
  reflexivity.

  apply simplify_fwd.
  eapply Imply_sound; [ apply allocated_shift_base | ].
  instantiate (1 := 0).
  instantiate (1 := base ^+ $4).
  W_eq.
  eauto.
  apply IHsize.

  intros.
  destruct (weq w base); subst.
  autorewrite with get; reflexivity.
  destruct (weq w (base ^+ $1)); subst.
  autorewrite with get; reflexivity.
  destruct (weq w (base ^+ $2)); subst.
  autorewrite with get; reflexivity.
  destruct (weq w (base ^+ $3)); subst.
  autorewrite with get; reflexivity.
  autorewrite with get.
  apply H.
  pre_nomega.
  rewrite wordToNat_wplus in H11;
    rewrite wordToNat_natToWord_idempotent in * by reflexivity;
      try (eapply goodSize_weaken; [ eassumption | omega ]).

  repeat match goal with
           | [ H : _ |- _ ] => apply wordToNat_ninj in H
         end.
  rewrite wordToNat_wplus in n0;
    rewrite wordToNat_natToWord_idempotent in * by reflexivity;
      try (eapply goodSize_weaken; [ eassumption | omega ]).
  rewrite wordToNat_wplus in n1;
    rewrite wordToNat_natToWord_idempotent in * by reflexivity;
      try (eapply goodSize_weaken; [ eassumption | omega ]).
  rewrite wordToNat_wplus in n2;
    rewrite wordToNat_natToWord_idempotent in * by reflexivity;
      try (eapply goodSize_weaken; [ eassumption | omega ]).
  omega.

  intros.
  rewrite get_clear_ne in H12.
  rewrite get_clear_ne in H12.
  rewrite get_clear_ne in H12.
  rewrite get_clear_ne in H12.
  apply H0 with (4 + n).
  omega.
  rewrite natToW_plus.
  etransitivity; try apply H12.
  f_equal.
  unfold natToW.
  W_eq.

  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.

  apply wordToNat_ninj'.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent.
  omega.
  change (goodSize (4 + n)).
  eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + n)).
  eapply goodSize_weaken; [ eassumption | omega ].

  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  apply wordToNat_ninj'.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  omega.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + n)).
  eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + n)).
  eapply goodSize_weaken; [ eassumption | omega ].

  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  apply wordToNat_ninj'.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  omega.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + n)).
  eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + n)).
  eapply goodSize_weaken; [ eassumption | omega ].

  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  apply wordToNat_ninj'.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  omega.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + n)).
  eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + n)).
  eapply goodSize_weaken; [ eassumption | omega ].

  intros.
  rewrite get_clear_ne.
  rewrite get_clear_ne.
  rewrite get_clear_ne.
  rewrite get_clear_ne.
  apply H1.
  Opaque mult.
  pre_nomega.
  rewrite <- wplus_assoc in H11.
  rewrite <- natToW_plus in H11.
  rewrite wordToNat_wplus in H11.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent in H11.
  rewrite wordToNat_natToWord_idempotent.
  omega.
  change (goodSize (4 * S size)); eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + 4 * size)); eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent.
  assumption.
  change (goodSize (4 * S size)); eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + 4 * size)); eapply goodSize_weaken; [ eassumption | omega ].

  intro; apply H11; subst.
  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  pre_nomega.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent.
  omega.
  change (goodSize (4 + 4 * size)); eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + 4 * size)); eapply goodSize_weaken; [ eassumption | omega ].

  intro; apply H11; subst.
  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  pre_nomega.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent.
  omega.
  change (goodSize (4 + 4 * size)); eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + 4 * size)); eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  eapply goodSize_weaken; [ eassumption | omega ].

  intro; apply H11; subst.
  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  pre_nomega.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent.
  omega.
  change (goodSize (4 + 4 * size)); eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + 4 * size)); eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  eapply goodSize_weaken; [ eassumption | omega ].

  intro; apply H11; subst.
  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  pre_nomega.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent.
  omega.
  change (goodSize (4 + 4 * size)); eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent.
  eapply goodSize_weaken; [ eassumption | omega ].
  change (goodSize (4 + 4 * size)); eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  eapply goodSize_weaken; [ eassumption | omega ].

  rewrite wordToNat_wplus.
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  eapply goodSize_weaken; [ eassumption | omega ].
  rewrite wordToNat_natToWord_idempotent by reflexivity.
  eapply goodSize_weaken; [ eassumption | omega ].
Qed.

Definition goodSize' (n : nat) := (N.of_nat n < 1 + Npow2 32)%N.

Lemma get_memoryIn' : forall m w init,
  (wordToNat w < init)%nat
  -> goodSize' init
  -> smem_get' (allWordsUpto 32 init) w (memoryIn' m _) = m w.
  induction init; simpl; intuition.
  destruct (H.addr_dec $ (init) w).
  unfold H.mem_get, ReadByte.
  congruence.
  apply IHinit.
  apply wordToNat_ninj in n.
  rewrite wordToNat_natToWord_idempotent in n.
  omega.
  generalize H0; clear.
  unfold goodSize'.
  generalize (Npow2 32); intros.
  apply Nlt_out in H0.
  rewrite N2Nat.inj_add in H0.
  autorewrite with N in *.
  pre_nomega.
  simpl in *.
  omega.
  generalize H0; clear.
  unfold goodSize'.
  generalize (Npow2 32).
  intros.
  nomega.
Qed.

Lemma pow2_N : forall n,
  N.of_nat (pow2 n) = Npow2 n.
  intros.
  assert (N.to_nat (N.of_nat (pow2 n)) = N.to_nat (Npow2 n)).
  autorewrite with N.
  symmetry; apply Npow2_nat.
  assert (N.of_nat (N.to_nat (N.of_nat (pow2 n))) = N.of_nat (N.to_nat (Npow2 n))) by congruence.
  autorewrite with N in *.
  assumption.
Qed.

Lemma get_memoryIn : forall m w,
  smem_get w (memoryIn m) = m w.
  intros.
  unfold smem_get, memoryIn, HT.memoryIn, H.all_addr.
  rewrite allWords_eq.
  apply get_memoryIn'.
  apply wordToNat_bound.
  hnf.
  rewrite pow2_N.
  reflexivity.
Qed.
Require Import Coq.Arith.Arith.

Theorem materialize_allocated : forall stn st size specs,
  (forall n, (n < size * 4)%nat -> st.(Mem) n <> None)
  -> (forall w, $ (size * 4) <= w -> st.(Mem) w = None)
  -> goodSize (size * 4)%nat
  -> interp specs (![ 0 =?> size ] (stn, st)).
  rewrite sepFormula_eq; intros.
  apply materialize_allocated'; simpl.
  intros.
  pre_nomega.
  rewrite roundTrip_0 in H2.
  omega.
  intros.
  rewrite <- natToW_plus; simpl.
  rewrite get_memoryIn.
  auto.
  intros.
  rewrite wplus_unit in H2.
  rewrite get_memoryIn.
  apply H0.
  rewrite mult_comm; assumption.
  rewrite mult_comm; assumption.
Qed.


(** * Now put it all together to prove [genesis]. *)

Section boot.
  Variables heapSize globalsSize : nat.

  Hypothesis heapSizeLowerBound : (3 <= heapSize)%nat.
  Hypothesis heapSizeUpperBound : goodSize (heapSize * 4).

  Lemma goodSize_heapSize : goodSize heapSize.
    eapply goodSize_weaken; [ eassumption | omega ].
  Qed.

  Hint Immediate goodSize_heapSize.

  Theorem heapSizeLowerBound' : natToW heapSize < natToW 3 -> False.
    change (natToW 3 <= natToW heapSize).
    intro; pre_nomega.
    rewrite wordToNat_natToWord_idempotent in *.
    rewrite wordToNat_natToWord_idempotent in *.
    omega.
    reflexivity.
    change (goodSize heapSize); eapply goodSize_weaken; [ eassumption | omega ].
  Qed.

  Hint Immediate heapSizeLowerBound'.

  Theorem noWrap : noWrapAround (natToW 4) (heapSize - 1).
    simpl; hnf; intros.
    intro.
    rewrite <- natToW_plus in H0.
    apply natToW_inj in H0.
    omega.
    2: reflexivity.
    eapply goodSize_weaken; [ eassumption | omega ].
  Qed.

  Theorem heapSize_roundTrip : wordToNat (natToW heapSize) = heapSize.
    intros; apply wordToNat_natToWord_idempotent;
      change (goodSize heapSize); eauto.
  Qed.

  Hint Rewrite heapSize_roundTrip : sepFormula.

  Definition bootS := {|
    Reserved := 49;
    Formals := nil;
    Precondition := fun _ => st ~> ![ 0 =?> (heapSize + 50 + globalsSize) ] st
  |}.
  Require Import Coq.Arith.Arith.

  Lemma wiggle : forall P Q R,
    P * (Q * R) ===> Q * P * R.
    sepLemma.
  Qed.

  Theorem genesis :
    0 =?> (heapSize + 50 + globalsSize)
    ===> (Ex vs, locals ("rp" :: nil) vs 49 (heapSize * 4)%nat) * 0 =?> heapSize * ((heapSize + 50) * 4)%nat =?> globalsSize.
    descend; intros; eapply Himp_trans; [ apply allocated_split | ].
    instantiate (1 := heapSize); auto.
    apply Himp_trans with (0 =?> heapSize *
      ((heapSize * 4)%nat =?> 50 * ((heapSize + 50) * 4)%nat =?> globalsSize))%Sep.
    apply Himp_star_frame.
    apply Himp_refl.
    intros; eapply Himp_trans; [ apply allocated_split | ].
    instantiate (1 := 50); auto.
    apply Himp_star_frame.
    apply allocated_shift_base.
    rewrite mult_comm.
    simpl.
    unfold natToW.
    words.
    reflexivity.
    apply allocated_shift_base.
    simpl.
    rewrite <- mult_plus_distr_l.
    rewrite mult_comm.
    unfold natToW.
    words.
    omega.

    eapply Himp_trans; [ apply wiggle | ].
    repeat (apply Himp_star_frame; try apply Himp_refl).
    change 50 with (length ("rp" :: nil) + 49).
    apply create_stack.
    NoDup.
  Qed.

  Transparent mult.

  Lemma bootstrap_Sp_nonzero : forall sp : W,
    sp = 0
    -> sp = heapSize * 4
    -> goodSize (heapSize * 4)
    -> False.
    intros; subst; apply natToW_inj in H0; auto; omega.
  Qed.

  Hypothesis globals : nat.
  Hypothesis mem_size : goodSize ((heapSize + 50 + globals) * 4)%nat.

  Lemma bootstrap_Sp_freeable : forall sp : W,
    sp = heapSize * 4
    -> freeable sp 50.
    intros; subst; constructor; auto.
    hnf; intros.
    rewrite <- natToW_plus.
    intro.
    apply natToW_inj in H0.
    omega.
    unfold size in *.
    eapply goodSize_weaken; [ apply mem_size | ].
    omega.
    auto.
  Qed.
End boot.

Definition genesisHints : TacPackage.
  prepare genesis tt.
Defined.

Ltac genesis := post; evaluate genesisHints; simpl in *; sep genesisHints; eauto.

Require Import Bedrock.Platform.Safety.

Ltac safety ok :=
  eapply safety; try eassumption; [
    link_simp; unfold labelSys, labelSys'; simpl; tauto
    | apply ok
    | apply LabelMap.find_2; link_simp; reflexivity
    | propxFo; apply materialize_allocated; assumption ].

Hint Immediate goodSize_heapSize heapSizeLowerBound' bootstrap_Sp_nonzero bootstrap_Sp_freeable.
Hint Rewrite heapSize_roundTrip using assumption : sepFormula.
Hint Extern 1 (noWrapAround _ _) => apply noWrap.

Ltac goodSize :=
  match goal with
    | [ H : goodSize (?size * 4)%nat |- _ ] => unfold size in *
  end; eapply goodSize_weaken; [ eassumption | omega ].
