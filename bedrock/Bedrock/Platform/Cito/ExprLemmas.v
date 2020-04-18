Require Import Bedrock.Platform.AutoSep Coq.omega.Omega.

Lemma S_le_lt : forall a b c, (a + S b <= c -> a < c)%nat.
  intros; omega.
Qed.
Lemma lt_goodSize'' : forall a b, (a < b)%nat -> goodSize b -> natToW a < natToW b.
  intros; apply lt_goodSize; auto; eapply goodSize_weaken; eauto.
Qed.
Lemma max_le_1 : forall b d1 d2 n, (b + S (max d1 d2) <= n -> b + d1 <= n)%nat.
  intros.
  eapply (Le.le_trans _ _ _ _ H).
  Grab Existential Variables.
  eapply Plus.plus_le_compat_l.
  eapply le_S.
  eapply Max.le_max_l.
Qed.
Lemma max_le_2 : forall b d1 d2 n, (b + S (max d1 d2) <= n -> S b + d2 <= n)%nat.
  intros.
  simpl.
  eapply (Le.le_trans _ _ _ _ H).
  Grab Existential Variables.
  eapply Lt.lt_le_S.
  eapply Plus.plus_lt_compat_l.
  eapply Lt.le_lt_n_Sm.
  eapply Max.le_max_r.
Qed.
Lemma selN_updN : forall ls n v, (n < length ls)%nat -> selN (updN ls n v) n = v.
  induction ls; induction n; simpl; intuition.
Qed.
Lemma sel_upd : forall n ls v, (n < length ls)%nat -> goodSize (length ls) -> Array.sel (Array.upd ls (natToW n) v) (natToW n) = v.
  intros; rewrite sel_selN; try (eapply goodSize_weaken; eauto).
  rewrite upd_updN; try (eapply goodSize_weaken; eauto).
  apply selN_updN; auto.
Qed.
Lemma sel_firstn' : forall ls1 ls2 n, (n < length ls1 -> length ls1 = length ls2 -> firstn (S n) ls1 = firstn (S n) ls2 -> selN ls1 n = selN ls2 n)%nat.
  induction ls1; induction ls2; induction n; simpl; intuition.
  apply IHls1; simpl in *; intuition.
Qed.
Lemma sel_firstn : forall ls1 ls2 n, (n < length ls1 -> length ls1 = length ls2 -> firstn (S n) ls1 = firstn (S n) ls2 -> goodSize (length ls1) -> Array.sel ls1 (natToW n) = Array.sel ls2 (natToW n))%nat.
  intros; repeat rewrite sel_selN; try (eapply goodSize_weaken; eauto).
  eapply sel_firstn'; eauto.
Qed.
Lemma sel_upd_firstn : forall n ls1 ls2 v, (n < length ls1)%nat -> length ls1 = length ls2 -> goodSize (length ls1) -> firstn (S n) ls1 = firstn (S n) (Array.upd ls2 (natToW n) v) -> Array.sel ls1 (natToW n) = v.
  intros.
  erewrite sel_firstn.
  Focus 4.
  eauto.
  apply sel_upd.
  congruence.
  congruence.
  omega.
  rewrite upd_length.
  omega.
  auto.
Qed.
Lemma firstn_S : forall A n (ls1 ls2 : list A), (n < length ls1)%nat -> length ls1 = length ls2 -> firstn (S n) ls1 = firstn (S n) ls2 -> firstn n ls1 = firstn n ls2.
  intros.
  rewrite <- removelast_firstn; try congruence.
  rewrite H1.
  apply removelast_firstn; congruence.
Qed.
Lemma upd_firstn : forall ls n v, firstn n (updN ls n v) = firstn n ls.
  induction ls; induction n; simpl; intuition.
Qed.
Hint Immediate upd_firstn.
Lemma firstn_S_upd : forall n ls1 ls2 v, (n < length ls2)%nat -> length ls1 = length ls2 -> goodSize (length ls1) -> firstn (S n) ls1 = firstn (S n) (Array.upd ls2 (natToW n) v) -> firstn n ls1 = firstn n ls2.
  clear.
  intros.
  apply firstn_S in H2; try rewrite upd_length; try congruence.
  rewrite H2.
  rewrite upd_updN; try (eapply goodSize_weaken; eauto).
  auto.
Qed.

Lemma evalInstrs_cons_fwd : forall i is stn st st_new,
  evalInstrs stn st (i :: is) = Some st_new -> exists st',
    evalInstr stn st i = Some st' /\ evalInstrs stn st' is = Some st_new.
  Transparent evalInstrs.
  simpl; intros.
  destruct (evalInstr stn st i); try discriminate.
  eauto.
  Opaque evalInstrs.
Qed.

Require Import Bedrock.Platform.Wrap.
Import DefineStructured.

Lemma evalInstrs_cons_fwd_None : forall (stn : settings) i (is1 : list instr) (st : state),
  evalInstrs stn st (i :: is1) = None ->
  evalInstr stn st i = None \/
  (exists st' : state,
    evalInstr stn st i = Some st' /\ evalInstrs stn st' is1 = None).
  intros; rewrite evalInstr_evalInstrs in *.
  apply evalInstrs_app_fwd_None. auto.
Qed.

Section Lemmas.

  Lemma sum_S: forall a b, a + S b = S a + b.
    intros; omega.
  Qed.

  Hint Rewrite sum_S : arith.
  Hint Resolve S_le_lt.
  Hint Resolve sel_upd_firstn.
  Hint Resolve firstn_S_upd.
  Hint Resolve Max.le_max_l Max.le_max_r.

  Lemma le_plus_lt : forall a b c, (a + c <= b -> 0 < c -> a < b)%nat.
    intros; omega.
  Qed.

  Lemma lt_max_l : forall l n m, (l < n -> l < max n m)%nat.
    intros; assert (n <= max n m)%nat by eauto; omega.
  Qed.

  Lemma lt_max_r : forall l n m, (l < m -> l < max n m)%nat.
    intros; assert (m <= max n m)%nat by eauto; omega.
  Qed.

  Hint Resolve le_plus_lt lt_max_l lt_max_r.

  Lemma plus_le : forall a b c d, (a + b <= c -> d <= b -> a + d <= c)%nat.
    intros; omega.
  Qed.

  Hint Resolve plus_le.

  Lemma plus_lt : forall a b c d, (a + b <= c -> d < b -> a + d < c)%nat.
    intros; omega.
  Qed.

  Hint Resolve lt_le_S plus_lt.

  Lemma lt_gt_flip : forall a b, (a < b -> b > a)%nat.
    intros; omega.
  Qed.

  Lemma le_ge_flip : forall a b, (a <= b -> b >= a)%nat.
    intros; omega.
  Qed.

  Lemma plus_max_l: forall a b c, (a + max b (S c) >= a + b)%nat.
    intros; apply le_ge_flip; eauto.
  Qed.

  Lemma S_plus_max_r: forall a b c, (a + max b (S c) >= S a + c)%nat.
    intros; apply le_ge_flip; simpl; eauto.
  Qed.

  Lemma S_max_simpl: forall n a b, (n + max a (S b) > n)%nat.
      induction n; induction a; induction b; simpl; intuition.
  Qed.

  Lemma plus_max_tran_r: forall a b c n, (n < c -> b + max a (S c) > n + S b)%nat.
    intros; replace (n + S b) with (b + S n) by omega; apply lt_gt_flip; simpl; eauto.
  Qed.

End Lemmas.
