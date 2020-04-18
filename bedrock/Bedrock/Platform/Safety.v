Require Import Coq.omega.Omega.
Require Import Bedrock.Bedrock Bedrock.Platform.PreAutoSep Bedrock.Platform.Sys.
Import XCAP.


Definition goodSize' (n : nat) := (N.of_nat n < 1 + Npow2 32)%N.

Lemma wordToNat_ninj : forall sz (u v : word sz),
  u <> v
  -> wordToNat u <> wordToNat v.
  intros; intro; apply H.
  assert (natToWord sz (wordToNat u) = natToWord sz (wordToNat v)) by congruence.
  repeat rewrite natToWord_wordToNat in H1.
  assumption.
Qed.

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

Require Import Bedrock.DepList.

Fixpoint smem_put ls (sm : smem' ls) (w : W) (v : B) : smem' ls :=
  match sm with
    | HNil => HNil
    | HCons w' _ v' sm' =>
      HCons (if H.addr_dec w w' then Some v else v') (smem_put _ sm' w v)
  end.

Fixpoint smem_clear ls (sm : smem' ls) (w : W) : smem' ls :=
  match sm with
    | HNil => HNil
    | HCons w' _ v sm' =>
      HCons (if H.addr_dec w w' then None else v) (smem_clear _ sm' w)
  end.

Fixpoint smem_graft (sm sm' : smem) (p : W) (len : nat) : smem :=
  match len with
    | O => sm
    | S len' =>
      match smem_get p sm' with
        | None => sm
        | Some v => smem_put _ (smem_graft sm sm' (p ^+ $1) len') p v
      end
  end.

Section OpSem.
  Variable m : module.
  Variable stn : settings.
  Variable prog : program.

  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Definition labelSys' (l_pre : string * spec) :=
    (Global (fst l_pre), Precondition (snd l_pre) None).

  Definition labelSys (l : LabelMap.key) (pre : assert) :=
    fst l = "sys"
    /\ In (snd l, pre) (map labelSys' (
      ("abort", abortS)
      :: ("printInt", printIntS)
      :: ("listen", listenS)
      :: ("accept", acceptS)
      :: ("connect", connectS)
      :: ("read", readS)
      :: ("write", writeS)
      :: ("declare", declareS)
      :: ("wait", waitS)
      :: ("close", closeS)
      :: nil)).

  Hypothesis impSys :
    LabelMap.fold (fun l pre P => labelSys l pre /\ P) (Imports m) True.

  Lemma preserve : forall (ls : list (LabelMap.key * assert)) Q,
    fold_left (fun P p => labelSys (fst p) (snd p) /\ P) ls Q
    -> Q.
    induction ls; simpl in *; intuition.
    apply IHls in H; tauto.
  Qed.

  Theorem impSys' : forall l pre, LabelMap.MapsTo l pre (Imports m)
    -> labelSys l pre.
    rewrite LabelMap.fold_1 in impSys; intros.
    apply LabelMap.elements_1 in H.
    generalize dependent True.
    clear impSys; induction H; simpl in *; intuition.

    hnf in H; simpl in H; intuition subst.
    apply preserve in impSys; tauto.

    eauto.
  Qed.

  Hypothesis agree : forall l pre bl, LabelMap.MapsTo l (pre, bl) (Blocks m)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis agreeImp : forall l pre, LabelMap.MapsTo l pre (Imports m)
    -> exists w, Labels stn l = Some w
      /\ prog w = None.

  Hypothesis omitImp : forall l w,
    Labels stn ("sys", l) = Some w
    -> prog w = None.

  Hypothesis ok : moduleOk m.

  Hint Constructors reachable sys_step sys_reachable.

  Definition goodState (st : state') :=
    exists l pre, Labels stn l = Some (fst st)
      /\ interp (specs m stn) (pre (stn, snd st))
      /\ (LabelMap.MapsTo l pre (Imports m)
        \/ exists bl, LabelMap.MapsTo l (pre, bl) (Blocks m)).

  Lemma unsplit_smem_get' : forall a v ls m m',
    smem_get' ls a m = Some v
    -> smem_get' ls a (join' ls m m') = Some v.
    induction ls; simpl; intuition.
    destruct (H.addr_dec a0 a); subst.
    rewrite H; auto.
    eauto.
  Qed.

  Lemma unsplit_smem_get : forall a m v m0 m1,
    smem_get a m = Some v
    -> split m0 m m1
      -> smem_get a m0 = Some v.
    unfold split; intuition subst; apply unsplit_smem_get'; auto.
  Qed.

  Lemma comeOnOut : forall P Q R,
    P * Q * R ===> Q * (P * R).
    clear; sepLemma.
  Qed.

  Lemma locals_mapped' : forall specs stn st vs ns sp P,
    interp specs (![array (toArray ns vs) sp * P] (stn, st))
    -> mapped sp (length ns * 4) (Mem st).
    induction ns; simpl; intuition; hnf; intuition.
    unfold array in H.
    assert (interp specs (![ptsto32m' nil sp 0 (vs a :: toArray ns vs) * P] (stn0, st))).
    eapply ILTacCommon.interp_interp_himp; eauto.
    eapply himp_star_frame; [ apply Arrays.ptsto32m'_in | reflexivity ].
    clear H.
    simpl in *.
    assert (n < 4 \/ (n >= 4 /\ n - 4 < length ns * 4))%nat by omega.
    intuition.
    rewrite sepFormula_eq in H2; propxFo.
    unfold smem_get_word, H.footprint_w in H6.
    repeat match type of H6 with
             | match ?E with None => _ | _ => _ end = _ => case_eq E; intros;
               try match goal with
                     | [ H : _ = _ |- _ ] => rewrite H in H6
                   end; try discriminate
           end.
    inversion H3; clear H3; subst.

    do 2 (eapply unsplit_smem_get in H11; eauto).
    rewrite get_memoryIn in H11.
    replace (sp ^+ $0 ^+ $3) with (sp ^+ $3) in * by words.
    congruence.

    inversion H13; clear H13; subst.
    do 2 (eapply unsplit_smem_get in H10; eauto).
    rewrite get_memoryIn in H10.
    replace (sp ^+ $0 ^+ $2) with (sp ^+ $2) in * by words.
    congruence.

    inversion H12; clear H12; subst.
    do 2 (eapply unsplit_smem_get in H9; eauto).
    rewrite get_memoryIn in H9.
    replace (sp ^+ $0 ^+ $1) with (sp ^+ $1) in * by words.
    congruence.

    inversion H13; clear H13; subst.
    do 2 (eapply unsplit_smem_get in H; eauto).
    rewrite get_memoryIn in H.
    congruence.

    inversion H12.

    assert (interp specs (![array (toArray ns vs) (sp ^+ $4) * ((sp ^+ $ (0)) =*> vs a * P)] (stn0, st))).
    eapply ILTacCommon.interp_interp_himp; eauto.
    clear.

    etransitivity; [ apply comeOnOut | ].
    apply Himp_star_frame; [ | apply Himp_refl ].
    eapply Himp_trans; [ | apply ptsto32m'_out ].
    apply ptsto32m'_shift_base'; auto.

    clear H2.
    apply IHns in H3.
    hnf in H3.
    eapply H3.
    eauto.
    replace (sp ^+ $4 ^+ $ (n - 4)) with (sp ^+ $ (n)); auto.
    rewrite natToW_minus by auto.
    unfold natToW.
    W_eq.
  Qed.

  Lemma locals_mapped : forall specs ns vs res sp stn st P,
    interp specs (![locals ns vs res sp * P] (stn, st))
    -> mapped sp (length ns * 4) (Mem st).
    unfold locals; intros.
    assert (interp specs
      (![array (toArray ns vs) sp * ([|NoDup ns|] *
        (sp ^+ $ (Datatypes.length ns * 4)) =?> res * P)]
      (stn0, st))).
    generalize H; clear; intros; step auto_ext.
    eapply locals_mapped'; eauto.
  Qed.

  Lemma array8_mapped : forall specs stn bs p m,
    interp specs (array8 bs p stn m)
    -> forall n, (n < length bs)%nat
      -> smem_get (p ^+ $ (n)) m <> None.
    induction bs; simpl; post.
    intuition.
    destruct n.
    replace (p ^+ $0) with p in H1 by words.
    eapply split_smem_get in H2; eauto.
    rewrite H1 in H2; discriminate.
    eapply IHbs in H4; try tauto.
    instantiate (1 := n); auto.
    replace (p ^+ $1 ^+ $ (n)) with (p ^+ $ (S n))
      by (rewrite natToW_S; unfold natToW; W_eq).
    case_eq (smem_get (p ^+ $ (S n)) x0); intros; auto.
    eapply split_smem_get in H2; eauto.
    congruence.
  Qed.

  Lemma bytes_mapped : forall specs p sz stn st P,
    interp specs (![p =?>8 sz * P] (stn, st))
    -> mapped p sz (Mem st).
    unfold buffer; rewrite sepFormula_eq; post.
    hnf; intros.
    eapply split_comm in H1; eapply split_semp in H1; eauto; subst.
    eapply array8_mapped in H; eauto.
    case_eq (smem_get (p ^+ $ (n)) x2); intros; try congruence.
    eapply split_smem_get in H0; eauto.
    rewrite get_memoryIn in H0.
    congruence.
  Qed.

  Lemma prove_ReadWord : forall stn m (p : W) v st,
    evalInstrs stn st (Assign Rv (LvMem p) :: nil) <> None
    -> (forall st', evalInstrs stn st (Assign Rv (LvMem p) :: nil) = Some st'
      -> Regs st' Rv = v)
    -> Mem st = m
    -> ReadWord stn m p = Some v.
    intros.
    match goal with
      | [ H : (?X <> None)%type |- _ ] => case_eq X; intros; try tauto
    end.
    Transparent evalInstrs.
    simpl in *.
    subst.
    destruct (ReadWord stn0 (Mem st) p); simpl in *; try congruence.
    injection H2; clear H2; intros; subst; auto.
    specialize (H0 _ eq_refl).
    subst; auto.
  Qed.

  Lemma evalInstrs_slot : forall stn st n,
    evalInstrs stn st (Assign Rv (LvMem (Imm (Regs st Sp ^+ $ (n)))) :: nil)
    = evalInstrs stn st (Assign Rv (LvMem (Sp + $ (n))%loc) :: nil).
    auto.
  Qed.

  Opaque evalInstrs.

  Lemma specs_hit : forall w pre,
    specs m stn w = Some pre
    -> exists l, Labels stn l = Some w
      /\ (LabelMap.MapsTo l pre (Imports m)
        \/ exists bl, LabelMap.MapsTo l (pre, bl) (Blocks m)).
    intros.
    apply specs_hit in H; post; eauto.
    apply specs'_hit in H0; post; eauto.
  Qed.

  Lemma smem_get'_emp : forall p ls,
    smem_get' ls p (smem_emp' ls) = None.
    induction ls; simpl; intuition.
    destruct (H.addr_dec a p); auto.
  Qed.

  Lemma smem_get_emp : forall p,
    smem_get p smem_emp = None.
    intros; apply smem_get'_emp.
  Qed.

  Lemma must_be' : forall p ls m1 m2,
    smem_get' ls p m1 = None
    -> smem_get' ls p m2 = None
    -> smem_get' ls p (join' ls m1 m2) = None.
    clear; induction ls; simpl; intuition.
    destruct (H.addr_dec a p); subst; intuition.
    rewrite H; auto.
  Qed.

  Lemma must_be : forall m m1 m2 p,
    split m m1 m2
    -> smem_get p m <> None
    -> smem_get p m1 = None
    -> smem_get p m2 <> None.
    destruct 1; intuition subst.
    unfold smem_get, join in H1.
    rewrite must_be' in H1; eauto.
  Qed.

  Lemma characterize_array8_fwd : forall specs stn bs base m m',
    interp specs (array8 bs base stn m)
    -> (forall p, (forall n, (n < length bs)%nat -> p <> base ^+ $ (n))
      -> smem_get p m' = smem_get p m)
    -> (forall p, smem_get p m <> None ->
      exists n, (n < length bs)%nat /\ p = base ^+ $ (n)).
    clear; induction bs; simpl; propxFo.

    hnf in H3; subst.
    rewrite smem_get_emp in H1; tauto.
    destruct (weq p base); subst.
    exists 0; intuition.
    unfold H.addr in *; W_eq.

    assert (smem_get p x0 <> None).
    eapply must_be; eauto.
    case_eq (smem_get p x0); intros; try congruence.
    clear H.
    edestruct IHbs; eauto.
    instantiate (1 := p); congruence.
    intuition subst.
    exists (S x1); intuition.
    change ($ (S x1)) with (natToW (S x1)).
    rewrite (natToW_S x1).
    unfold natToW.
    unfold H.addr in *.
    W_eq.
  Qed.

  Lemma split_None : forall p m m1 m2,
    smem_get p m = None
    -> split m m1 m2
    -> smem_get p m2 = None.
    intros; case_eq (smem_get p m2); intros; auto.
    eapply split_smem_get in H0; eauto.
    congruence.
  Qed.

  Lemma split'_None' : forall p ls m1 m2,
    smem_get' ls p m1 = None
    -> smem_get' ls p m2 = smem_get' ls p (join' ls m1 m2).
    induction ls; simpl; intuition.
    destruct (H.addr_dec a p); subst; intuition.
    rewrite H; auto.
  Qed.

  Lemma split_None' : forall p m m1 m2,
    split m m1 m2
    -> smem_get p m1 = None
    -> smem_get p m2 = smem_get p m.
    destruct 1; subst; apply split'_None'.
  Qed.

  Lemma characterize_array8_bwd : forall specs stn bs base m,
    interp specs (array8 bs base stn m)
    -> (forall n, (n < length bs)%nat
      -> smem_get (base ^+ $ (n)) m <> None).
    induction bs; simpl; propxFo.

    intuition.

    destruct n.
    erewrite split_smem_get in H1.
    discriminate.
    eauto.
    replace (base ^+ $0) with base by words.
    eauto.

    eapply IHbs.
    eauto.
    instantiate (1 := n); omega.
    replace (base ^+ $1 ^+ $ (n)) with (base ^+ $ (S n))
      by (rewrite natToW_S; unfold natToW; words).
    eauto using split_None.
  Qed.

  Lemma semp_eta' : forall ls, NoDup ls
    -> forall m,
      (forall p, In p ls -> smem_get' ls p m = None)
      -> m = smem_emp' ls.
    clear; induction 1; simpl; intuition.
    rewrite (hlist_nil_only _ m); auto.
    rewrite (hlist_eta _ m); f_equal.
    specialize (H1 x); destruct (H.addr_dec x x); tauto.
    apply IHNoDup; intros.
    specialize (H1 p); destruct (H.addr_dec x p); subst; eauto; tauto.
  Qed.

  Lemma semp_eta : forall m,
    (forall p, smem_get p m = None)
    -> semp m.
    intros; apply semp_eta'; auto.
    apply H.NoDup_all_addr.
  Qed.

  Lemma get_clear_ne' : forall a a' ls (sm : smem' ls),
    a <> a'
    -> smem_get' ls a (smem_clear _ sm a') = smem_get' ls a sm.
    induction sm; simpl; intuition.
    destruct (H.addr_dec x a); auto.
    destruct (H.addr_dec a' x); congruence.
  Qed.

  Lemma get_clear_ne : forall a a' sm,
    a <> a'
    -> smem_get a (smem_clear _ sm a') = smem_get a sm.
    intros; apply get_clear_ne'; auto.
  Qed.

  Lemma get_clear_eq' : forall a ls (sm : smem' ls),
    smem_get' ls a (smem_clear _ sm a) = None.
    induction sm; simpl; intuition.
    destruct (H.addr_dec x a); auto.
    destruct (H.addr_dec a x); congruence.
  Qed.

  Lemma get_clear_eq : forall a sm,
    smem_get a (smem_clear _ sm a) = None.
    intros; apply get_clear_eq'.
  Qed.

  Hint Rewrite get_clear_eq get_clear_ne
    using solve [ assumption | W_neq ] : get.

  Lemma get_put_eq' : forall a v ls (sm : smem' ls),
    In a ls
    -> smem_get' ls a (smem_put _ sm a v) = Some v.
    induction sm; simpl; intuition.
    subst.
    destruct (H.addr_dec a a); intuition idtac.
    destruct (H.addr_dec x a); intuition idtac.
    subst.
    destruct (H.addr_dec a a); intuition idtac.
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

  Lemma get_put_eq : forall a v sm,
    smem_get a (smem_put _ sm a v) = Some v.
    intros; apply get_put_eq'.
    apply allWords_universal.
  Qed.

  Lemma get_put_ne' : forall a a' v ls (sm : smem' ls),
    a <> a'
    -> smem_get' ls a (smem_put _ sm a' v) = smem_get' ls a sm.
    induction sm; simpl; intuition.
    destruct (H.addr_dec a' x); intuition idtac.
    destruct (H.addr_dec x a); intuition idtac.
    congruence.
    destruct (H.addr_dec x a); intuition idtac.
  Qed.

  Lemma get_put_ne : forall a a' v sm,
    a <> a'
    -> smem_get a (smem_put _ sm a' v) = smem_get a sm.
    intros; apply get_put_ne'; auto.
  Qed.

  Hint Rewrite smem_get_emp get_put_eq get_put_ne
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

  Lemma disjoint_get' : forall ls sm1 sm2,
    NoDup ls
    -> List.Forall (fun w => smem_get' ls w sm1 <> None -> smem_get' ls w sm2 <> None -> False) ls
    -> disjoint' ls sm1 sm2.
    induction sm1; simpl; intuition; rewrite (hlist_eta _ sm2) in *; simpl in *.
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
    induction sm1; simpl; intuition; rewrite (hlist_eta _ sm2) in *; simpl in *;
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

  Lemma disjoint_get_fwd : forall sm1 sm2,
    disjoint sm1 sm2
    -> (forall w, smem_get w sm1 <> None -> smem_get w sm2 <> None -> False).
    intros; eapply disjoint_get_fwd' in H; try apply BedrockHeap.NoDup_all_addr.
    assert (In w H.all_addr) by apply allWords_universal.
    generalize (proj1 (Forall_forall _ _) H _ H2); tauto.
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
    rewrite (hlist_eta _ sm'); f_equal.
    apply IHsm; auto.
    eapply Forall_weaken'; eauto.
    simpl; intros.
    destruct (H.addr_dec x x0); subst; tauto.
  Qed.

  Lemma split_put_clear : forall sm sm1 sm2 a v,
    split sm sm1 sm2
    -> smem_get a sm2 = Some v
    -> split sm (smem_put _ sm1 a v) (smem_clear _ sm2 a).
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

  Lemma recharacterize_array8 : forall specs stn sz base m,
    (forall n, (0 < n < sz)%nat
      -> base ^+ $ (n) <> base)
    -> (forall n, (n < sz)%nat
      -> smem_get (base ^+ $ (n)) m <> None)
    -> (forall p, smem_get p m <> None ->
      exists n, (n < sz)%nat /\ p = base ^+ $ (n))
    -> exists bs, length bs = sz /\ interp specs (array8 bs base stn m).
    clear; induction sz; simpl; intuition.

    exists nil; simpl; propxFo.
    apply semp_eta.
    intros.
    specialize (H1 p).
    destruct (smem_get p m); auto.
    destruct H1.
    congruence.
    intuition.

    generalize (H0 0); replace (base ^+ $0) with base by words;
      case_eq (smem_get base m); intros; try solve [ elimtype False; eauto ].
    clear H3.
    edestruct IHsz.
    instantiate (1 := base ^+ $1).
    intros.
    replace (base ^+ $ (1) ^+ $ (n)) with (base ^+ natToW (S n)) in *
      by (rewrite natToW_S; unfold natToW; W_eq).
    intros.
    eapply H.
    instantiate (1 := n); auto.
    apply (f_equal (fun x => x ^- $1)) in H4.
    rewrite natToW_S in H4.
    unfold natToW in H4.
    replace (base ^+ ($1 ^+ $ (n)) ^- $1) with (base ^+ $ (n)) in H4 by W_eq.
    replace (base ^+ $1 ^- $1) with base in H4 by W_eq.
    auto.

    instantiate (1 := smem_clear _ m base).
    intros.
    replace (base ^+ $ (1) ^+ $ (n)) with (base ^+ natToW (S n)) in H4
      by (rewrite natToW_S; unfold natToW; W_eq).
    rewrite get_clear_ne in H4.
    apply H0 with (S n).
    auto.
    auto.
    intro.
    eapply H.
    2: eauto.
    auto.

    intros.
    destruct (weq p base); subst.
    rewrite get_clear_eq in H3; tauto.
    rewrite get_clear_ne in H3; auto.
    apply H1 in H3.
    propxFo; subst.
    destruct x.
    elimtype False; apply n.
    words.
    exists x; intuition.
    rewrite natToW_S.
    unfold natToW.
    unfold H.addr in *.
    W_eq.

    intuition subst; simpl; exists (b :: x); propxFo.
    exists (smem_put _ smem_emp base b).
    exists (smem_clear _ m base).
    descend.
    apply split_put_clear.
    apply split_a_semp_a.
    auto.
    apply get_put_eq.
    rewrite get_put_ne; auto.
    autorewrite with get; auto.
  Qed.

  Lemma disjoint_eta' : forall ls, NoDup ls
    -> forall m1 m2,
      (forall p v1 v2, In p ls
        -> smem_get' ls p m1 = Some v1
        -> smem_get' ls p m2 = Some v2
        -> False)
      -> disjoint' ls m1 m2.
    induction 1; simpl; intuition auto 1.
    specialize (H1 x); destruct (H.addr_dec x x); try tauto.
    destruct (hlist_hd m1); auto; destruct (hlist_hd m2); auto.
    elimtype False; eauto.

    apply IHNoDup; intros.
    specialize (H1 p).
    destruct (H.addr_dec x p); try congruence.
    eauto.
  Qed.

  Lemma disjoint_eta : forall m1 m2,
    (forall p v1 v2, smem_get p m1 = Some v1
      -> smem_get p m2 = Some v2
      -> False)
    -> disjoint m1 m2.
    intros; apply disjoint_eta'.
    apply H.NoDup_all_addr.
    eauto.
  Qed.

  Lemma get_graft : forall p0 v sz m m' p,
    smem_get p0 (smem_graft m m' p sz) = Some v
    -> smem_get p0 m = Some v \/ (exists n, p0 = p ^+ $ (n)
      /\ (n < sz)%nat
      /\ smem_get p0 m' = Some v).
    clear; induction sz; simpl; intuition auto 1.
    case_eq (smem_get p m'); intros;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *; try congruence; eauto
      end.
    destruct (weq p0 p); subst.
    rewrite get_put_eq in *.
    right; exists 0; intuition.
    unfold H.addr in *; W_eq.
    rewrite get_put_ne in *; eauto.
    destruct (IHsz _ _ _ H) as [ | [ ? [ ] ] ]; subst; intuition eauto.
    right; exists (S x); intuition.
    unfold H.addr in *.
    change ($ (S x)) with (natToW (S x)).
    rewrite (natToW_S x).
    unfold natToW in *; words.
  Qed.

  Lemma disjoint_not_both' : forall p v ls m1 m2,
    disjoint' ls m1 m2
    -> smem_get' ls p m2 = Some v
    -> smem_get' ls p m1 = None.
    clear; induction ls; simpl; intuition.

    destruct (H.addr_dec a p); eauto.

    destruct (H.addr_dec a p); eauto; congruence.
  Qed.

  Lemma disjoint_not_both : forall m1 m2 p v,
    disjoint m1 m2
    -> smem_get p m2 = Some v
    -> smem_get p m1 = None.
    intros; eapply disjoint_not_both'; eauto.
  Qed.

  Lemma smem_canon' : forall ls, NoDup ls
    -> forall m1 m2,
      (forall p, In p ls -> smem_get' ls p m1 = smem_get' ls p m2)
      -> m1 = m2.
    clear; induction 1; simpl; intuition.
    rewrite (hlist_nil_only _ m1); rewrite (hlist_nil_only _ m2); auto.
    rewrite (hlist_eta _ m1); rewrite (hlist_eta _ m2).
    f_equal.
    specialize (H1 x); destruct (H.addr_dec x x); tauto.
    apply IHNoDup; intros.
    specialize (H1 p).
    destruct (H.addr_dec x p).
    congruence.
    auto.
  Qed.

  Lemma smem_canon : forall m1 m2,
    (forall p, smem_get p m1 = smem_get p m2)
    -> m1 = m2.
    intros; apply smem_canon'.
    apply H.NoDup_all_addr.
    auto.
  Qed.

  Fixpoint smem_minus' ls : smem' ls -> smem' ls -> smem' ls :=
    match ls with
      | nil => fun sm _ => sm
      | a :: ls' => fun sm sm' =>
        HCons match hlist_hd sm' with
                | Some _ => None
                | _ => hlist_hd sm
              end (smem_minus' _ (hlist_tl sm) (hlist_tl sm'))
    end.

  Definition smem_minus (sm sm' : smem) := smem_minus' _ sm sm'.

  Lemma disjoint_minus' : forall ls, NoDup ls
    -> forall m m',
      (forall p v, In p ls
        -> smem_get' ls p m' = Some v -> smem_get' ls p m = Some v)
      -> disjoint' ls (smem_minus' _ m m') m'.
    clear; induction 1; simpl; intuition.
    specialize (H1 x).
    destruct (H.addr_dec x x); try tauto.
    destruct (hlist_hd m'); eauto.
    apply IHNoDup; intros.
    specialize (H1 p); destruct (H.addr_dec x p); try congruence.
    eauto.
  Qed.

  Lemma disjoint_minus : forall m m',
    (forall p v, smem_get p m' = Some v -> smem_get p m = Some v)
    -> disjoint (smem_minus' _ m m') m'.
    intros; apply disjoint_minus'; auto.
    apply H.NoDup_all_addr.
  Qed.

  Lemma join_minus' : forall ls, NoDup ls
    -> forall m m',
      (forall p v, In p ls
        -> smem_get' ls p m' = Some v -> smem_get' ls p m = Some v)
      -> m = join' ls (smem_minus' _ m m') m'.
    clear; induction 1; simpl; intuition.
    rewrite (hlist_nil_only _ m); auto.
    rewrite (hlist_eta _ m); simpl; f_equal.
    specialize (H1 x); destruct (H.addr_dec x x); try tauto.
    destruct (hlist_hd m'); eauto.
    destruct (hlist_hd m); auto.

    apply IHNoDup; intros.
    specialize (H1 p); destruct (H.addr_dec x p); subst.
    tauto.
    eauto.
  Qed.

  Lemma join_minus : forall m m',
    (forall p v, smem_get p m' = Some v -> smem_get p m = Some v)
    -> m = join (smem_minus' _ m m') m'.
    intros; apply join_minus'; auto.
    apply H.NoDup_all_addr.
  Qed.

  Lemma split_minus : forall m m',
    (forall p v, smem_get p m' = Some v -> smem_get p m = Some v)
    -> split m (smem_minus m m') m'.
    unfold split; intuition subst; auto using disjoint_minus, join_minus.
  Qed.

  Lemma no_overlap' : forall p v1 v2 ls m1 m2,
    disjoint' ls m1 m2
    -> In p ls
    -> smem_get' ls p m1 = Some v1
    -> smem_get' ls p m2 = Some v2
    -> False.
    induction ls; simpl; intuition subst.
    destruct (H.addr_dec p p); try tauto; congruence.
    destruct (H.addr_dec p p); try tauto; congruence.
    destruct (H.addr_dec a p); eauto; congruence.
    destruct (H.addr_dec a p); eauto; congruence.
  Qed.

  Lemma no_overlap : forall m1 m2 p v1 v2,
    disjoint m1 m2
    -> smem_get p m1 = Some v1
    -> smem_get p m2 = Some v2
    -> False.
    intros; eapply no_overlap'; eauto.
    apply allWords_universal.
  Qed.

  Lemma not_zero : forall sz n,
    (0 < n < pow2 sz)%nat
    -> natToWord sz n <> wzero sz.
    intros; intro.
    apply (f_equal (@wordToNat _)) in H0.
    rewrite wordToNat_natToWord_idempotent in H0.
    subst.
    rewrite roundTrip_0 in H.
    omega.
    pre_nomega.
    rewrite Npow2_nat.
    auto.
  Qed.

  Lemma get_minus_out' : forall p ls m1 m2,
    smem_get' ls p m2 = None
    -> smem_get' ls p (smem_minus' _ m1 m2) = smem_get' ls p m1.
    clear; induction ls; simpl; intuition.
    destruct (H.addr_dec a p); intuition.
    rewrite H; auto.
  Qed.

  Lemma get_minus_out : forall p m1 m2,
    smem_get p m2 = None
    -> smem_get p (smem_minus m1 m2) = smem_get p m1.
    intros; apply get_minus_out'; auto.
  Qed.

  Lemma get_minus_in' : forall p ls m1 m2,
    smem_get' ls p m2 <> None
    -> smem_get' ls p (smem_minus' _ m1 m2) = None.
    clear; induction ls; simpl; intuition.
    destruct (H.addr_dec a p); intuition.
    destruct (hlist_hd m2); tauto.
  Qed.

  Lemma get_minus_in : forall p m1 m2,
    smem_get p m2 <> None
    -> smem_get p (smem_minus m1 m2) = None.
    intros; apply get_minus_in'; auto.
  Qed.

  Lemma tickle_bytes : forall specs p sz P stn st st',
    interp specs (![ p =?>8 sz * P] (stn, st))
    -> onlyChange p sz (Mem st) (Mem st')
    -> interp specs (![ p =?>8 sz * P] (stn, st')).
    clear; unfold buffer; rewrite sepFormula_eq.
    intros.
    apply simplify_fwd in H; simpl in *.
    repeat match goal with
             | [ H : Logic.ex _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
           end.
    apply simplify_bwd in H3.
    hnf in H5; subst.
    apply split_comm in H1; apply split_semp in H1; try reflexivity; subst.

    edestruct recharacterize_array8.

    instantiate (1 := p).
    instantiate (1 := length x1).
    intros.
    apply word_neq.
    replace (p ^+ $ (n) ^- p) with (natToW n).
    apply not_zero.
    eapply array8_bound in H3.
    generalize dependent 32.
    intros.
    omega.
    unfold H.addr, natToW in *; W_eq.

    instantiate (1 := smem_minus (memoryIn (Mem st')) x0).
    intros.
    eapply characterize_array8_bwd in H3; eauto.

    rewrite get_minus_out.
    case_eq (smem_get (p ^+ $ (n)) x2); intros; try congruence.
    eapply unsplit_smem_get in H4; eauto.
    repeat rewrite get_memoryIn in *.
    destruct H0.
    specialize (SameMapped (p ^+ $ (n))).
    intuition.

    case_eq (smem_get (p ^+ $ (n)) x2); intros; try congruence.
    case_eq (smem_get (p ^+ $ (n)) x0); intros; try congruence.
    destruct H.
    elimtype False; eapply no_overlap; eauto.

    intros.
    destruct H0.
    eapply characterize_array8_fwd; eauto.
    case_eq (smem_get p0 x0); intros.
    rewrite get_minus_in in H1; congruence.
    rewrite get_minus_out in H1 by congruence.
    assert (smem_get p0 (memoryIn (Mem st)) <> None).
    repeat rewrite get_memoryIn in *.
    specialize (SameMapped p0); intuition.
    eapply must_be; eauto; apply split_comm; auto.

    intuition.
    propxFo.
    descend.
    apply split_minus; intros.
    assert (smem_get p0 (memoryIn (Mem st)) = Some v)
      by (eapply split_smem_get; eauto).
    repeat rewrite get_memoryIn in *.
    destruct H0.
    rewrite Elsewhere; auto.
    intros.
    destruct (weq p0 (p ^+ $ (n))); subst; auto.
    eapply characterize_array8_bwd in H3; eauto.
    case_eq (smem_get (p ^+ $ (n)) x2); intros; try congruence.
    destruct H; intro; eauto using no_overlap.

    apply split_comm; apply split_a_semp_a.

    eauto.
    eauto.
    reflexivity.
    auto.
  Qed.

  Ltac eqer := repeat (match goal with
                         | [ H : _ = _ |- _ ] => rewrite H in *
                         | [ H : Some _ = Some _ |- _ ] =>
                           injection H; clear H; intros
                         | [ H : Logic.ex _ |- _ ] => destruct H; try clear H
                         | [ H : _ /\ _ |- _ ] => destruct H; try clear H
                       end; subst).

  Lemma onlyChange_refl : forall p len m,
    onlyChange p len m m.
    constructor; intuition.
  Qed.

  Hint Immediate onlyChange_refl.

  Ltac prove_ReadWord :=
    eapply prove_ReadWord; hnf; intros; cbv beta in *;
      try rewrite evalInstrs_slot in *;
        match goal with
          | [ st : (W * state)%type |- _ ] => destruct st; simpl in *
          | [ st : state' |- _ ] => destruct st; simpl in *
        end;
        generalize dependent (specs m stn); intros;
          repeat match goal with
                   | [ H : interp _ _ |- _ ] => generalize dependent H
                   | [ H : context[evalInstrs] |- _ ] => generalize dependent H
                 end; clear; intros; evaluate auto_ext; auto.

  Lemma progress : forall st, goodState st
    -> exists st', sys_step stn prog st st'.
    unfold goodState; post;
      match goal with
        | [ x : label |- _ ] => destruct x
      end.

    match goal with
      | [ H : _ |- _ ] => specialize (impSys' _ _ H); intro Hi; hnf in Hi;
        unfold labelSys' in Hi; simpl in Hi; intuition subst;
          match goal with
            | [ H : (_, _) = (_, _) |- _ ] =>
              injection H; clear H; intros; subst
          end; eauto; post
    end;
    match goal with
      | [ H : interp ?specs (![locals ?a ?b ?c ?d * ?Q * ?R] ?X) |- _ ] =>
        let H' := fresh in
          assert (H' : interp specs (![locals a b c d * (Q * R)] X))
            by (generalize H; clear; intros; step auto_ext);
            clear H; rename H' into H;
              specialize (locals_mapped _ _ _ _ _ _ _ _ H);
                intro Hm; simpl in Hm
    end;
    try match goal with
          | [ H : interp ?specs (![?P * (?p =?>8 ?sz * ?Q)] ?X) |- _ ] =>
            let H' := fresh in
              assert (H' : interp specs (![p =?>8 sz * (P * Q)] X))
                by (generalize H; clear; intros; step auto_ext);
                clear H; rename H' into H;
                  specialize (bytes_mapped _ _ _ _ _ _ H);
                    intro Hb; simpl in Hb
        end;
    match goal with
      | [ H : specs _ _ _ = Some _ |- _ ] =>
        apply specs_hit in H; post; eauto
    end;
    try match goal with
          | [ st : state' |- Logic.ex _ ] =>
            solve [ exists (st#Rp, snd st); eauto
              | exists (st#Rp, snd st);
                match goal with
                  | [ _ : context["connect"] |- _ ] => eapply Connect
                  | [ _ : context["read"] |- _ ] => eapply Read
                  | _ => eapply Write
                end; eauto;
                match goal with
                  | [ H : interp _ _ |- ReadWord ?stn (Mem (snd ?st)) _ = Some _ ] =>
                    generalize H; clear; intros; prove_ReadWord
                end ]
        end.

    match goal with
      | [ H : _, H' : interp _ _ |- _ ] =>
        specialize (BlocksOk ok H); intro Hb; hnf in Hb;
          apply Hb in H'; [ | eapply specsOk; eauto ];
            clear Hb; post;
              specialize (agree _ _ _ H); destruct agree as [ ? [ ] ]
    end.
    eqer;
    match goal with
      | [ H : specs _ _ _ = Some _ |- _ ] =>
        apply specs_hit in H; post; eauto
    end;
    descend; apply Normal; unfold step;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H; eauto
      end.
  Qed.

  Lemma goOnIn : forall P Q R,
    Q * (P * R) ===> P * Q * R.
    clear; sepLemma.
  Qed.

  Lemma preservation : forall st, goodState st
    -> forall st', sys_step stn prog st st'
      -> goodState st'.
    unfold goodState; destruct 2; post;
      try match goal with
            | [ x : label, H : _ |- _ ] =>
              solve [ destruct x; specialize (impSys' _ _ H);
                intro Hi; hnf in Hi; unfold labelSys' in Hi; simpl in Hi;
                  intuition subst;
                    match goal with
                      | [ H : _ |- _ ] => apply omitImp in H;
                        match goal with
                          | [ H' : prog _ = None |- _ ] =>
                            unfold step in *; rewrite H' in *; discriminate
                        end
                    end ]

            | [ H : LabelMap.MapsTo _ _ (Blocks _), H' : interp _ _ |- _ ] =>
              solve [ specialize (BlocksOk ok H); intro Hb; hnf in Hb;
                apply Hb in H'; [ | eapply specsOk; eauto ];
                  clear Hb; post;
                    specialize (agree _ _ _ H); destruct agree as [ ? [ ] ];
                      unfold step in *; eqer;
                        apply specs_hit in H4; destruct H4; intuition idtac;
                          try match goal with
                                | [ H : Logic.ex _ |- _ ] => destruct H
                              end; eauto 10 ]

            | [ H1 : _, H2 : _ |- _ ] =>
              solve [ apply (inj _ _ _ H1) in H2; subst;
                specialize (omitImp _ _ H1);
                  match goal with
                    | [ H : _ |- _ ] => apply agree in H; post; congruence
                  end ]
          end;
      match goal with
        | [ x : label, H5 : LabelMap.MapsTo _ _ (Imports _) |- _ ] =>
          destruct x; specialize (impSys' _ _ H5);
            intro Hi; hnf in Hi; unfold labelSys' in Hi; simpl in Hi;
              intuition subst;
                match goal with
                  | [ H : (_, _) = (_, _) |- _ ] =>
                    injection H; clear H; intros; subst
                end; eauto; post;
                try match goal with
                      | [ H1 : _, H2 : _ |- _ ] =>
                        solve [ apply (inj _ _ _ H1) in H2;
                          cbv beta in H2; congruence ]
                    end; post;
                match goal with
                  | [ H : _ = _ |- _ ] => apply specs_hit in H; destruct H; intuition idtac
                end;
                match goal with
                  | [ st' : state |- _ ] => destruct st'; simpl in *; subst
                end; descend; eauto;
                match goal with
                  | [ H : forall x : state, _ |- _ ] =>
                    apply (Imply_sound (H _)); propxFo; descend;
                      try (apply ILTacCommon.ignore_regs; eassumption)
                end
      end;
      match goal with
        | [ H : interp (specs _ ?stn) (![?P] (_, snd ?st))%PropX |- _ ] =>
          match P with
            | context[locals _ ?V _ _] =>
              (eapply ILTacCommon.interp_interp_himp in H; [ | apply comeOnOut ];
                eapply ILTacCommon.interp_interp_himp; [ | apply goOnIn ];
                  eapply tickle_bytes; eauto;
                    assert (ReadWord stn (IL.Mem (snd st)) (st#Sp ^+ $8)
                      = Some (sel V "buffer")) by prove_ReadWord;
                    assert (ReadWord stn (IL.Mem (snd st)) (st#Sp ^+ $12)
                      = Some (sel V "size")) by prove_ReadWord;
                    cbv beta in *; simpl; congruence)
              || (eapply ILTacCommon.interp_interp_himp in H; [ | apply comeOnOut ];
                eapply ILTacCommon.interp_interp_himp; [ | apply goOnIn ];
                  eapply tickle_bytes; eauto;
                    assert (ReadWord stn (IL.Mem (snd st)) (st#Sp ^+ $4)
                      = Some (sel V "address")) by prove_ReadWord;
                    assert (ReadWord stn (IL.Mem (snd st)) (st#Sp ^+ $8)
                      = Some (sel V "size")) by prove_ReadWord;
                    cbv beta in *; simpl; congruence)
          end
      end.
  Qed.

  Lemma safety' : forall st, goodState st
    -> forall st', sys_reachable stn prog st st'
      -> goodState st'.
    induction 2; simpl; eauto using preservation.
  Qed.

  Theorem safety : forall st mn g pre, LabelMap.MapsTo (mn, Global g) pre (Exports m)
    -> Labels stn (mn, Global g) = Some (fst st)
    -> interp (specs0 m stn) (pre (stn, snd st))
    -> sys_safe stn prog st.
    unfold sys_safe; intros.
    eapply safety' in H2.
    auto using progress.
    hnf; descend; eauto.
    apply (ExportsSound ok) in H; eauto.
  Qed.
End OpSem.
