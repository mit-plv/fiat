Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith Bedrock.Bedrock Bedrock.sep.Locals Coq.Lists.List Bedrock.Platform.PreAutoSep.

Lemma wordToNat_wminus : forall sz (w u : word sz),
  u <= w
  -> wordToNat (w ^- u) = wordToNat w - wordToNat u.
  intros.
  eapply natToWord_inj; try eapply wordToNat_bound.
  2: generalize (wordToNat_bound w); omega.
  rewrite natToWord_wordToNat.
  unfold wminus.
  rewrite wneg_alt.
  unfold wnegN.
  pattern w at 1.
  rewrite <- (natToWord_wordToNat w).
  rewrite <- natToWord_plus.
  specialize (wordToNat_bound u); intro.
  destruct (le_lt_dec (wordToNat u) (wordToNat w)).
  replace (wordToNat w + (pow2 sz - wordToNat u))
    with (pow2 sz + (wordToNat w - wordToNat u)) by omega.
  rewrite natToWord_plus.
  rewrite natToWord_pow2.
  apply wplus_unit.
  elimtype False; apply H.
  nomega.
Qed.

Hint Rewrite wordToNat_wminus using assumption : sepFormula.

Lemma Nle_out : forall n m, (n <= m)%N -> (N.to_nat n <= N.to_nat m)%nat.
  intros; apply N.lt_eq_cases in H; intuition.
  apply Nlt_out in H0; auto.
Qed.

Lemma wordToNat_wplus : forall (w u : W),
  goodSize (wordToNat w + wordToNat u)
  -> wordToNat (w ^+ u) = wordToNat w + wordToNat u.
  intros.
  rewrite wplus_alt; unfold wplusN, wordBinN.
  apply wordToNat_natToWord_idempotent; auto.
Qed.

Lemma wordToNat_wmult : forall (w u : W),
  goodSize (wordToNat w * wordToNat u)
  -> wordToNat (w ^* u) = wordToNat w * wordToNat u.
  intros.
  rewrite wmult_alt; unfold wmultN, wordBinN.
  apply wordToNat_natToWord_idempotent; auto.
Qed.

Lemma wle_le : forall (n sz : W),
  n <= sz
  -> (wordToNat n <= wordToNat sz)%nat.
  intros; destruct (le_lt_dec (wordToNat n) (wordToNat sz)); auto.
  elimtype False; apply H.
  nomega.
Qed.

Local Hint Resolve simplify_fwd.

Lemma subst_qspecOut_fwd' : forall pc state (specs : codeSpec pc state) A B v v' qs (k : _ -> propX _ _ (A :: B :: nil)),
  interp specs (subst (subst (qspecOut qs k) v) v' ---> qspecOut qs (fun x => subst (subst (k x) v) v')).
  induction qs; simpl; intros.
  apply Imply_refl.
  apply Imply_I.
  eapply Exists_E.
  apply Env; simpl; eauto.
  simpl; intros.
  eapply Exists_I.
  eapply Imply_E.
  apply interp_weaken; eauto.
  eapply Env; simpl; eauto.
Qed.

Lemma subst_qspecOut_fwd : forall pc state (specs : codeSpec pc state) A v qs (k : _ -> propX _ _ (A :: nil)),
  interp specs (subst (qspecOut qs k) v)
  -> interp specs (qspecOut qs (fun x => subst (k x) v)).
  induction qs; propxFo; eauto.
Qed.

Lemma subst_qspecOut_bwd' : forall pc state (specs : codeSpec pc state) A B v v' qs (k : _ -> propX _ _ (A :: B :: nil)),
  interp specs (qspecOut qs (fun x => subst (subst (k x) v) v') ---> subst (subst (qspecOut qs k) v) v').
  induction qs; simpl; intros.
  apply Imply_refl.
  apply Imply_I.
  eapply Exists_E.
  apply Env; simpl; eauto.
  simpl; intros.
  eapply Exists_I.
  eapply Imply_E.
  apply interp_weaken; eauto.
  eapply Env; simpl; eauto.
Qed.

Lemma subst_qspecOut_bwd : forall pc state (specs : codeSpec pc state) A v qs (k : _ -> propX _ _ (A :: nil)),
  interp specs (qspecOut qs (fun x => subst (k x) v))
  -> interp specs (subst (qspecOut qs k) v).
  induction qs; propxFo; eauto.
Qed.

Fixpoint domain (qs : qspec) : Type :=
  match qs with
    | Programming.Body _ => unit
    | Quant _ f => sigT (fun x => domain (f x))
  end.

Fixpoint qspecOut' (qs : qspec) : domain qs -> HProp :=
  match qs with
    | Programming.Body P => fun _ => P
    | Quant _ f => fun d => qspecOut' (f (projT1 d)) (projT2 d)
  end.

Lemma qspecOut_fwd' : forall (specs : codeSpec W (settings * state)) qs k,
  interp specs (qspecOut qs k ---> Ex v : domain qs, k (qspecOut' qs v))%PropX.
  induction qs; simpl; intros.
  apply Imply_I; apply Exists_I with tt; apply Env; simpl; tauto.
  apply Imply_I; eapply Exists_E; [ apply Env; simpl; tauto | ].
  simpl; intros.
  eapply Exists_E.
  eapply Imply_E.
  apply interp_weaken; apply H.
  apply Env; simpl; eauto.
  simpl; intros.
  apply Exists_I with (existT _ B B0).
  apply Env; simpl; eauto.
Qed.

Lemma qspecOut_fwd : forall (specs : codeSpec W (settings * state)) qs k,
  interp specs (qspecOut qs k)
  -> exists v : domain qs, interp specs (k (qspecOut' qs v)).
  intros; apply (Imply_sound (qspecOut_fwd' _ _ _)) in H; propxFo; eauto.
Qed.

Lemma qspecOut_bwd' : forall (specs : codeSpec W (settings * state)) qs k v,
  interp specs (k (qspecOut' qs v) ---> qspecOut qs k).
  induction qs; simpl; intros.
  apply Imply_refl.
  destruct v; simpl.
  eapply Imply_trans; eauto.
  apply Imply_I; eapply Exists_I; apply Env; simpl; eauto.
Qed.

Lemma qspecOut_bwd : forall (specs : codeSpec W (settings * state)) qs k v,
  interp specs (k (qspecOut' qs v))
  -> interp specs (qspecOut qs k).
  intros; eapply (Imply_sound (qspecOut_bwd' _ _ _ _)); eauto.
Qed.

Lemma qspecOut_bwd'' : forall (specs : codeSpec W (settings * state)) qs k,
  interp specs ((Ex v, k (qspecOut' qs v)) ---> qspecOut qs k)%PropX.
  intros.
  apply Imply_I.
  eapply Exists_E; [ apply Env; simpl; eauto | ].
  simpl; intros.
  eapply Imply_E.
  apply interp_weaken; apply qspecOut_bwd'.
  apply Env; simpl; eauto.
Qed.

Theorem localsInvariant_in : forall ns' pre post ns res ns'' res' stn_st specs,
  interp specs (Ex st' : state,
    localsInvariant pre post false (fun w => w) ns res (fst stn_st, st')
    /\ [| evalInstrs (fst stn_st) st' (Assign (LvMem (Sp + 0)%loc) Rp :: nil)
      = Some (snd stn_st) |])%PropX
  -> (length ns' <= res)%nat
  -> res' = res - length ns'
  -> ns ++ ns' = ns''
  -> NoDup ("rp" :: ns ++ ns')
  -> (forall vs1 vs2, (forall x, In x ns
    -> sel vs1 x = sel vs2 x)
  -> pre vs1 = pre vs2)
  -> (forall vs1 vs2, (forall x, In x ns
    -> sel vs1 x = sel vs2 x)
  -> post vs1 = post vs2)
  -> interp specs (localsInvariant pre post true (fun w => w)
    ns'' res' stn_st).
  post; subst.
  apply subst_qspecOut_fwd in H.
  apply qspecOut_fwd in H.
  destruct H.
  post.
  change (locals ("rp" :: ns) x1 res (Regs x Sp))
    with (locals_in ("rp" :: ns) x1 res (Regs x Sp) ns' ("rp" :: ns ++ ns') (res - length ns')) in H1.
  assert (ok_in ("rp" :: ns) res ns' ("rp" :: ns ++ ns') (res - length ns')).
  red; intuition.
  change (LvMem (Sp + 0)%loc) with (LvMem (Sp + variablePosition ("rp" :: ns ++ ns') "rp")%loc) in H7.
  assert (In "rp" ("rp" :: ns ++ ns')) by intuition.
  evaluate auto_ext.
  generalize dependent x2.
  rewrite <- H10.
  erewrite H4.
  intros.
  descend.
  apply subst_qspecOut_bwd.
  eapply qspecOut_bwd.
  post.
  step auto_ext.
  intros.
  match goal with
    | [ |- himp _ ?P ?Q ] =>
      match P with
        | context[pre ?X _] =>
          match Q with
            | context[pre ?Y _] => equate X Y
          end
      end
  end.
  step auto_ext.
  descend.
  clear H8.
  eauto.
  clear H8.
  step auto_ext.
  descend.
  Focus 2.
  intuition subst.
  unfold sel at 1 3.
  rewrite sel_upd_ne.
  specialize (@merge_agree x1 x4 ("rp" :: ns)).
  unfold agree_on; intro Hag.
  rewrite (proj1 (Forall_forall _ _) Hag _ (or_intror _ H11)); auto.
  inversion H3; subst.
  intro; subst.
  apply H14.
  apply in_or_app; tauto.

  step auto_ext.
  erewrite H5.
  instantiate (2 := sel x1).
  generalize dependent x2.
  rewrite H10; intros.
  eapply Imply_trans; [ apply subst_qspecOut_fwd' | ].
  eapply Imply_trans; [ | apply subst_qspecOut_bwd' ].
  eapply Imply_trans; [ apply qspecOut_fwd' | ].
  simpl.
  apply existsL; simpl; intros.
  post.
  eapply Imply_trans; [ | apply qspecOut_bwd' ].
  descend; step auto_ext.
  change ("rp" :: ns ++ ns') with (("rp" :: ns) ++ ns').
  rewrite H1.
  apply prelude_out; auto.
  intros; unfold sel at 1 3.
  rewrite sel_upd_ne.
  specialize (@merge_agree x1 x4 ("rp" :: ns)).
  unfold agree_on; intro Hag.
  rewrite (proj1 (Forall_forall _ _) Hag _ (or_intror _ H12)); auto.
  inversion H3; subst.
  intro; subst.
  apply H15.
  apply in_or_app; tauto.
Qed.

Theorem localsInvariant_inEx : forall specs A p q p',
  (forall x, interp specs (Ex st' : state,
      p st' x
      /\ q st')%PropX
    -> interp specs (p' x))
  -> interp specs (Ex st' : state,
    (Ex x : A, p st' x)
    /\ q st')%PropX
  -> interp (pc := W) (state := settings * state) specs (Ex x : A, p' x).
  propxFo.
  exists x0.
  apply simplify_fwd.
  apply H.
  propxFo; eauto.
Qed.

Lemma word_le : forall sz (u v : word sz),
  u = v \/ u < v
  -> u <= v.
  intuition subst; nomega.
Qed.

Hint Resolve word_le.

Hint Rewrite wordToNat_natToWord_idempotent using reflexivity : sepFormula.
