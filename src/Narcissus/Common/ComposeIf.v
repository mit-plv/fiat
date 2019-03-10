Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.BaseFormats.

Definition composeIf {S T}
           {cache : Cache}
           {monoid : Monoid T}
           (formatT : FormatM S T)
           (formatE : FormatM S T)
  := Union_Format (Vector.cons _ formatT _ (Vector.cons _ formatE _ (Vector.nil _))).

Notation "'Either' t 'Or' e " :=
  (composeIf t e) : format_scope.

Lemma composeIf_format_correct
      {S V T}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_invT P_invE : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_invT P /\ P_invE P))
      (monoid : Monoid T)
      (Source_Predicate : S -> Prop)
      (View_Predicate : V -> Prop)
      (view : S -> V -> Prop)
      (ICompb : T -> bool)
      (formatT formatE : FormatM S T)
      (decodeT decodeE : DecodeM (V * T) T)
      (view_formatT view_formatE : FormatM V T)
      (decodeT_pf :
         cache_inv_Property P P_invT
         -> CorrectDecoder
              monoid
              Source_Predicate
              View_Predicate
              view
              formatT decodeT P
              view_formatT)
      (decodeE_pf :
         cache_inv_Property P P_invE
         -> CorrectDecoder
              monoid Source_Predicate
              View_Predicate
              view
              formatE decodeE P
              view_formatE)
      (ICompb_OKT : forall data bin env xenv ext,
          Source_Predicate data
          -> formatT data env ↝ (bin, xenv)
          -> ICompb (mappend bin ext) = true)
      (ICompb_OKE : forall data bin env xenv ext,
          Source_Predicate data
          -> formatE data env ↝ (bin, xenv)
          -> ICompb (mappend bin ext) = false)
  : CorrectDecoder
      monoid
      Source_Predicate
      View_Predicate
      view
      (composeIf formatT formatE)
      (fun (b : T) (env : CacheDecode) =>
         If ICompb b Then
            decodeT b env
            Else
            decodeE b env
      ) P
      (composeIf view_formatT view_formatE).
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm com_pf.
    unfold composeIf, Union_Format, Bind2 in com_pf.
      rewrite unfold_computes in com_pf; destruct_ex.
      revert H; pattern x; apply IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv; simpl.
      constructor; intros; [ | constructor; eauto].
    - erewrite ICompb_OKT; eauto.
      eapply (decodeT_pf (proj1 P_inv_pf)) with (ext := ext) in H; eauto.
      destruct_ex; split_and.
      simpl; eexists _, _; intuition eauto.
      unfold composeIf, Union_Format.
      apply unfold_computes; eexists Fin.F1; simpl; eauto.
    - intros; erewrite ICompb_OKE; eauto.
      eapply (decodeE_pf (proj2 P_inv_pf)) with (ext := ext) in H; eauto.
      destruct_ex; split_and.
      simpl; eexists _, _; intuition eauto.
      unfold composeIf, Union_Format.
      apply unfold_computes; eexists (Fin.FS Fin.F1); simpl; eauto.
  }
  { intros.
    destruct (ICompb t) eqn : IComp_v ; simpl in *.
    - eapply decodeT_pf in H1; intuition eauto.
      destruct_ex; intuition; eexists _, _;
        unfold composeIf; intuition eauto.
      unfold Union_Format; apply unfold_computes; eexists (Fin.F1); simpl; eauto.
    - eapply decodeE_pf in H1; intuition eauto.
      destruct_ex; intuition; eexists _, _;
        unfold composeIf; intuition eauto.
      unfold Union_Format; apply unfold_computes; eexists (Fin.FS Fin.F1); simpl; eauto.
  }
Qed.

Lemma composeIf_format_correct'
      {S V T}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_invT P_invE P_invS: (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_invT P /\ P_invE P /\ P_invS P))
      (monoid : Monoid T)
      (Source_Predicate : S -> Prop)
      (View_Predicate : V -> Prop)
      (view : S -> V -> Prop)
      (formatT formatE : FormatM S T)
      (subformat : FormatM S T)
      (decodeT decodeE : DecodeM (V * T) T)
      (decodeB : DecodeM (bool * T) T)
      (view_formatT view_formatE : FormatM V T)
      (decodeT_pf :
         cache_inv_Property P P_invT
         -> CorrectDecoder
              monoid
              Source_Predicate
              View_Predicate
              view
              formatT decodeT P
              view_formatT)
      (decodeE_pf :
         cache_inv_Property P P_invE
         -> CorrectDecoder
              monoid Source_Predicate
              View_Predicate
              view
              formatE decodeE P
              view_formatE)
      (decodeB_pf :
         cache_inv_Property P P_invS
         -> CorrectRefinedDecoder
              monoid
              Source_Predicate
              (fun bs => True)
              (fun s bs => True)
              (composeIf formatT formatE)
              subformat
              decodeB P
              (fun bs env t => (forall s t' env', Source_Predicate s ->
                                          (formatT s env (mappend (fst t) t', env') -> bs = true)
                                          /\ (formatE s env (mappend (fst t) t', env') -> bs = false)))
           /\ Prefix_Format _ (composeIf formatT formatE) subformat)
  : CorrectDecoder
      monoid
      Source_Predicate
      View_Predicate
      view
      (composeIf formatT formatE)
      (fun (t : T) (env : CacheDecode) =>
         `(b, _, _) <- decodeB t env;
           If b Then decodeT t env
              Else decodeE t env
      ) P
      (composeIf view_formatT view_formatE).
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm com_pf.
    generalize com_pf; intro.
    subst.
    unfold composeIf, Union_Format, Bind2 in com_pf0.
    rewrite unfold_computes in com_pf0; destruct_ex.
    revert H; pattern x; apply IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv; simpl.
    constructor; intros; [ | constructor; eauto].
    -  eapply (proj2 (decodeB_pf (proj2 (proj2 P_inv_pf)))) in com_pf; eauto;
         destruct_ex; split_and; intros.
       subst.
       eapply H0 in H2; eauto.
       destruct_ex; split_and.
       rewrite <- mappend_assoc.
       rewrite H2; simpl.
       rewrite unfold_computes in H5.
       rewrite (proj1 (proj1 H5 _ _ _ pred_pm) H); simpl.
       eapply decodeT_pf in H;
         destruct_ex; split_and.
       rewrite mappend_assoc.
       rewrite H9; eexists _, _; intuition eauto.
       unfold composeIf, Union_Format; apply unfold_computes;
         exists Fin.F1; simpl; eauto.
      eauto.
      eauto.
      eauto.
      eauto.
    - eapply (proj2 (decodeB_pf (proj2 (proj2 P_inv_pf)))) in com_pf; eauto;
         destruct_ex; split_and; intros.
       subst.
       eapply H in H1; eauto.
       destruct_ex; split_and.
       rewrite <- mappend_assoc.
       rewrite H1; simpl.
       rewrite unfold_computes in H7.
       rewrite (proj2 (proj1 H7 _ _ _ pred_pm) H4); simpl.
       eapply decodeE_pf in H4; destruct_ex; split_and.
       rewrite mappend_assoc.
       rewrite H9; eexists _, _; intuition eauto.
       unfold composeIf, Union_Format; apply unfold_computes;
         exists (Fin.FS Fin.F1); simpl; eauto.
      eauto.
      eauto.
      eauto.
      eauto.
  }
  { intros.
    destruct (decodeB t env') as [ [ [? ?] ? ] | ] eqn: ? ;
      simpl in *; try discriminate.
    destruct b; simpl in *.
    - eapply decodeT_pf in H1.
      split_and; destruct_ex; intuition eauto; subst.
      eexists _, _; intuition eauto.
      unfold composeIf, Union_Format; apply unfold_computes;
        exists Fin.F1; simpl; eauto.
      intuition.
      eauto.
      intuition.
    - eapply decodeE_pf in H1.
      split_and; destruct_ex; intuition eauto; subst.
      eexists _, _; intuition eauto.
      unfold composeIf, Union_Format; apply unfold_computes;
        exists (Fin.FS Fin.F1); simpl; eauto.
      intuition.
      eauto.
      intuition.
  }
Qed.

Lemma composeIf_format_inj1
      {S T} {cache : Cache}
      (monoid : Monoid T)
      s env t env'
      (formatT formatE : FormatM S T)
  : formatT s env ∋ (t, env') ->
    composeIf formatT formatE s env ∋ (t, env').
Proof.
  intros. unfold composeIf, Union_Format.
  rewrite unfold_computes.
  exists Fin.F1. eauto.
Qed.

Lemma composeIf_format_inj2
      {S T} {cache : Cache}
      (monoid : Monoid T)
      s env t env'
      (formatT formatE : FormatM S T)
  : formatE s env ∋ (t, env') ->
    composeIf formatT formatE s env ∋ (t, env').
Proof.
  intros. unfold composeIf, Union_Format.
  rewrite unfold_computes.
  exists (Fin.FS Fin.F1). eauto.
Qed.

Lemma composeIf_format_elim
      {S T} {cache : Cache}
      (monoid : Monoid T)
      s env t env'
      (formatT formatE : FormatM S T)
  : composeIf formatT formatE s env ∋ (t, env') ->
    formatT s env ∋ (t, env') \/ formatE s env ∋ (t, env').
Proof.
  unfold composeIf, Union_Format.
  rewrite unfold_computes. intros [? ?].
  revert H. apply (Fin.caseS' x). eauto. clear x.
  intros x. apply (Fin.caseS' x). eauto. clear x.
  intros x. apply Fin.case0; auto.
Qed.

Lemma composeIf_subformat_correct_prefix
      {S T}
      {cache : Cache}
      (monoid : Monoid T)
      (formatT formatE : FormatM S T)
      (subformatT subformatE : FormatM S T)
      (subformat_OK1 : Prefix_Format monoid formatT subformatT)
      (subformat_OK2 : Prefix_Format monoid formatE subformatE)
  : Prefix_Format monoid (composeIf formatT formatE) (composeIf subformatT subformatE).
Proof.
  unfold Prefix_Format in *; intros.
  apply composeIf_format_elim in H. destruct H.
  edestruct subformat_OK1; eauto. destruct_ex.
  eexists _, _, _; intuition eauto. eauto using composeIf_format_inj1.
  edestruct subformat_OK2; eauto. destruct_ex.
  eexists _, _, _; intuition eauto. eauto using composeIf_format_inj2.
Qed.

Lemma composeIf_subformat_correct_low
      {S T}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {monoid : Monoid T}
      {richmonoid : RichMonoidOpt monoid}
      (Source_Predicate : S -> Prop)
      (formatT formatE : FormatM S T)
      (subformat : FormatM S T)
      (decodeB : DecodeM (bool * T) T)
      (decodeB_OK : forall env env' xenv s t ext,
          P env' ->
          Equiv env env' ->
          Source_Predicate s ->
          subformat s env ∋ (t, xenv) ->
          exists v xenv', decodeB (mappend t ext) env' = Some (v, ext, xenv') /\
                   Equiv xenv xenv' /\ P xenv')
      (decodeB_OK' : forall env env' xenv' v t t',
          Equiv env env' ->
          P env' ->
          decodeB t env' = Some (v, t', xenv') ->
          P xenv' /\
          exists t'' xenv,
            (forall s t1 xenv,
                Source_Predicate s ->
                (formatT s env ∋ (mappend t'' t1, xenv) -> v = true) /\
                (formatE s env ∋ (mappend t'' t1, xenv) -> v = false)) /\
            t = mappend t'' t' /\ Equiv xenv xenv')
  : CorrectRefinedDecoder
      monoid
      Source_Predicate
      (fun bs => True)
      (fun s bs => True)
      (composeIf formatT formatE)
      subformat
      decodeB P
      (fun bs env t => (forall s t' env',
                        Source_Predicate s ->
                        (formatT s env (mappend (fst t) t', env') -> bs = true)
                        /\ (formatE s env (mappend (fst t) t', env') -> bs = false))).
Proof.
  split; intros. {
    edestruct decodeB_OK; eauto. destruct_conjs.
    eexists _, _; intuition eauto.
    rewrite unfold_computes; repeat split; simpl; intros;
      rewrite <- unfold_computes in H7;
      edestruct decodeB_OK' with (env:=env); eauto; destruct_conjs;
        apply mappend_inj in H12; subst; eapply H11; eauto.
  } {
    edestruct decodeB_OK' with (env:=env); eauto. destruct_conjs. subst. intuition eauto.
    eexists _, _. rewrite unfold_computes; simpl.
    intuition eauto 1; rewrite <- unfold_computes in H8; eapply H5; eauto.
  }
Qed.

Lemma EquivFormat_ComposeIf {S T}
      {cache : Cache}
      {monoid : Monoid T}
  : forall (format1 format1' format2 format2' : FormatM S T),
    EquivFormat format1 format1'
    -> EquivFormat format2 format2'
    -> EquivFormat (composeIf format1 format2)
                   (composeIf format1' format2').
Proof.
  unfold composeIf, Union_Format; split; intros; intros ? ? ;
    rewrite unfold_computes in H1; destruct_ex; intros;
      rewrite unfold_computes; exists x;
        revert H1; pattern x; apply IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv; simpl;
          repeat (apply IterateBoundedIndex.Build_prim_and; intros); eauto; simpl.
  apply H; apply H1.
  apply H0; apply H1.
  apply H; apply H1.
  apply H0; apply H1.
Qed.

Lemma refineEquiv_ComposeIf {S T}
      {cache : Cache}
      {monoid : Monoid T}
  : forall (format1 format1' format2 format2' : FormatM S T),
    (forall s env, refineEquiv (format1 s env) (format1' s env))
    -> (forall s env, refineEquiv (format2 s env) (format2' s env))
    -> (forall s env,
           refineEquiv (composeIf format1 format2 s env)
                       (composeIf format1' format2' s env)).
Proof.
  intros; eapply EquivFormat_ComposeIf; eauto.
Qed.
