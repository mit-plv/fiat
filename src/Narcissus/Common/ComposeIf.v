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
         -> CorrectDecoder
              monoid
              Source_Predicate
              (fun bs => True)
              (fun s bs => True)
              (composeIf formatT formatE)
              decodeB P
              (fun bs env t => (forall s, (formatT s env t -> bs = true)
                                          /\ (formatE s env t -> bs = false))))
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
    eapply decodeB_pf with (ext := ext) in com_pf; intuition eauto.
    destruct_ex; split_and.
    rewrite unfold_computes in H7.
    unfold composeIf, Union_Format, Bind2 in com_pf0.
    rewrite unfold_computes in com_pf0; destruct_ex.
    specialize (H7 data); split_and.
    rewrite H6.
    revert H9; pattern x1; apply IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv; simpl.
    constructor; intros; [ | constructor; eauto].
    - generalize (H11 H9); intros; subst.
      eapply H0 in H9.
      destruct_ex; split_and.
      rewrite H9; eexists _, _; intuition eauto.
      unfold composeIf, Union_Format; apply unfold_computes;
        exists Fin.F1; simpl; eauto.
      eauto.
      eauto.
      eauto.
    - intros; generalize (H12 H9); intros; subst.
      eapply H3 in H9.
      destruct_ex; split_and.
      rewrite H9; eexists _, _; intuition eauto.
      unfold composeIf, Union_Format; apply unfold_computes;
        exists (Fin.FS Fin.F1); simpl; eauto.
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
