Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Compose.

Definition composeIf E B
           (monoid : Monoid B)
           (iComp : Comp bool)
           (formatT : E -> Comp (B * E))
           (formatE : E -> Comp (B * E))
           (e : E)
  := b <- iComp;
       If b Then formatT e
          Else formatE e.

Notation "'Either' t 'Or' e " :=
  (composeIf _ _ _ { _ : bool | True} t e) : format_scope.

Lemma composeIf_format_correct
      {A B}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_invT P_invE : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_invT P /\ P_invE P))
      (monoid : Monoid B)
      (predicate : A -> Prop)
      (predicate_rest : A -> B -> Prop)
      (ICompb : B -> bool)
      (formatT : A -> CacheFormat -> Comp (B * CacheFormat))
      (decodeT : B -> CacheDecode -> option (A * B * CacheDecode))
      (formatE : A -> CacheFormat -> Comp (B * CacheFormat))
      (decodeE : B -> CacheDecode -> option (A * B * CacheDecode))
      (decodeT_pf :
         cache_inv_Property P P_invT
         -> CorrectDecoder
              monoid predicate predicate_rest
              formatT decodeT P)
      (decodeE_pf :
         cache_inv_Property P P_invE
         -> CorrectDecoder
              monoid predicate predicate_rest
              formatE decodeE P)
      (ICompb_OKT : forall data bin env xenv ext,
          predicate data
          -> formatT data env ↝ (bin, xenv)
          -> ICompb (mappend bin ext) = true)
      (ICompb_OKE : forall data bin env xenv ext,
          predicate data
          -> formatE data env ↝ (bin, xenv)
          -> ICompb (mappend bin ext) = false)
  : CorrectDecoder
      monoid
      (fun a => predicate a)
      predicate_rest
      (fun (data : A) =>
         composeIf _ _ _ {b : bool | True }
                   (formatT data)
                   (formatE data)
      )%comp
      (fun (b : B) (env : CacheDecode) =>
         If ICompb b Then
            decodeT b env
            Else
            decodeE b env
      ) P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold composeIf, Bind2 in com_pf; computes_to_inv; destruct v;
      simpl in com_pf'; computes_to_inv.
    - erewrite ICompb_OKT; eauto.
      simpl; eapply decodeT_pf; intuition eauto.
    - erewrite ICompb_OKE; eauto.
      simpl; eapply decodeE_pf; intuition eauto.
  }
  { intros.
    destruct (ICompb bin) eqn : IComp_v ; simpl in *.
    - eapply decodeT_pf in H1; intuition eauto.
      destruct_ex; intuition; eexists; eexists;
        unfold composeIf; intuition eauto.
      refine pick val true; eauto.
    - eapply decodeE_pf in H1; intuition eauto.
      destruct_ex; intuition; eexists; eexists;
        unfold composeIf; intuition eauto.
      refine pick val false; eauto. }
Qed.

Definition composeIf' E B
           (monoid : Monoid B)
           (format1 : E -> Comp (B * E))
           (format2 : E -> Comp (B * E))
           (iComp : Comp bool)
           (formatT : E -> Comp (B * E))
           (formatE : E -> Comp (B * E))
  :=
    (fun e0 =>
         b <- iComp;
           If b Then
              `(p, e1) <- format1 e0;
            `(q, e2) <- formatT e1;
            ret (mappend p q, e2)
                Else (`(p, e1) <- format2 e0;
                      `(q, e2) <- formatE e1;
                      ret (mappend p q, e2))
    )%comp.

Lemma composeIf'_format_correct
      {A A' B}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_inv1 P_invT P_invE : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_invT P /\ P_invE P))
      (monoid : Monoid B)
      (projectT : A -> A')
      (projectE : A -> A')
      (predicate : A -> Prop)
      (predicate_rest : A' -> B -> Prop)
      (predicate_rest' : A -> B -> Prop)
      (predicate' : A' -> Prop)
      (format1 : A' -> CacheFormat -> Comp (B * CacheFormat))
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (ICompb : A' -> bool)
      (formatT : A -> CacheFormat -> Comp (B * CacheFormat))
      (decodeT : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
      (formatE : A -> CacheFormat -> Comp (B * CacheFormat))
      (decodeE : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> CorrectDecoder
              monoid predicate' predicate_rest
              format1 decode1 P)
      (decodeT_pf : forall proj,
          ICompb proj = true ->
          predicate' proj ->
          cache_inv_Property P P_invT ->
          CorrectDecoder
            monoid
            (fun data => predicate data /\ projectT data = proj)
            predicate_rest'
            formatT
            (decodeT proj) P)
      (decodeE_pf : forall proj,
          ICompb proj = false ->
          predicate' proj ->
          cache_inv_Property P P_invE ->
          CorrectDecoder
            monoid
            (fun data => predicate data /\ projectE data = proj)
            predicate_rest'
            formatE
            (decodeE proj) P)
      (predicate_rest_implT : forall a' b b'',
          (ICompb a' = true /\
           exists a ce ce' ce'' b' b'',
             computes_to (format1 a' ce) (b', ce')
             /\ projectT a = a'
             /\ predicate a
             /\ computes_to (formatT a ce') (b'', ce'')
             /\ predicate_rest' a b)
          -> predicate_rest a' (mappend b'' b))
      (predicate_rest_implE : forall a' b b'',
          (ICompb a' = false /\
           exists a ce ce' ce'' b',
             computes_to (format1 a' ce) (b', ce')
             /\ projectE a = a'
             /\ predicate a
             /\ computes_to (formatE a ce') (b'', ce'')
             /\ predicate_rest' a b)
          -> predicate_rest a' (mappend b'' b))
      (pred_pf : forall data, predicate data -> predicate' (projectT data))
      (pred_pf' : forall data, predicate data -> predicate' (projectE data))
      (ICombT_OK : forall data, ICompb (projectT data) = true)
      (ICombE_OK : forall data, ICompb (projectE data) = false)
  : CorrectDecoder
      monoid
      (fun a => predicate a)
      predicate_rest'
      (fun (data : A) (ctx : CacheFormat) =>
         composeIf' _ _ _ (format1 (projectT data))
                   (format1 (projectE data)) {b : bool | True } (formatT data) (formatE data)  ctx
      )%comp
      (fun (bin : B) (env : CacheDecode) =>
         `(proj, rest, env') <- decode1 bin env;
           If ICompb proj Then
              decodeT proj rest env'
              Else
              decodeE proj rest env'
      ) P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold composeIf', Bind2 in com_pf; computes_to_inv; destruct v;
      simpl in com_pf'; computes_to_inv; destruct v; destruct v0;
        simpl in com_pf'', com_pf'''.
    - injections.
      destruct (fun H => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend b0 ext) env_OK env_pm (pred_pf _ pred_pm) H com_pf'); intuition; simpl in *; injections.
      eapply predicate_rest_implT; repeat eexists; intuition eauto.
      destruct (fun H' => proj1 (decodeT_pf (projectT data) (ICombT_OK data) (pred_pf _ pred_pm)
                                            H)
                                _ _ _ _ _ ext H5 H1 (conj pred_pm (eq_refl _)) H' com_pf'');
        intuition; simpl in *; injections.
      setoid_rewrite <- mappend_assoc; rewrite H2.
      intuition; simpl in *; injections.
      rewrite ICombT_OK, H7; simpl; eauto.
    - injections.
      destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend b0 ext) env_OK env_pm (pred_pf' _ pred_pm) H' com_pf'); intuition; simpl in *; injections.
      eapply predicate_rest_implE; intuition; repeat eexists; intuition eauto.
      destruct (fun H' => proj1 (decodeE_pf (projectE data) (ICombE_OK data) (pred_pf' _ pred_pm)
                                            H4)
                                _ _ _ _ _ ext H5 H1 (conj pred_pm (eq_refl _)) H' com_pf'');
        intuition; simpl in *; injections.
      setoid_rewrite <- mappend_assoc; rewrite H2.
      intuition; simpl in *; injections.
      rewrite ICombE_OK, H7; simpl; eauto.
  }
  { intros.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    destruct (ICompb a) eqn: ?; simpl in *.
    - eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto;
        destruct Heqo; destruct_ex; intuition;
          eapply (proj2 (decodeT_pf a Heqb0 H7 H3)) in H1; eauto;
            destruct H1; destruct_ex; intuition; subst.
      eexists; eexists; repeat split.
      unfold composeIf'; refine pick val true.
      repeat computes_to_econstructor; eauto.
      eauto.
      simpl; rewrite mappend_assoc; reflexivity.
      eassumption.
      eassumption.
    - eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto;
        destruct Heqo; destruct_ex; intuition;
          eapply (proj2 (decodeE_pf a Heqb0 H7 H8)) in H1; eauto;
            destruct H1; destruct_ex; intuition; subst.
      eexists; eexists; repeat split.
      unfold composeIf'; refine pick val false.
      repeat computes_to_econstructor; eauto.
      eauto.
      simpl; repeat computes_to_econstructor; eauto.
      simpl; rewrite mappend_assoc; reflexivity.
      eassumption.
      eassumption.
  }
Qed.
