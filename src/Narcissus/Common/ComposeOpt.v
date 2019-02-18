Require Import
        Fiat.Computation
        Fiat.Common.DecideableEnsembles
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Notations.

Set Implicit Arguments.

Definition compose E B
           (monoid : Monoid B)
           (format1 : E -> Comp (B * E))
           (format2 : E -> Comp (B * E)) :=
  (fun e0 =>
     `(p, e1) <- format1 e0;
     `(q, e2) <- format2 e1;
       ret (mappend p q, e2))%comp.

Notation "x 'ThenC' y" := (compose _ x y) : format_scope .
Notation "x 'DoneC'"   := (x ThenC fun e => ret (mempty, e)) : format_scope.

Lemma refineEquiv_compose_compose E B
      (monoid : Monoid B)
      (format1 format2 format3 : E -> Comp (B * E))
  : forall ctx,
    refineEquiv (compose _ (compose _ format1 format2) format3 ctx)
                (compose _ format1 (compose _ format2 format3) ctx).
Proof.
  unfold compose; intros.
  rewrite refineEquiv_bind2_bind.
  eapply refineEquiv_bind; [ reflexivity | ].
  intro; rewrite refineEquiv_bind2_bind.
  symmetry; rewrite refineEquiv_bind2_bind.
  eapply refineEquiv_bind; [ reflexivity | ].
  intro; rewrite refineEquiv_bind2_bind.
  rewrite refineEquiv_bind2_unit.
  eapply refineEquiv_bind; [ reflexivity | ].
  intro; rewrite refineEquiv_bind2_unit; simpl.
  rewrite mappend_assoc; reflexivity.
Qed.

Lemma refineEquiv_compose_Done E B
      (monoid : Monoid B)
      (format2 : E -> Comp (B * E))
  : forall ctx,
    refineEquiv (compose _ (fun ctx => ret (mempty, ctx)) format2 ctx)
                (format2 ctx).
Proof.
  unfold compose; simpl; intros.
  rewrite refineEquiv_bind2_unit; simpl.
  split; unfold Bind2; intros v Comp_v.
  - computes_to_econstructor; eauto; destruct v; simpl;
      rewrite mempty_left; eauto.
  - computes_to_inv; subst; destruct v0;
      rewrite mempty_left; eauto.
Qed.

Lemma refineEquiv_under_compose E B
      (monoid : Monoid B)
      (format1 format2 format2' : E -> Comp (B * E))
  : (forall ctx', refineEquiv (format2 ctx') (format2' ctx'))
    -> forall ctx,
      refineEquiv (compose _ format1 format2 ctx)
                  (compose _ format1 format2' ctx).
Proof.
  unfold compose; intros.
  eapply refineEquiv_bind; [ reflexivity | ].
  intro ab; destruct ab; simpl.
  eapply refineEquiv_bind; [ apply H | reflexivity ].
Qed.

Lemma Compose_decode_correct
      {A A' C B}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid B)
      (proj' : A -> A')
      (proj : A -> C)
      (predicate : A -> Prop)
      (consistency_predicate : A' -> A -> Prop)
      (predicate' : A -> Prop)
      (format1 : A -> CacheFormat -> Comp (B * CacheFormat))
      (format2 : A -> CacheFormat -> Comp (B * CacheFormat))
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (consistency_predicate_OK :
         forall (data : A) (a' : A'),
           consistency_predicate a' data ->
           forall data' b env xenv,
             computes_to (format1 data' env) (b, xenv)
             -> consistency_predicate a' data'
             -> computes_to (format1 data env) (b, xenv))
      (consistency_predicate_refl :
         forall a, consistency_predicate (proj' a) a)
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> CorrectDecoder
              monoid predicate'
              proj'
              format1 decode1 P)
      (pred_pf : forall data, predicate data -> predicate' data)
      (decode2 : A' -> B -> CacheDecode -> option (C * B * CacheDecode))
      (decode2_pf : forall a' : A',
          cache_inv_Property P P_inv2 ->
          CorrectDecoder monoid
                         (fun data => predicate data
                                      /\ consistency_predicate a' data)
                         proj
                         format2
                         (decode2 a') P)
  : CorrectDecoder
      monoid
      (fun a => predicate a)
      proj
      (fun (data : A) (ctx : CacheFormat) =>
         compose _ (format1 data) (format2 data)  ctx
      )%comp
      (fun (bin : B) (env : CacheDecode) =>
         `(proj, rest, env') <- decode1 bin env;
           decode2 proj rest env') P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm com_pf.
    unfold compose, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    destruct (proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend b0 ext) env_OK env_pm (pred_pf _ pred_pm) com_pf); intuition; simpl in *; injections; eauto.
    setoid_rewrite <- mappend_assoc; rewrite H2.
    simpl.
    destruct (proj1 (decode2_pf (proj' data) H1)
                    _ _ _ _ _ ext H4 H (conj pred_pm (consistency_predicate_refl _)) com_pf');
      intuition; simpl in *; injections.
    eauto. }
  { intros.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    generalize Heqo; intros Heqo'.
    eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto.
    destruct Heqo as [? [? [? [? [? [? [? [? ?] ] ] ] ] ] ] ].
    eapply (proj2 (decode2_pf a (proj2 P_inv_pf))) in H2; eauto.
    destruct H2 as [? ?]; destruct_ex; split_and; subst.
    setoid_rewrite mappend_assoc.
    split; eauto.
    eexists x2, _, _; repeat split; eauto.
    repeat computes_to_econstructor; simpl; eauto.
  }
Qed.

Lemma compose_format_correct
      {A A' C B}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid B)
      (project : A -> A')
      (project2 : A -> C)
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (format1 : A' -> CacheFormat -> Comp (B * CacheFormat))
      (format2 : A -> CacheFormat -> Comp (B * CacheFormat))
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> CorrectDecoder
              monoid predicate'
              id
              format1 decode1 P)
      (pred_pf : forall data, predicate data -> predicate' (project data))
      (decode2 : A' -> B -> CacheDecode -> option (C * B * CacheDecode))
      (decode2_pf : forall proj,
          predicate' proj ->
          cache_inv_Property P P_inv2 ->
          CorrectDecoder monoid
                                  (fun data => predicate data /\ project data = proj)
                                  project2
                                  format2
                                  (decode2 proj) P)
  : CorrectDecoder
      monoid
      (fun a => predicate a)
      project2
      (fun (data : A) (ctx : CacheFormat) =>
         compose _ (format1 (project data)) (format2 data)  ctx
      )%comp
      (fun (bin : B) (env : CacheDecode) =>
         `(proj, rest, env') <- decode1 bin env;
           decode2 proj rest env') P.
Proof.
  eapply Compose_decode_correct with
      (consistency_predicate := fun proj data => project data = proj)
      (proj' := project);
    try eassumption; eauto.
  - intros; congruence.
  - intros.
    revert decode1_pf; clear.

(* For decoding fixed fields that do no depend on the object *)
(* being formatd, e.g. version numbers in an IP packet. This *)
(* allows us to avoid polluting the data invariant with  *)
(* extraneous clauses. *)

(* SUGGESTION: If we're using a deterministic formatr, we *)
(* could compare the binary values of the field instead of *)
(* decoding and comparing. *)

Lemma compose_format_correct_no_dep
      {A C B}
      (* Need decideable equality on the type of the fixed field. *)
      (C_eq_dec : Query_eq C)
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid B)
      (a' : C)
      (predicate : A -> Prop)
      (predicate' : C -> Prop)
      (predicate_rest' : A -> B -> Prop)
      (predicate_rest : C -> B -> Prop)
      (format1 : C -> CacheFormat -> Comp (B * CacheFormat))
      (format2 : A -> CacheFormat -> Comp (B * CacheFormat))
      (decode1 : B -> CacheDecode -> option (C * B * CacheDecode))
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid predicate' predicate_rest
                                    format1 decode1 P)
      (predicate_a' : predicate' a')
      (predicate_rest_impl :
         forall a' b
                a ce ce' ce'' b' b'',
           computes_to (format1 a' ce) (b', ce')
           -> predicate a
           -> computes_to (format2 a ce') (b'', ce'')
           -> predicate_rest' a b
           -> predicate_rest a' (mappend b'' b))
      (decode2 : B -> CacheDecode -> option (A * B * CacheDecode))
      (decode2_pf :
         predicate' a' ->
         cache_inv_Property P P_inv2 ->
         CorrectDecoder monoid
                                 (fun data => predicate data)
                                 predicate_rest'
                                 format2
                                 decode2 P)
  : CorrectDecoder
      monoid
      (fun a => predicate a)
      predicate_rest'
      (fun (data : A) (ctx : CacheFormat) =>
         compose _ (format1 a') (format2 data)  ctx
      )%comp
      (fun (bin : B) (env : CacheDecode) =>
         `(a, rest, env') <- decode1 bin env;
           (if A_eq_dec a a' then decode2 rest env' else None)) P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold compose, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    destruct (fun H => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend b0 ext) env_OK env_pm predicate_a' H com_pf); intuition; simpl in *; injections.
    eapply predicate_rest_impl; eauto.
    setoid_rewrite <- mappend_assoc; rewrite H2.
    simpl.
    destruct (A_eq_dec a' a'); try congruence.
    subst.
    destruct (fun H => proj1 H6 (*decode2_pf _ (conj (eq_refl _) predicate_a') H1*)
                             _ _ _ _ _ ext H4 H pred_pm pred_pm_rest com_pf');
      intuition; simpl in *; injections.
    eauto. }
  { intros.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate;
        destruct (A_eq_dec a a'); try discriminate;
          eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto;
            destruct Heqo; destruct_ex; intuition; subst;
              eapply (proj2 H11 (*decode2_pf a' (conj (eq_refl _) H7) H5)*)) in H1; eauto;
                destruct H1; destruct_ex; intuition; subst.
    eexists; eexists; repeat split.
    repeat computes_to_econstructor; eauto.
    simpl; rewrite mappend_assoc; reflexivity.
    eassumption.
    eassumption.
  }
Qed.

Lemma CorrectDecoderinish {A B}
  : forall (cache : Cache)
           (monoid : Monoid B)
           (predicate : A -> Prop)
           (rest_predicate : A -> B -> Prop)
           (decode_inv : CacheDecode -> Prop)
           (a : A)
           (b : bool),
    (forall a', predicate a' -> a' = a)
    -> decides b (predicate a)
    -> CorrectDecoder
         monoid
         predicate
         rest_predicate
         (fun a' ctxE => ret (mempty, ctxE))
         (fun b' ctxD => if b then Some (a, b', ctxD) else None)
         decode_inv.
Proof.
  unfold CorrectDecoder; split; intros.
  - eexists env'; pose proof (H _ H2); subst; find_if_inside;
      simpl in *; intuition eauto; computes_to_inv; injections.
    rewrite mempty_left; eauto.
    eassumption.
  - find_if_inside; injections; try discriminate;
      simpl in *; intuition eauto.
    eexists; eexists; intuition eauto.
    rewrite mempty_left; reflexivity.
Qed.

Lemma decides_and :
  forall b b' P Q,
    decides b P
    -> decides b' Q
    -> decides (andb b b') (P /\ Q).
Proof.
  destruct b; destruct b'; simpl in *; intuition.
Qed.

Lemma decides_assumption :
  forall (P : Prop),
    P -> decides true P.
Proof. simpl in *; intuition. Qed.

Lemma decides_eq_refl {A} :
  forall (a : A), decides true (a = a).
Proof. simpl in *; intuition. Qed.

Lemma decides_dec_eq {A} :
  forall (A_eqb : A -> A -> bool)
         (A_eqb_sound : forall a a', a = a' <-> A_eqb a a' = true)
         (a a' : A), decides (A_eqb a a') (a = a').
Proof.
  simpl in *; intros; pose proof (A_eqb_sound a a');
    destruct (A_eqb a a'); simpl; intuition.
Qed.

Lemma decides_dec_lt
  : forall n n', decides (if (Compare_dec.lt_dec n n') then true else false) (lt n n').
Proof.
  intros; find_if_inside; simpl; eauto.
Qed.

Lemma refine_If_Then_Else_ThenC
  : forall (E B : Type) (monoid : Monoid B) (format1 format2 format3 : E -> Comp (B * E)) (ctx : E) b,
    refine (((If b Then format1 Else format2) ThenC format3) ctx)
           (If b Then ((format1 ThenC format3) ctx) Else ((format2 ThenC format3) ctx)).
Proof.
  intros; destruct b; reflexivity.
Qed.

Lemma refineEquiv_If_Then_Else_ThenC
  : forall (E B : Type) (monoid : Monoid B) (format1 format2 format3 : E -> Comp (B * E)) (ctx : E) b,
    refineEquiv (((If b Then format1 Else format2) ThenC format3) ctx)
                (If b Then ((format1 ThenC format3) ctx) Else ((format2 ThenC format3) ctx)).
Proof.
  intros; destruct b; reflexivity.
Qed.
