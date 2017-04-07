Require Import
        Fiat.Computation
        Fiat.Common.DecideableEnsembles
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Notations.

Set Implicit Arguments.

Definition compose E B
           (transformer : Transformer B)
           (encode1 : E -> Comp (B * E))
           (encode2 : E -> Comp (B * E)) :=
  (fun e0 =>
    `(p, e1) <- encode1 e0;
    `(q, e2) <- encode2 e1;
    ret (transform p q, e2))%comp.

Notation "x 'ThenC' y" := (compose _ x y) : binencoders_scope .
Notation "x 'DoneC'"   := (x ThenC fun e => ret (transform_id, e)) : binencoders_scope.

Lemma refineEquiv_compose_compose E B
           (transformer : Transformer B)
           (encode1 encode2 encode3 : E -> Comp (B * E))
  : forall ctx,
    refineEquiv (compose _ (compose _ encode1 encode2) encode3 ctx)
                (compose _ encode1 (compose _ encode2 encode3) ctx).
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
  rewrite transform_assoc; reflexivity.
Qed.

Lemma refineEquiv_compose_Done E B
           (transformer : Transformer B)
           (encode2 : E -> Comp (B * E))
  : forall ctx,
    refineEquiv (compose _ (fun ctx => ret (transform_id, ctx)) encode2 ctx)
                  (encode2 ctx).
Proof.
  unfold compose; simpl; intros.
  rewrite refineEquiv_bind2_unit; simpl.
  split; unfold Bind2; intros v Comp_v.
  - computes_to_econstructor; eauto; destruct v; simpl;
      rewrite transform_id_left; eauto.
  - computes_to_inv; subst; destruct v0;
    rewrite transform_id_left; eauto.
Qed.

Lemma refineEquiv_under_compose E B
           (transformer : Transformer B)
           (encode1 encode2 encode2' : E -> Comp (B * E))
  : (forall ctx', refineEquiv (encode2 ctx') (encode2' ctx'))
    -> forall ctx,
      refineEquiv (compose _ encode1 encode2 ctx)
                  (compose _ encode1 encode2' ctx).
Proof.
  unfold compose; intros.
  eapply refineEquiv_bind; [ reflexivity | ].
  intro ab; destruct ab; simpl.
  eapply refineEquiv_bind; [ apply H | reflexivity ].
Qed.

Lemma compose_encode_correct
      {A A' B}
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (transformer : Transformer B)
      (project : A -> A')
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (predicate_rest' : A -> B -> Prop)
      (predicate_rest : A' -> B -> Prop)
      (encode1 : A' -> CacheEncode -> Comp (B * CacheEncode))
      (encode2 : A -> CacheEncode -> Comp (B * CacheEncode))
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> encode_decode_correct_f
              cache transformer predicate'
              predicate_rest
              encode1 decode1 P)
      (pred_pf : forall data, predicate data -> predicate' (project data))
      (predicate_rest_impl :
         forall a' b
                a ce ce' ce'' b' b'',
           computes_to (encode1 a' ce) (b', ce')
           -> project a = a'
           -> predicate a
           -> computes_to (encode2 a ce') (b'', ce'')
           -> predicate_rest' a b
          -> predicate_rest a' (transform b'' b))
      (decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
      (decode2_pf : forall proj,
          predicate' proj ->
          cache_inv_Property P P_inv2 ->
          encode_decode_correct_f cache transformer
            (fun data => predicate data /\ project data = proj)
            predicate_rest'
            encode2
            (decode2 proj) P)
  : encode_decode_correct_f
      cache transformer
      (fun a => predicate a)
      predicate_rest'
      (fun (data : A) (ctx : CacheEncode) =>
         compose _ (encode1 (project data)) (encode2 data)  ctx
      )%comp
     (fun (bin : B) (env : CacheDecode) =>
        `(proj, rest, env') <- decode1 bin env;
          decode2 proj rest env') P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold compose, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (transform b0 ext) env_OK env_pm (pred_pf _ pred_pm) H' com_pf); intuition; simpl in *; injections; eauto.
    setoid_rewrite <- transform_assoc; rewrite H2.
    simpl.
    destruct (fun H'' => proj1 (decode2_pf (project data) (pred_pf _ pred_pm) H1)
                               _ _ _ _ _ ext H4 H (conj pred_pm (eq_refl _)) H'' com_pf');
      intuition; simpl in *; injections.
    eauto. }
  { intros.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto.
      destruct Heqo as [? [? [? [? [? [? ?] ] ] ] ] ].
    eapply (proj2 (decode2_pf a H5 (proj2 P_inv_pf))) in H2; eauto.
    destruct H2 as [? ?]; destruct_ex; intuition; subst.
    eexists; eexists; repeat split.
    repeat computes_to_econstructor; eauto.
    simpl; rewrite transform_assoc; reflexivity.
    eassumption.
    eassumption.
  }
Qed.

(* For decoding fixed fields that do no depend on the object *)
(* being encoded, e.g. version numbers in an IP packet. This *)
(* allows us to avoid polluting the data invariant with  *)
(* extraneous clauses. *)

(* SUGGESTION: If we're using a deterministic encoder, we *)
(* could compare the binary values of the field instead of *)
(* decoding and comparing. *)

Lemma compose_encode_correct_no_dep
      {A A' B}
      (* Need decideable equality on the type of the fixed field. *)
      (A'_eq_dec : Query_eq A')
      {cache : Cache}
      {P  : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (transformer : Transformer B)
      (a' : A')
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (predicate_rest' : A -> B -> Prop)
      (predicate_rest : A' -> B -> Prop)
      (encode1 : A' -> CacheEncode -> Comp (B * CacheEncode))
      (encode2 : A -> CacheEncode -> Comp (B * CacheEncode))
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> encode_decode_correct_f cache transformer predicate' predicate_rest
                                    encode1 decode1 P)
      (predicate_a' : predicate' a')
      (predicate_rest_impl :
         forall a' b
                a ce ce' ce'' b' b'',
           computes_to (encode1 a' ce) (b', ce')
           -> predicate a
           -> computes_to (encode2 a ce') (b'', ce'')
           -> predicate_rest' a b
           -> predicate_rest a' (transform b'' b))
      (decode2 : B -> CacheDecode -> option (A * B * CacheDecode))
      (decode2_pf :
         predicate' a' ->
          cache_inv_Property P P_inv2 ->
          encode_decode_correct_f cache transformer
                                  (fun data => predicate data)
                                  predicate_rest'
            encode2
            decode2 P)
  : encode_decode_correct_f
      cache transformer
      (fun a => predicate a)
      predicate_rest'
      (fun (data : A) (ctx : CacheEncode) =>
         compose _ (encode1 a') (encode2 data)  ctx
      )%comp
     (fun (bin : B) (env : CacheDecode) =>
        `(a, rest, env') <- decode1 bin env;
          (if A_eq_dec a a' then decode2 rest env' else None)) P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold compose, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    destruct (fun H => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (transform b0 ext) env_OK env_pm predicate_a' H com_pf); intuition; simpl in *; injections.
    eapply predicate_rest_impl; eauto.
    setoid_rewrite <- transform_assoc; rewrite H2.
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
    simpl; rewrite transform_assoc; reflexivity.
    eassumption.
    eassumption.
  }
Qed.

Lemma encode_decode_correct_finish {A B}
  : forall (cache : Cache)
           (transformer : Transformer B)
           (predicate : A -> Prop)
           (rest_predicate : A -> B -> Prop)
           (decode_inv : CacheDecode -> Prop)
           (a : A)
           (b : bool),
    (forall a', predicate a' -> a' = a)
    -> decides b (predicate a)
    -> encode_decode_correct_f
         cache
         transformer
         predicate
         rest_predicate
         (fun a' ctxE => ret (transform_id, ctxE))
         (fun b' ctxD => if b then Some (a, b', ctxD) else None)
         decode_inv.
Proof.
  unfold encode_decode_correct_f; split; intros.
  - eexists env'; pose proof (H _ H2); subst; find_if_inside;
      simpl in *; intuition eauto; computes_to_inv; injections.
    rewrite transform_id_left; eauto.
    eassumption.
  - find_if_inside; injections; try discriminate;
      simpl in *; intuition eauto.
    eexists; eexists; intuition eauto.
    rewrite transform_id_left; reflexivity.
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
