Require Import
        Fiat.Computation
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose.

Set Implicit Arguments.

Definition compose E B
           (transformer : Transformer B)
           (encode1 : E -> Comp (B * E))
           (encode2 : E -> Comp (B * E)) :=
  (fun e0 =>
    `(p, e1) <- encode1 e0;
    `(q, e2) <- encode2 e1;
    ret (transform p q, e2))%comp.

Notation "x 'Then' y" := (compose _ x y) (at level 100, right associativity).
Notation "x 'Done'"   := (x Then fun e => ret (transform_id, e)) (at level 99, right associativity).

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
      (encode1 : A' -> CacheEncode -> Comp (B * CacheEncode))
      (encode2 : A -> CacheEncode -> Comp (B * CacheEncode))
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> encode_decode_correct_f cache transformer predicate' encode1 decode1 P)
      (decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
      (decode2_pf : forall proj,
          predicate' proj ->
          cache_inv_Property P P_inv2 ->
          encode_decode_correct_f cache transformer
            (fun data => predicate data /\ project data = proj)
            encode2
            (decode2 proj) P)
      (pred_pf : forall data, predicate data -> predicate' (project data))
  : encode_decode_correct_f
      cache transformer predicate
      (fun (data : A) (ctx : CacheEncode) =>
         compose _ (encode1 (project data)) (encode2 data)  ctx
      )%comp
     (fun (bin : B) (env : CacheDecode) =>
        `(proj, rest, env') <- decode1 bin env;
          decode2 proj rest env') P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext env_pm pred_pm com_pf.
    unfold compose, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    destruct (proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (transform b0 ext) env_pm (pred_pf _ pred_pm) com_pf); intuition; simpl in *; injections.
    setoid_rewrite <- transform_assoc; rewrite H2.
    simpl.
    destruct (proj1 (decode2_pf (project data) (pred_pf _ pred_pm) H1)
                    _ _ _ _ _ ext H3 (conj pred_pm (eq_refl _)) com_pf');
      intuition; simpl in *; injections.
    eauto. }
  { intros.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto;
      destruct Heqo; destruct_ex; intuition;
        eapply (proj2 (decode2_pf a H7 H5)) in H1; eauto;
          destruct H1; destruct_ex; intuition; subst.
    eexists; eexists; repeat split.
    repeat computes_to_econstructor; eauto.
    simpl; rewrite transform_assoc; reflexivity.
    eassumption.
    simpl; eauto.
  }
Qed.
