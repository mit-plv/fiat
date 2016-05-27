Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose.

Set Implicit Arguments.

Lemma compose_encode_correct A A' B
      (cache : Cache)
      {P : CacheDecode -> Prop}
      (transformer : Transformer B)
      (project : A -> A')
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (encode1 : A' -> CacheEncode -> Comp (B * CacheEncode))
      (encode2 : A -> CacheEncode -> Comp (B * CacheEncode))
      (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
      (decode1_pf : encode_decode_correct_f cache transformer predicate' encode1 decode1 P)
      (pred_pf : forall data, predicate data -> predicate' (project data))
      (decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
      (decode2_pf : forall proj,
          encode_decode_correct_f cache transformer
            (fun data => predicate data /\ project data = proj)
            encode2
            (decode2 proj) P)
  : encode_decode_correct_f
      cache transformer predicate
      (fun (data : A) (ctx : CacheEncode) =>
         `(bin, env') <- encode1 (project data) ctx;
         `(bin', env'') <- encode2 data env';
         ret (transform bin bin', env'')
      )%comp
     (fun (bin : B) (env : CacheDecode) =>
        `(proj, rest, env') <- decode1 bin env;
          decode2 proj rest env') P.
Proof.
  split.
  { intros env env' xenv data bin ext env_pm pred_pm com_pf.
    unfold Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    destruct (proj1 decode1_pf _ _ _ _ _ (transform b0 ext) env_pm (pred_pf _ pred_pm) com_pf); intuition; simpl in *; injections.
    setoid_rewrite <- transform_assoc; rewrite H0.
    simpl.
    destruct (proj1 (decode2_pf (project data)) _ _ _ _ _ ext H1 (conj pred_pm (eq_refl _)) com_pf'); intuition; simpl in *; injections.
    rewrite H2; eauto. }
  { intros.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    eapply (proj2 decode1_pf) in Heqo; eauto;
      destruct Heqo; destruct_ex; intuition;
        eapply (proj2 (decode2_pf a)) in H1; eauto;
          destruct H1; destruct_ex; intuition; subst.
    eexists; eexists; repeat split.
    repeat computes_to_econstructor; eauto.
    simpl; rewrite transform_assoc; reflexivity.
    eassumption.
    simpl; eauto.
  }
Qed.
