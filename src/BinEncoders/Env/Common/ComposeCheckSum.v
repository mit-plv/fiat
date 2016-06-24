Require Import
        Fiat.Computation
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Notations.

Section Checksum.

  Variable A : Type. (* Type of data to be encoded. *)
  Variable B : Type. (* Type of encoded values. *)
  Variable transformer : Transformer B. (* Record of operations on encoded values. *)

  Variable calculate_checksum : B -> B. (* Function to compute checksums. *)
  Variable checksum_Valid : nat -> B -> Prop.  (* Property of properly checksummed encoded values. *)
  Variable checksum_Valid_dec :         (* Checksum validity should be decideable . *)
    forall n b, {checksum_Valid n b} + {~ checksum_Valid n b}.
  Variable checksum_OK :
    forall b ext, checksum_Valid (bin_measure (transform b (calculate_checksum b)))
                                 (transform (transform b (calculate_checksum b)) ext).
  Variable checksum_commute :
    forall b b', calculate_checksum (transform b b') = calculate_checksum (transform b' b).
  Variable checksum_Valid_commute :
    forall b b' ext, checksum_Valid (bin_measure (transform b b')) (transform (transform b b') ext) <->
                     checksum_Valid (bin_measure (transform b' b)) (transform (transform b' b) ext).
  Variable cache : Cache.

  Open Scope comp_scope.

  Definition composeChecksum {Env}
             (encode1 : Env -> Comp (B * Env))
             (encode2 : Env -> Comp (B * Env))
             (ctx : Env) :=
    `(p, ctx) <- encode1 ctx;
      `(q, ctx) <- encode2 ctx;
      ret (transform p (transform (calculate_checksum (transform p q)) q), ctx)%comp.

  Lemma compose_encode_correct
        {A'}
        {P  : CacheDecode -> Prop}
        {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
        (decodeChecksum : B -> CacheDecode -> option (unit * B * CacheDecode))
        (P_inv_pf :
           cache_inv_Property P (fun P =>
                                   P_inv1 P /\ P_inv2 P
                                   /\ (forall b ctx u b' ctx',
                                          decodeChecksum b ctx = Some (u, b', ctx')
                                          -> P ctx
                                          -> P ctx')))
        (project : A -> A')
        (predicate : A -> Prop)
        (predicate' : A' -> Prop)
        (predicate_rest' : A -> B -> Prop)
        (predicate_rest : A' -> B -> Prop)
        (encode1 : A' -> CacheEncode -> Comp (B * CacheEncode))
        (encode2 : A -> CacheEncode -> Comp (B * CacheEncode))
        (encoded_A_measure : B -> nat)
        (encoded_A_measure_OK :
           forall a ctx ctx' b ext,
             computes_to (composeChecksum (encode1 (project a)) (encode2 a) ctx) (b, ctx')
             -> bin_measure b = encoded_A_measure (transform b ext))
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
             -> predicate_rest a' (transform (transform (calculate_checksum (transform b' b'')) b'') b))
        (decodeChecksum_pf : forall b b' ext a' ctx ctx' ctxD,
            computes_to (encode1 a' ctx) (b, ctx')
            -> Equiv ctx' ctxD
            -> decodeChecksum (transform (transform (calculate_checksum (transform b b')) b') ext) ctxD =
               Some (tt, transform b' ext, ctxD))
        (decodeChecksum_pf' : forall u b b' ctx ctxD ctxD',
            Equiv ctx ctxD
            -> decodeChecksum b ctxD = Some (u, b', ctxD')
            -> Equiv ctx ctxD'
               /\ exists b'', b = transform b'' b')
        (decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
        (decode2_pf : forall proj,
            predicate' proj ->
            cache_inv_Property P P_inv2 ->
            encode_decode_correct_f cache transformer
                                    (fun data => predicate data /\ project data = proj)
                                    predicate_rest'
                                    encode2
                                    (decode2 proj) P)
        (checksum_Valid_chk :
           forall env env' xenv' data ext c0 c1 x x0 x1 x2 x3,
             Equiv env env' ->
             P env' ->
             Equiv x0 c0 ->
             P xenv' ->
             Equiv x2 xenv' ->
             predicate data ->
             encode_decode_correct_f cache transformer predicate' predicate_rest encode1 decode1 P ->
             encode1 (project data) env ↝ (x, x0) ->
             predicate' (project data) ->
             decode2 (project data) (transform x1 ext) c1 = Some (data, ext, xenv') ->
             encode2 data x0 ↝ (x1, x2) ->
             Equiv x0 c1 ->
             checksum_Valid (encoded_A_measure (transform x (transform x3 (transform x1 ext)))) (transform x (transform x3 (transform x1 ext))) ->
             x3 = calculate_checksum (transform x x1))
    : encode_decode_correct_f
        cache transformer
        (fun a => predicate a)
        predicate_rest'
        (fun (data : A) (ctx : CacheEncode) =>
           composeChecksum (encode1 (project data)) (encode2 data)  ctx
        )%comp
        (fun (bin : B) (env : CacheDecode) =>
           if checksum_Valid_dec (encoded_A_measure bin) bin then
             `(proj, rest, env') <- decode1 bin env;
               `(_, rest', env') <- decodeChecksum rest env';
               decode2 proj rest' env'
           else None)
        P.
  Proof.
    unfold cache_inv_Property in *; split.
    { intros env env' xenv data bin ext env_pm pred_pm pred_pm_rest com_pf.
      unfold composeChecksum, Bind2 in com_pf; computes_to_inv; destruct v;
        destruct v0.
      destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (transform (transform (calculate_checksum (transform b b0)) b0) ext) env_pm (pred_pf _ pred_pm) H' com_pf); intuition; simpl in *; injections; eauto.
      find_if_inside.
      - setoid_rewrite <- transform_assoc; rewrite H2.
        simpl; rewrite (decodeChecksum_pf _ _ _ _ _ _ _ com_pf); simpl; eauto.
        destruct (fun H'' => proj1 (decode2_pf (project data) (pred_pf _ pred_pm) H)
                                   _ _ _ _ _ ext H3 (conj pred_pm (eq_refl _)) H'' com_pf');
          intuition; simpl in *; injections.
        eauto.
      - destruct f.
        erewrite <- encoded_A_measure_OK, <- transform_assoc, checksum_commute; eauto.
        rewrite !transform_assoc.
        rewrite checksum_Valid_commute, transform_assoc; eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
    }
    { intros.
      find_if_inside; try discriminate.
      - destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
          simpl in *; try discriminate.
        eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto.
        destruct Heqo as [? [? [? [? [? [? ?] ] ] ] ] ]; subst.
        destruct (decodeChecksum b c0) as [ [ [? ?] ? ] | ] eqn : ? ;
          simpl in *; try discriminate.
        eapply P_inv_pf in H2; eauto.
        eapply (proj2 (decode2_pf a H5 (proj1 (proj2 P_inv_pf)))) in H2; eauto.
        destruct H2 as [? ?]; destruct_ex; intuition; subst.
        eexists; eexists; repeat split.
        repeat computes_to_econstructor; eauto.
        simpl; rewrite transform_assoc.
        rewrite <- !transform_assoc.
        eapply decodeChecksum_pf' in Heqo; eauto; intuition; destruct_ex;
          subst.
        simpl in *.
        repeat f_equal.
        eauto.
        eassumption.
        simpl; eassumption.
        simpl; eapply decodeChecksum_pf' in Heqo; intuition eauto.
    }
  Qed.

End Checksum.

Notation "encode1 'ThenChecksum' c 'ThenC' encode2"
  := (composeChecksum _ _ c encode1 encode2) : binencoders_scope.
