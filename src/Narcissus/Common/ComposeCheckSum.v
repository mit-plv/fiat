Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Formats.WordOpt.

Section Checksum.

  Variable A : Type. (* Type of data to be formatd. *)
  Variable B : Type. (* Type of formatd values. *)
  Variable monoid : Monoid B. (* Record of operations on formatd values. *)
  Variable monoid_opt : QueueMonoidOpt monoid bool.

  (*Variable calculate_checksum : B -> B -> B. (* Function to compute checksums. *) *)

  Variable checksum_sz : nat.
  Variable checksum_Valid : nat -> B -> Prop.  (* Property of properly checksummed formatd values. *)
  Variable checksum_Valid_dec :         (* Checksum validity should be decideable . *)
    forall n b, {checksum_Valid n b} + {~ checksum_Valid n b}.
  (*Variable checksum_OK :
    forall b ext, checksum_Valid (bin_measure (mappend b (calculate_checksum b)))
                                 (mappend (mappend b (calculate_checksum b)) ext).
  Variable checksum_commute :
    forall b b', calculate_checksum (mappend b b') = calculate_checksum (mappend b' b).
  Variable checksum_Valid_commute :
    forall b b' ext, checksum_Valid (bin_measure (mappend b b')) (mappend (mappend b b') ext) <->
                     checksum_Valid (bin_measure (mappend b' b)) (mappend (mappend b' b) ext). *)
  Variable cache : Cache.

  Open Scope comp_scope.

  Definition format_checksum c := encode_word' checksum_sz c mempty.

  Definition composeChecksum {Env}
             (format1 : Env -> Comp (B * Env))
             (format2 : Env -> Comp (B * Env))
             (ctx : Env) :=
    `(p, ctx) <- format1 ctx;
    `(q, ctx) <- format2 ctx;
    c <- { c : word checksum_sz | forall ext,
             checksum_Valid
               (bin_measure (mappend p (mappend (format_checksum c) q)))
               (mappend (mappend p (mappend (format_checksum c) q)) ext) };
    ret (mappend p (mappend (format_checksum c) q), ctx)%comp.

  Lemma composeChecksum_format_correct
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
        (format1 : A' -> CacheFormat -> Comp (B * CacheFormat))
        (format2 : A -> CacheFormat -> Comp (B * CacheFormat))
        (formatd_A_measure : B -> nat)
        (formatd_A_measure_OK :
           forall a ctx ctx' ctx'' b b' b'' ext,
             computes_to (format1 (project a) ctx) (b, ctx')
             -> computes_to (format2 a ctx') (b'', ctx'')
             -> predicate a
             -> bin_measure (mappend b (mappend (format_checksum b') b''))
                = formatd_A_measure (mappend (mappend b (mappend (format_checksum b') b'')) ext))
        (*checksum_Valid_OK :
           forall a ctx ctx' ctx'' b b' ext,
             computes_to (format1 (project a) ctx) (b, ctx')
             -> computes_to (format2 a ctx') (b', ctx'')
             -> predicate a
             -> checksum_Valid
                          (bin_measure (mappend (mappend b (calculate_checksum b b')) b'))
                          (mappend (mappend (mappend b (calculate_checksum b b')) b') ext) *)
        (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
        (decode1_pf :
           cache_inv_Property P P_inv1
           -> CorrectDecoder
                monoid predicate'
                predicate_rest
                format1 decode1 P)
        (pred_pf : forall data, predicate data -> predicate' (project data))
        (predicate_rest_impl :
           forall a' b
                  a ce ce' ce'' b' b'' c,
             computes_to (format1 a' ce) (b', ce')
             -> project a = a'
             -> predicate a
             -> computes_to (format2 a ce') (b'', ce'')
             -> predicate_rest' a b
             -> computes_to
                  { c | forall ext,
                      checksum_Valid
                        (bin_measure (mappend b' (mappend (format_checksum c) b'')))
                        (mappend (mappend b' (mappend (format_checksum c) b'')) ext)} c
             -> predicate_rest a' (mappend (mappend (format_checksum c) b'') b))
        (decodeChecksum_pf : forall a' b a ce ce' ce'' b' b'' c ctxD ext,
             computes_to (format1 a' ce) (b', ce')
             -> project a = a'
             -> predicate a
             -> computes_to (format2 a ce') (b'', ce'')
             -> predicate_rest' a b
             -> computes_to
                  { c | forall ext,
                      checksum_Valid
                        (bin_measure (mappend b' (mappend (format_checksum c) b'')))
                        (mappend (mappend b' (mappend (format_checksum c) b'')) ext)} c
             -> decodeChecksum (mappend (mappend (format_checksum c) b'') ext) ctxD =
               Some (tt, mappend b'' ext, ctxD))
        (decodeChecksum_pf' : forall u b b' ctx ctxD ctxD',
            Equiv ctx ctxD
            -> decodeChecksum b ctxD = Some (u, b', ctxD')
            -> Equiv ctx ctxD'
               /\ exists c,
                b = mappend (format_checksum c) b')
        (decode2 : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
        (decode2_pf : forall proj,
            predicate' proj ->
            cache_inv_Property P P_inv2 ->
            CorrectDecoder monoid
                                    (fun data => predicate data /\ project data = proj)
                                    predicate_rest'
                                    format2
                                    (decode2 proj) P)
        (checksum_Valid_chk :
           forall data x x0 x1 x2 ext ext' env c,
             predicate data
             -> format1 (project data) env ↝ (x, x0)
             -> format2 data x0 ↝ (x1, x2)
             -> checksum_Valid (bin_measure (mappend x (mappend (format_checksum c) x1))) (mappend (mappend x (mappend (format_checksum c) x1)) ext)
             -> checksum_Valid (bin_measure (mappend x (mappend (format_checksum c) x1))) (mappend (mappend x (mappend (format_checksum c) x1)) ext'))
        (*checksum_Valid_chk :
           forall env xenv' data ext c0 c1 x x0 x1 x2 x3,
             checksum_Valid
               (bin_measure (mappend x (mappend x3 x1)))
               (mappend x (mappend x3 (mappend x1 ext)))
             -> predicate data
             -> format1 (project data) env ↝ (x, x0)
             -> predicate' (project data)
             -> decodeChecksum (mappend x3 (mappend x1 ext)) c0 = Some (tt, mappend x1 ext, c1)
             -> decode2 (project data) (mappend x1 ext) c1 = Some (data, ext, xenv')
             -> format2 data (snd (x, x0)) ↝ (x1, x2)
             -> mappend x (mappend x3 (mappend x1 ext)) = mappend x (mappend (calculate_checksum x x1) (mappend x1 ext))*)
    : CorrectDecoder
        monoid
        predicate
        predicate_rest'
        (fun (data : A) =>
           composeChecksum (format1 (project data)) (format2 data)
        )%comp
        (fun (bin : B) (env : CacheDecode) =>
           if checksum_Valid_dec (formatd_A_measure bin) bin then
             `(proj, rest, env') <- decode1 bin env;
               `(_, rest', env') <- decodeChecksum rest env';
               decode2 proj rest' env'
           else None)
        P.
  Proof.
    unfold cache_inv_Property in *; split.
    { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
      unfold composeChecksum, Bind2 in com_pf; computes_to_inv; destruct v;
        destruct v0.
      simpl in *.
      destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend (mappend (format_checksum v1) b0) ext) env_OK env_pm (pred_pf _ pred_pm) H' com_pf); intuition; simpl in *; injections; eauto.
      find_if_inside.
      - setoid_rewrite <- mappend_assoc; rewrite H2.
        simpl.
        simpl; rewrite (decodeChecksum_pf _ _ _ _ _ _ _ _ _ _ _ com_pf (eq_refl _) pred_pm com_pf' pred_pm_rest); simpl; eauto.
        destruct (fun H'' => proj1 (decode2_pf (project data) (pred_pf _ pred_pm) H)
                                   _ _ _ _ _ ext H5 H1 (conj pred_pm (eq_refl _)) H'' com_pf');
          intuition; simpl in *; injections.
        eauto.
      - destruct f.
        erewrite <- formatd_A_measure_OK; eauto.
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
        simpl; pose proof (decodeChecksum_pf' _ _ _ x0 _ _ H6 Heqo);
          intuition; destruct_ex; intuition; subst.
        rewrite !mappend_assoc in c.
        rewrite <- (mappend_assoc x (format_checksum x3)) in c.
        erewrite <- formatd_A_measure_OK in c; try eassumption;
          try (eapply H16; eauto).
        eexists; eexists; repeat split.
        unfold composeChecksum.
        repeat computes_to_econstructor; eauto.
        simpl; intros; eauto.
        rewrite !mappend_assoc.
        eauto.
        eauto.
        eauto.
        simpl; eapply decodeChecksum_pf' in Heqo; intuition eauto.
    }
  Qed.

End Checksum.


(*Section ComposeComposeChecksum.

  Variable A : Type. (* Type of data to be formatd. *)
  Variable B : Type. (* Type of formatd values. *)
  Variable monoid : Monoid B. (* Record of operations on formatd values. *)

  Variable calculate_checksum : B -> B -> B. (* Function to compute checksums. *)
  Variable checksum_Valid : nat -> B -> Prop.  (* Property of properly checksummed formatd values. *)
  Variable checksum_Valid_dec :         (* Checksum validity should be decideable . *)
    forall n b, {checksum_Valid n b} + {~ checksum_Valid n b}.
  (*Variable checksum_OK :
    forall b ext, checksum_Valid (bin_measure (mappend b (calculate_checksum b)))
                                 (mappend (mappend b (calculate_checksum b)) ext).
  Variable checksum_commute :
    forall b b', calculate_checksum (mappend b b') = calculate_checksum (mappend b' b).
  Variable checksum_Valid_commute :
    forall b b' ext, checksum_Valid (bin_measure (mappend b b')) (mappend (mappend b b') ext) <->
                     checksum_Valid (bin_measure (mappend b' b)) (mappend (mappend b' b) ext). *)
  Variable cache : Cache.

Lemma composeChecksum_compose_format_correct
      {A'}
        {P  : CacheDecode -> Prop}
        {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
        (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
        (project : A -> A')
        (predicate : A -> Prop)
        (predicate' : A' -> Prop)
        (predicate_rest' : A -> B -> Prop)
        (predicate_rest : A' -> B -> Prop)
        (format1 : A' -> CacheFormat -> Comp (B * CacheFormat))
        (format2 : A -> CacheFormat -> Comp (B * CacheFormat))
        (format3 : A -> CacheFormat -> Comp (B * CacheFormat))
        (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
        (decode1_pf :
           cache_inv_Property P P_inv1
           -> CorrectDecoder
                cache monoid predicate'
                predicate_rest
                format1 decode1 P)
        (pred_pf : forall data, predicate data -> predicate' (project data))
        (predicate_rest_impl :
           forall a' b
                  a ce ce' ce'' ce''' b' b'' b''',
             format1 a' ce ↝ (b', ce')
             -> project a = a'
             -> predicate a
             -> format2 a ce' ↝ (b'', ce'')
             -> format3 a ce'' ↝ (b''', ce''')
             -> predicate_rest' a b
             -> predicate_rest a' (mappend (mappend (mappend b'' (calculate_checksum (mappend b' b'') b''')) b''') b))
        (decode23 : A' -> B -> CacheDecode -> option (A * B * CacheDecode))
        (decode23_pf :
           forall proj b' ce ce',
             predicate' proj
             -> format1 proj ce ↝ (b', ce')
             -> cache_inv_Property P P_inv2
             -> CorrectDecoder
                  cache monoid
                  (fun data => predicate data /\ project data = proj)
               predicate_rest'
               (fun (data : A) =>
                  composeChecksum _ _ (fun b => calculate_checksum (mappend b' b)) (format2 data) (format3 data)
               )%comp
               (decode23 proj) P)
    : CorrectDecoder
        cache monoid
        predicate
        predicate_rest'
        (fun (data : A) =>
           composeChecksum _ _ calculate_checksum (compose _ (format1 (project data)) (format2 data) ) (format3 data)
        )%comp
        (fun (bin : B) (env : CacheDecode) =>
           `(proj, rest, env') <- decode1 bin env;
             decode23 proj rest env')
        P.
  Proof.
    unfold cache_inv_Property in *; split.
    { intros env env' xenv data bin ext env_pm pred_pm pred_pm_rest com_pf.
      unfold composeChecksum, compose, Bind2 in com_pf; computes_to_inv; destruct v;
        destruct v0; destruct v1; destruct v2.
      destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend (mappend (mappend b2 (calculate_checksum b b0)) b0) ext) env_pm (pred_pf _ pred_pm) H' com_pf); intuition; simpl in *; injections; eauto.
      rewrite <- !mappend_assoc.
      rewrite <- !mappend_assoc in H2.
      rewrite H2.
      pose proof (proj1 (decode23_pf (project data) _ _ _ (pred_pf _ pred_pm) com_pf H1)).
      destruct (fun H'' => proj1 (decode23_pf (project data) _ _ _ (pred_pf _ pred_pm) com_pf H1)
                                 _ _ xenv _ (mappend b2 (mappend (calculate_checksum (mappend b1 b2) b0) b0)) ext H3 (conj pred_pm (eq_refl _)) H'');
        intuition; simpl in *; injections.
      unfold composeChecksum, compose, Bind2; computes_to_econstructor; eauto.
      rewrite !mappend_assoc.
      rewrite !mappend_assoc in H6; rewrite H6.
      eauto.
    }
    { intros.
      - destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
          simpl in *; try discriminate.
        eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto.
        destruct Heqo as [? [? [? [? [? [? ?] ] ] ] ] ]; subst.
        eapply (proj2 (decode23_pf a x env x0 H5 H3 (proj2 P_inv_pf))) in H1; eauto.
        destruct H1 as [? ?]; destruct_ex; intuition; subst.
        unfold composeChecksum, compose, Bind2 in *.
        computes_to_inv; injections.
        eexists; eexists; repeat split.
        repeat computes_to_econstructor; eauto.
        simpl; rewrite <- !mappend_assoc; reflexivity.
        eauto.
        eauto.
    }
  Qed.

  Lemma composeChecksum_compose_format_correct_no_dep
        {A'}
        (A_eq_dec : forall a a' : A', {a = a'} + {a <> a'})
        {P  : CacheDecode -> Prop}
        {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
        (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
        (predicate : A -> Prop)
        (predicate' : A' -> Prop)
        (predicate_rest' : A -> B -> Prop)
        (predicate_rest : A' -> B -> Prop)
        (format1 : A' -> CacheFormat -> Comp (B * CacheFormat))
        (format2 : A -> CacheFormat -> Comp (B * CacheFormat))
        (format3 : A -> CacheFormat -> Comp (B * CacheFormat))
        (decode1 : B -> CacheDecode -> option (A' * B * CacheDecode))
        (decode1_pf :
           cache_inv_Property P P_inv1
           -> CorrectDecoder
                cache monoid predicate'
                predicate_rest
                format1 decode1 P)
        (a' : A')
        (pred_pf : predicate' a')
        (predicate_rest_impl :
           forall b a ce ce' ce'' ce''' b' b'' b''',
             format1 a' ce ↝ (b', ce')
             -> predicate a
             -> format2 a ce' ↝ (b'', ce'')
             -> format3 a ce'' ↝ (b''', ce''')
             -> predicate_rest' a b
             -> predicate_rest a' (mappend (mappend (mappend b'' (calculate_checksum (mappend b' b'') b''')) b''') b))
        (decode23 : B -> CacheDecode -> option (A * B * CacheDecode))
        (decode23_pf :
           forall b' ce ce',
             format1 a' ce ↝ (b', ce')
             -> cache_inv_Property P P_inv2
             -> CorrectDecoder
                  cache monoid
                  predicate
               predicate_rest'
               (fun (data : A) =>
                  composeChecksum _ _ (fun b => calculate_checksum (mappend b' b)) (format2 data) (format3 data)
               )%comp
               decode23 P)
    : CorrectDecoder
        cache monoid
        predicate
        predicate_rest'
        (fun (data : A) =>
           composeChecksum _ _ calculate_checksum (compose _ (format1 a') (format2 data) ) (format3 data)
        )%comp
        (fun (bin : B) (env : CacheDecode) =>
           `(a, rest, env') <- decode1 bin env;
             (if A_eq_dec a a' then decode23 rest env' else None))
        P.
  Proof.
    unfold cache_inv_Property in *; split.
    { intros env env' xenv data bin ext env_pm pred_pm pred_pm_rest com_pf.
      unfold composeChecksum, compose, Bind2 in com_pf; computes_to_inv; destruct v;
        destruct v0; destruct v1; destruct v2.
      destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend (mappend (mappend b2 (calculate_checksum b b0)) b0) ext) env_pm pred_pf H' com_pf); intuition; simpl in *; injections; eauto.
      rewrite <- !mappend_assoc.
      rewrite <- !mappend_assoc in H2.
      rewrite H2.
      pose proof (proj1 (decode23_pf _ _ _ com_pf H1)).
      destruct (fun H'' => proj1 (decode23_pf _ _ _ com_pf H1)
                                 _ _ xenv _ (mappend b2 (mappend (calculate_checksum (mappend b1 b2) b0) b0)) ext H3 pred_pm H'');
        intuition; simpl in *; injections.
      unfold composeChecksum, compose, Bind2; computes_to_econstructor; eauto.
      rewrite !mappend_assoc.
      rewrite !mappend_assoc in H6; rewrite H6.
      find_if_inside; eauto.
      congruence.
    }
    { intros.
      - destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
          simpl in *; try discriminate.
        eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto.
        destruct Heqo as [? [? [? [? [? [? ?] ] ] ] ] ]; subst.
        find_if_inside; subst; try discriminate.
        eapply (proj2 (decode23_pf x env x0 H3 (proj2 P_inv_pf))) in H1; eauto.
        destruct H1 as [? ?]; destruct_ex; intuition; subst.
        unfold composeChecksum, compose, Bind2 in *.
        computes_to_inv; injections.
        eexists; eexists; repeat split.
        repeat computes_to_econstructor; eauto.
        simpl; rewrite <- !mappend_assoc; reflexivity.
        eauto.
        eauto.
    }
  Qed.

End ComposeComposeChecksum.

  (* Corollary composeChecksum_compose_format_correct *)
  (*       {A_fst} *)
  (*       {P  : CacheDecode -> Prop} *)
  (*       {P_inv_fst P_inv_snd P_inv2 : (CacheDecode -> Prop) -> Prop} *)
  (*       (decodeChecksum : B -> CacheDecode -> option (unit * B * CacheDecode)) *)
  (*       (P_inv_pf : *)
  (*          cache_inv_Property P (fun P => *)
  (*                                  P_inv_fst P /\ P_inv_snd P /\ P_inv2 P *)
  (*                                  /\ (forall b ctx u b' ctx', *)
  (*                                         decodeChecksum b ctx = Some (u, b', ctx') *)
  (*                                         -> P ctx *)
  (*                                         -> P ctx'))) *)
  (*       (project_fst : A -> A_fst) *)
  (*       (project_snd : A -> A_snd) *)
  (*       (predicate : A -> Prop) *)
  (*       (predicate_fst : A_fst -> Prop) *)
  (*       (predicate_snd : A_snd -> Prop) *)
  (*       (predicate_rest' : A -> B -> Prop) *)
  (*       (predicate_rest_fst : A_fst -> B -> Prop) *)
  (*       (predicate_rest_snd : A_snd -> B -> Prop) *)
  (*       (format_fst : A_fst -> CacheFormat -> Comp (B * CacheFormat)) *)
  (*       (format_snd : A -> CacheFormat -> Comp (B * CacheFormat)) *)
  (*       (format2 : A -> CacheFormat -> Comp (B * CacheFormat)) *)
  (*       (formatd_A_measure : B -> nat) *)
  (*       (formatd_A_measure_OK : *)
  (*          forall a ctx ctx' b ext, *)
  (*            computes_to (composeChecksum (compose _ (format_fst (project_fst a)) (format_snd (project_snd a))) (format2 a) ctx) (b, ctx') *)
  (*            -> bin_measure b = formatd_A_measure (mappend b ext)) *)
  (*       (decode_fst : B -> CacheDecode -> option (A_fst * B * CacheDecode)) *)
  (*       (decode_fst_pf : *)
  (*          cache_inv_Property P P_inv_fst *)
  (*          -> CorrectDecoder *)
  (*               cache monoid predicate_fst *)
  (*               predicate_rest_fst *)
  (*               format_fst decode_fst P) *)
  (*       (pred_fst_pf : forall data, predicate data -> predicate_fst (project_fst data)) *)
  (*       (*predicate_rest_impl : *)
  (*          forall a' b *)
  (*                 a ce ce' ce'' b' b'', *)
  (*            computes_to (format1 a' ce) (b', ce') *)
  (*            -> project a = a' *)
  (*            -> predicate a *)
  (*            -> computes_to (format2 a ce') (b'', ce'') *)
  (*            -> predicate_rest' a b *)
  (*            -> predicate_rest_fst a' (mappend (mappend (calculate_checksum (mappend b' b'')) b'') b) *) *)
  (*       (*decodeChecksum_pf : forall b b' ext a' ctx ctx' ctxD, *)
  (*           computes_to (format1 a' ctx) (b, ctx') *)
  (*           -> Equiv ctx' ctxD *)
  (*           -> decodeChecksum (mappend (mappend (calculate_checksum (mappend b b')) b') ext) ctxD = *)
  (*              Some (tt, mappend b' ext, ctxD)) *)
  (*       (decodeChecksum_pf' : forall u b b' ctx ctxD ctxD', *)
  (*           Equiv ctx ctxD *)
  (*           -> decodeChecksum b ctxD = Some (u, b', ctxD') *)
  (*           -> Equiv ctx ctxD' *)
  (*              /\ exists b'', b = mappend b'' b'*) *)
  (*       (decode2 : A_fst -> B -> CacheDecode -> option (A * B * CacheDecode)) *)
  (*       (decode2_pf : forall proj_fst proj_snd, *)
  (*           predicate_fst proj_fst -> *)
  (*           predicate_snd proj_snd -> *)
  (*           cache_inv_Property P P_inv2 -> *)
  (*           CorrectDecoder cache monoid *)
  (*                                   (fun data => predicate data *)
  (*                                                /\ project_fst data = proj_fst *)
  (*                                                /\ project_snd data = proj_snd) *)
  (*                                   predicate_rest' *)
  (*                                   format2 *)
  (*                                   (decode2 proj_fst proj_snd) P) *)
  (*       (*checksum_Valid_chk : *)
  (*          forall env env' xenv' data ext c0 c1 x x0 x1 x2 x3, *)
  (*            Equiv env env' -> *)
  (*            P env' -> *)
  (*            Equiv x0 c0 -> *)
  (*            P xenv' -> *)
  (*            Equiv x2 xenv' -> *)
  (*            predicate data -> *)
  (*            CorrectDecoder cache monoid predicate' predicate_rest format1 decode1 P -> *)
  (*            format1 (project data) env ↝ (x, x0) -> *)
  (*            predicate' (project data) -> *)
  (*            decode2 (project_fst data) (mappend x1 ext) c1 = Some (data, ext, xenv') -> *)
  (*            format2 data x0 ↝ (x1, x2) -> *)
  (*            Equiv x0 c1 -> *)
  (*            checksum_Valid (formatd_A_measure (mappend x (mappend x3 (mappend x1 ext)))) (mappend x (mappend x3 (mappend x1 ext))) -> *)
  (*            x3 = calculate_checksum (mappend x x1)*) *)
  (*   : CorrectDecoder *)
  (*       cache monoid *)
  (*       (fun a => predicate a) *)
  (*       predicate_rest' *)
  (*       (fun (data : A) (ctx : CacheFormat) => *)
  (*          composeChecksum (compose _ (format_fst (project_fst data)) (format_snd (project_snd data))) (format2 data)  ctx *)
  (*       )%comp *)
  (*       (fun (bin : B) (env : CacheDecode) => *)
  (*          if checksum_Valid_dec (formatd_A_measure bin) bin then *)
  (*            `(proj_fst, rest, env') <- decode_fst bin env; *)
  (*            `(proj_snd, rest, env') <- decode_snd rest env'; *)
  (*            `(_, rest', env') <- decodeChecksum rest env'; *)
  (*              decode2 proj_fst proj_snd rest' env' *)
  (*          else None) *)
  (*       P. *)
  (* Proof. *)
  (*unfold cache_inv_Property in *; split.
    { intros env env' xenv data bin ext env_pm pred_pm pred_pm_rest com_pf.
      eapply composeChecksum_format_correct in com_pf.

      unfold composeChecksum, Bind2 in com_pf; computes_to_inv; destruct v;
        destruct v0.
      destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend (mappend (calculate_checksum (mappend b b0)) b0) ext) env_pm (pred_pf _ pred_pm) H' com_pf); intuition; simpl in *; injections; eauto.
      find_if_inside.
      - setoid_rewrite <- mappend_assoc; rewrite H2.
        simpl; rewrite (decodeChecksum_pf _ _ _ _ _ _ _ com_pf); simpl; eauto.
        destruct (fun H'' => proj1 (decode2_pf (project data) (pred_pf _ pred_pm) H)
                                   _ _ _ _ _ ext H3 (conj pred_pm (eq_refl _)) H'' com_pf');
          intuition; simpl in *; injections.
        eauto.
      - destruct f.
        erewrite <- formatd_A_measure_OK, <- mappend_assoc, checksum_commute; eauto.
        rewrite !mappend_assoc.
        rewrite checksum_Valid_commute, mappend_assoc; eauto.
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
        simpl; rewrite mappend_assoc.
        rewrite <- !mappend_assoc.
        eapply decodeChecksum_pf' in Heqo; eauto; intuition; destruct_ex;
          subst.
        simpl in *.
        repeat f_equal.
        eauto.
        eassumption.
        simpl; eassumption.
        simpl; eapply decodeChecksum_pf' in Heqo; intuition eauto.
    }
  Qed. *) *)

Notation "format1 'ThenChecksum' c 'OfSize' sz 'ThenCarryOn' format2"
  := (composeChecksum _ _ _ sz c format1 format2) : format_scope.
