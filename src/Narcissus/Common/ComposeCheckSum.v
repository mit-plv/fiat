Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.BaseFormats.

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
  Context {cacheAddNat : CacheAdd cache nat}.

  Open Scope comp_scope.

  Definition format_checksum c := encode_word' checksum_sz c mempty.

  Definition composeChecksum
             (format1 : FormatM A B)
             (format2 : FormatM A B)
             (a : A) (ctx : _) :=
    `(p, ctx) <- format1 a ctx;
    `(q, ctx) <- format2 a (addE ctx checksum_sz);
    c <- { c : word checksum_sz | forall ext,
             checksum_Valid
               (bin_measure (mappend p (mappend (format_checksum c) q)))
               (mappend (mappend p (mappend (format_checksum c) q)) ext) };
    ret (mappend p (mappend (format_checksum c) q), ctx)%comp.

  Lemma composeChecksum_format_correct
        {P  : CacheDecode -> Prop}
        {P_inv : (CacheDecode -> Prop) -> Prop}
        (decodeChecksum := decode_unused_word (sz := checksum_sz))
        (P_inv_pf :
           cache_inv_Property P (fun P => P_inv P))
        (predicate : A -> Prop)
        (format1 format2 : A -> CacheFormat -> Comp (B * CacheFormat))
        (formatd_A_measure : B -> nat)
        (formatd_A_measure_OK :
           forall a ctx ctx' ctx'' b b' b'' ext,
             computes_to (format1 a ctx) (b, ctx')
             -> computes_to (format2 a (addE ctx' checksum_sz)) (b'', ctx'')
             -> predicate a
             -> bin_measure (mappend b (mappend (format_checksum b') b''))
                = formatd_A_measure (mappend (mappend b (mappend (format_checksum b') b'')) ext))
        (decodeA : B -> CacheDecode -> option (A * B * CacheDecode))
        (decodeA_pf :
           cache_inv_Property P P_inv
           -> CorrectDecoder
                monoid
                predicate
                predicate
                eq
                (format1 ++ format_unused_word checksum_sz ++ format2) decodeA P
                (format1 ++ format_unused_word checksum_sz ++ format2))
        (checksum_Valid_chk :
           forall data x x0 x1 x2 ext ext' env c,
             predicate data
             -> format1 data env ↝ (x, x0)
             -> format2 data (addE x0 checksum_sz) ↝ (x1, x2)
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
        predicate
        eq
        (composeChecksum format1 format2)
        (fun (bin : B) (env : CacheDecode) =>
           if checksum_Valid_dec (formatd_A_measure bin) bin then
             decodeA bin env
           else None)
        P
        (composeChecksum format1 format2).
  Proof.
    unfold cache_inv_Property in *; split.
    { intros env env' xenv data bin ext ? env_pm pred_pm com_pf.
      unfold composeChecksum, Bind2 in com_pf; computes_to_inv; destruct v;
        destruct v0.
      simpl in *.
      find_if_inside.
      - intuition.
        eapply H; eauto.
        rewrite <- com_pf'''.
        unfold sequence_Format, compose.
        computes_to_econstructor; try eassumption; simpl.
        eapply refineEquiv_bind2_bind.
        computes_to_econstructor.
        + instantiate (1 := (format_checksum v1, _)).
          apply unfold_computes.
          unfold format_unused_word, Compose_Format.
          eexists _; split; eauto;
          repeat computes_to_econstructor.
          apply unfold_computes; eauto.
        + eapply refineEquiv_bind2_bind.
          computes_to_econstructor; eauto.
          eapply refineEquiv_bind2_unit; reflexivity.
      - destruct n.
        injections.
        erewrite <- formatd_A_measure_OK; eauto.
    }
    { intros.
      find_if_inside; try discriminate.
      - eapply decodeA_pf in H1; intuition eauto.
        destruct H3 as [? [? [? [? [? ?] ] ] ] ].
        subst.
        unfold sequence_Format, compose, Bind2 in H3.
        computes_to_inv; subst.
        destruct v0; destruct v2; destruct v3; simpl in *.
        unfold composeChecksum, Bind2.
        unfold format_unused_word, Compose_Format in H3'.
        apply (proj1 (unfold_computes _ _)) in H3'; simpl in H3'.
        destruct_ex; intuition.
        unfold format_word in H7; computes_to_inv; injections.
        eexists _, _; split.
        computes_to_econstructor; eauto.
        computes_to_econstructor; simpl; eauto.
        computes_to_econstructor.
        computes_to_econstructor; simpl.
        intros; eapply checksum_Valid_chk.
        eassumption.
        eassumption.
        eassumption.
        erewrite formatd_A_measure_OK; eauto.
        computes_to_econstructor.
        intuition.
    }
  Qed.

End Checksum.

Notation "format1 'ThenChecksum' c 'OfSize' sz 'ThenCarryOn' format2"
  := (composeChecksum _ _ _ _ sz c _ format1 format2) : format_scope.
