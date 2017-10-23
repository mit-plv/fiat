Require Import
        Eqdep_dec
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.BinEncoders.Env.Common.Specs
        Coq.Numbers.BinNums
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Common.WordFacts
        compcert.lib.Integers.

Unset Implicit Arguments.

Module Make (WS : WORDSIZE).

  Include compcert.lib.Integers.Make(WS).

  Section Int.
    Context {B : Type}.
    Context {cache : Cache}.
    Context {cacheAddNat : CacheAdd cache nat}.
    Context {transformer : Transformer B}.
    Context {transformerUnit : QueueTransformerOpt transformer bool}.

    Definition intToWord (sz : nat) (i : int) : word sz :=
      match intval i with
      | 0%Z => wzero sz
      | Zpos p => posToWord sz p
      | _ => wzero sz
      end.

    Definition wordToInt {sz : nat} (w : word sz) : int :=
      repr (BinInt.Z.of_N (wordToN w)).

    Lemma intToWord_wordToInt
      : forall {sz} w,
        le sz wordsize
        -> intToWord sz (wordToInt w) = w.
    Proof.
      unfold wordToInt, intToWord, repr; simpl.
      intros; rewrite Z_mod_modulus_eq.
      unfold modulus.
      rewrite Coqlib.Zmod_small.
      replace (match BinInt.Z.of_N (wordToN w) with
               | 0%Z => wzero sz
               | Zpos p => posToWord sz p
               | Zneg _ => wzero sz
               end)
      with (match (wordToN w) with
            | 0%N => wzero sz
            | Npos p => posToWord sz p
            end) by (destruct (wordToN w); reflexivity).
      apply wordToN_inj.
      rewrite wordToN_nat at 1.
      destruct (wordToN w) eqn: ?.
      - replace (wordToNat (wzero sz)) with 0.
        reflexivity.
        clear; induction sz; simpl; eauto.
        replace (natToWord sz 0) with (wzero sz).
        rewrite <- IHsz; reflexivity.
        clear; induction sz; simpl; eauto.
      - rewrite posToWord_nat, wordToNat_natToWord_idempotent,
        Znat.positive_nat_N; eauto.
        rewrite Znat.positive_nat_N, <- Heqn.
        apply Nomega.Nlt_in;
          rewrite Npow2_nat, wordToN_nat, Nnat.Nat2N.id.
        apply wordToNat_bound.
      - split.
        + destruct ((wordToN w)); compute; congruence.
        + replace (Zpower.two_power_nat wordsize) with (BinInt.Z.of_N (Npow2 wordsize)).
          * apply Znat.N2Z.inj_lt.
            apply Nomega.Nlt_in;
              rewrite Npow2_nat, wordToN_nat, Nnat.Nat2N.id.
            eapply NPeano.Nat.lt_le_trans.
            apply wordToNat_bound.
            induction H; eauto.
            simpl; omega.
          * clear H;
              rewrite <- Znat.N_nat_Z, Zpower.two_power_nat_correct,
              Npow2_nat.
            induction wordsize; simpl; auto.
            rewrite <- IHn.
            rewrite !Znat.Nat2Z.inj_add.
            simpl.
            destruct (BinInt.Z.of_nat (pow2 n)); simpl.
            reflexivity.
            rewrite BinPos.Pos.add_diag; auto.
            rewrite BinPos.Pos.add_diag; auto.
    Qed.

    Definition encode_int_Spec (sz : nat) (i : int) (ce : CacheEncode) : Comp (B * CacheEncode) := encode_word_Spec (intToWord sz i) ce.

    Definition decode_int (sz : nat) (b : B) (cd : CacheDecode) : option (int * B * CacheDecode) :=
      `(w, b, cd) <- decode_word (sz:=sz) b cd;
        Some (wordToInt w, b, cd).

    Theorem innt_decode_correct
            (sz : nat)
            (sz_OK : le sz wordsize)
            {P : CacheDecode -> Prop}
            (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
      : encode_decode_correct_f cache transformer (fun i : int => BinInt.Z.lt (intval i) (BinInt.Z.of_N (Npow2 sz)))
                                (fun _ _ => True) (encode_int_Spec sz) (decode_int sz) P.
  Proof.
    unfold encode_decode_correct_f, encode_int_Spec, decode_int.
    split.
    { intros env xenv xenv' n n' ext ? Eeq Ppred Ppred_rest Penc.
      destruct (proj1 (Word_decode_correct P_OK) _ _ _ _ _ ext env_OK Eeq I I Penc) as [? [? [? xenv_OK] ] ].
      rewrite H; simpl; eexists; intuition eauto.
      repeat f_equal.
      unfold wordToInt, intToWord; destruct n; unfold repr; simpl.
      apply mkint_eq.
      rewrite Z_mod_modulus_eq.
      destruct intval0; simpl in *.
      - replace (wordToN (wzero sz)) with 0%N.
        reflexivity.
          clear; induction sz; simpl; eauto;
            unfold wzero in IHsz; rewrite <- IHsz; eauto.
      - rewrite posToWord_nat, wordToN_nat,
        wordToNat_natToWord_idempotent, Znat.positive_nat_N.
        apply Coqlib.Zmod_small; intuition.
        rewrite Znat.positive_nat_N.
        apply Znat.N2Z.inj_lt; simpl; eauto.
      - destruct intrange0.
        destruct p; compute in l; congruence.
    }
    { intros env xenv xenv' n n' ext Eeq OK_env Penc.
      destruct (decode_word n' xenv) as [ [ [? ? ] ? ] | ] eqn: ? ;
        simpl in *; try discriminate.
      injections.
      eapply (proj2 (Word_decode_correct P_OK)) in Heqo;
        destruct Heqo; destruct_ex; intuition; subst; eauto.
      unfold encode_word_Spec in *; computes_to_inv; injections.
      rewrite intToWord_wordToInt by eauto.
      - repeat eexists; eauto.
        unfold wordToInt; simpl.
        assert (BinInt.Z.lt (BinInt.Z.of_N (wordToN w)) (BinInt.Z.of_N (Npow2 sz))).
        { apply Znat.N2Z.inj_lt; simpl; eauto.
          apply Nomega.Nlt_in.
          rewrite Npow2_nat, wordToN_nat, Nnat.Nat2N.id.
          apply wordToNat_bound.
        }
        rewrite Z_mod_modulus_eq.
        destruct (Coqlib.zlt (BinInt.Z.of_N (wordToN w)) modulus).
        + rewrite Coqlib.Zmod_small; intuition.
          apply (Znat.N2Z.inj_le 0).
          destruct (wordToN w); compute; congruence.
        + etransitivity.
          apply Zdiv.Z_mod_lt.
          reflexivity.
          eapply BinInt.Z.le_lt_trans.
          eapply BinInt.Z.ge_le_iff; eassumption.
          eassumption.
    }
  Qed.

  End Int.

End Make.
