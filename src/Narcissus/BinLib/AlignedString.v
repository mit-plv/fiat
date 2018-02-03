Require Import
        Coq.omega.Omega
        Coq.Strings.Ascii
        Coq.Strings.String
        Coq.Arith.Mult
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.DecideableEnsembles
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.FixStringOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.AsciiOpt
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant.

Require Import
        Bedrock.Word.

Section AlignedList.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Fixpoint BytesToString {sz}
           (b : Vector.t (word 8) sz)
    : string :=
    match b with
    | Vector.nil => EmptyString
    | Vector.cons a _ b' => String (Ascii.ascii_of_N (wordToN a)) (BytesToString b')
    end.

  Variable addD_addD_plus :
    forall (cd : CacheDecode) (n m : nat), addD (addD cd n) m = addD cd (n + m).

  Variable addE_addE_plus :
    forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m).

  Lemma decode_string_aligned_ByteString
        {sz sz'}
    : forall (b : t (word 8) (sz + sz'))
             (cd : CacheDecode),
      FixStringOpt.decode_string sz (build_aligned_ByteString b) cd =
      Some (BytesToString (fst (Vector_split sz sz' b)),
            build_aligned_ByteString (snd (Vector_split sz sz' b)),
            addD cd (8 * sz)).
  Proof.
    induction sz; intros.
    - simpl; repeat f_equal.
    - simpl.
      assert (forall A n b, exists a b', b = Vector.cons A a n b')
        by (clear; intros; pattern n, b; apply caseS; eauto).
      destruct (H _ _ b) as [? [? ?] ]; subst; simpl.
      unfold AsciiOpt.decode_ascii, DecodeBindOpt2.
      rewrite BindOpt_assoc; simpl.
      etransitivity.
      unfold BindOpt at 1.
      rewrite AlignedDecodeChar; simpl.
      rewrite IHsz. higher_order_reflexivity.
      simpl.
      destruct (Vector_split sz sz' x0); simpl.
      unfold LetIn.
      rewrite addD_addD_plus;
        repeat f_equal.
      omega.
  Qed.

  Fixpoint StringToBytes
           (s : string)
    : Vector.t (word 8) (String.length s) :=
    match s return Vector.t (word 8) (String.length s) with
    | EmptyString => Vector.nil _
    | String a s' => Vector.cons _ (NToWord 8 (Ascii.N_of_ascii a)) _ (StringToBytes s')
    end.

  Lemma format_string_ByteString
    : forall (s : string)
             (ce : CacheFormat),
      refine (FixStringOpt.format_string s ce)
             (ret (build_aligned_ByteString (StringToBytes s), addE ce (8 * String.length s))).
  Proof.
    induction s; intros; simpl.
    - f_equiv. f_equal.
      eapply ByteString_f_equal.
      instantiate (1 := eq_refl _); reflexivity.
      instantiate (1 := eq_refl _); reflexivity.
    - unfold AsciiOpt.format_ascii.
      unfold Bind2;  setoid_rewrite aligned_format_char_eq.
      simplify with monad laws.
      rewrite IHs.
      simplify with monad laws.
      simpl.
      rewrite <- build_aligned_ByteString_append; simpl.
      rewrite !addE_addE_plus.
      f_equiv; f_equiv; f_equiv; omega.
  Qed.

  Lemma format_string_aligned_ByteString {numBytes}
    : forall (s : string)
             (ce : CacheFormat)
             (ce' : CacheFormat)
             (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce (8 * String.length s))) (ret (build_aligned_ByteString v, ce'))
      -> refine (((FixStringOpt.format_string s) ThenC c) ce)
                (ret (build_aligned_ByteString (append (StringToBytes s) v), ce')).
  Proof.
    unfold compose, Bind2; autorewrite with monad laws; intros.
    rewrite format_string_ByteString.
    simplify with monad laws.
    unfold snd at 1.
    rewrite H.
    simplify with monad laws.
    simpl.
    rewrite <- build_aligned_ByteString_append; simpl.
    reflexivity.
  Qed.

  Lemma decode_string_aligned_ByteString_overflow
        {sz}
    : forall {sz'}
             (b : t (word 8) sz')
             (cd : CacheDecode),
      lt sz' sz
      -> FixStringOpt.decode_string sz (build_aligned_ByteString b) cd = None.
  Proof.
    induction sz; intros.
    - omega.
    - simpl.
      assert (forall A n b, exists a b', b = Vector.cons A a n b')
        by (clear; intros; pattern n, b; apply caseS; eauto).
      destruct sz'.
      + reflexivity.
      + destruct (H0 _ _ b) as [? [? ?] ]; subst; simpl.
        unfold AsciiOpt.decode_ascii, DecodeBindOpt2.
        rewrite BindOpt_assoc; simpl.
        etransitivity.
        unfold BindOpt.
        rewrite AlignedDecodeChar; simpl.
        rewrite IHsz. higher_order_reflexivity.
        omega.
        reflexivity.
  Qed.

  Fixpoint align_decode_string_with_term_char
           (term_char : word 8)
           {sz}
           (v : Vector.t (word 8) sz)
           (cd : CacheDecode)
    : option (string * {n : _ & Vector.t (word 8) n} * CacheDecode) :=
    match v with
    | Vector.nil => None
    | Vector.cons c _ v' => if weqb c term_char then
                              Some (String.EmptyString, existT _ _ v', cd)
                            else
                              `(s, b', cd') <- align_decode_string_with_term_char term_char v' cd;
                              Some (String (ascii_of_N (wordToN c)) s, b', cd')
    end.

  Lemma optimize_align_decode_string_w_term_char
    : forall (term_char : Ascii.ascii)
             {sz}
             (v : Vector.t (word 8) sz)
             (cd : CacheDecode),
      decode_string_with_term_char term_char (build_aligned_ByteString v) cd
      = Ifopt align_decode_string_with_term_char (NToWord _ (N_of_ascii term_char)) v cd as a
              Then
              Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
              Else
              None.
  Proof.
    intros.
  Admitted.

End AlignedList.
