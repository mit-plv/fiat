Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.Base.FMapFormat.

Require Import Fiat.Computation.FixComp.
Import Fiat.Computation.FixComp.LeastFixedPointFun.

Section FixFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {cache : Cache}. (* State Type *)

  Definition Fix_Format
             (format_body : FormatM S T -> FormatM S T)
    := LeastFixedPoint (fDom := [S; CacheFormat]%type)
                       (fCod := T * CacheFormat) format_body.

  Fixpoint FueledFix' {A B C}
           (f : (B -> C -> option A) -> B -> C -> option A)
           (n : nat)
    : B -> C -> option A :=
    match n with
    | Datatypes.S n' => f (FueledFix' f n')
    | _ => fun _ _ => None
    end.

  
  Theorem FueledFix_continuous {A B C} (F : (B -> C -> option A) -> B -> C -> option A)
    : (forall n a b c,
          FueledFix' F n b c = Some a ->
          FueledFix' F (Datatypes.S n) b c = Some a) ->
      forall n n',
        n <= n' ->
        forall a b c,
          FueledFix' F n b c = Some a ->
          FueledFix' F n' b c = Some a.
  Proof.
    intros; induction H0; eauto.
  Qed.
  
  Definition Fix_Decode
             {monoid : Monoid T}
             (decode_body : DecodeM S T -> DecodeM S T)
    : DecodeM S T :=
    fun t env => FueledFix' decode_body (Datatypes.S (bin_measure t)) t env.

  Definition FMap_Target
             (P : T -> Prop)
             (format : FormatM S T)
    : FormatM S T :=
    fun s env tenv' =>
      format s env ∋ tenv'
       /\ P (fst tenv').
  
  Lemma CorrectDecoder_Fix'
        (decode_body : DecodeM S T -> DecodeM S T)
        (format_body : FormatM S T -> FormatM S T)
        (format_body_OK : Frame.monotonic_function (format_body : funType [S; CacheFormat] (T * CacheFormat) ->
                                                                  funType [S; CacheFormat] (T * CacheFormat)))
        (bound : T -> nat)        
        (decode_body_correct :
           forall n,
             (CorrectDecoder_simpl
                (FMap_Target (fun t => bound t < n)  (Fix_Format format_body))
                (FueledFix' decode_body n)) ->
             CorrectDecoder_simpl
               (FMap_Target (fun t => bound t < Datatypes.S n)
                            (format_body (Fix_Format format_body)))
               (decode_body (FueledFix' decode_body n)))
    : forall n,
      CorrectDecoder_simpl
        (FMap_Target (fun t => bound t < n) (Fix_Format format_body))
        (FueledFix' decode_body n).
  Proof.
    induction n; simpl; intros.
    - split; unfold FMap_Target; intros.
      + apply_in_hyp @unfold_computes; omega.
      + discriminate.
    - split; unfold FMap_Target in *; intros.
      + apply_in_hyp @unfold_computes; split_and.
        apply_in_hyp (unroll_LeastFixedPoint format_body_OK).
        eapply decode_body_correct; eauto.
        apply unfold_computes; intuition eauto.
      + eapply decode_body_correct in H0; eauto.
        destruct_ex; split_and.
        eexists; intuition eauto.
        apply unfold_computes.
        repeat apply_in_hyp @unfold_computes.
        intuition.
        eapply (unroll_LeastFixedPoint' format_body_OK).
        apply unfold_computes; eauto.
  Qed.

  Lemma CorrectDecoder_Fix
        {monoid : Monoid T}
        (decode_body : DecodeM S T -> DecodeM S T)
        (format_body : FormatM S T -> FormatM S T)
        (format_body_OK : Frame.monotonic_function (format_body : funType [S; CacheFormat] (T * CacheFormat) ->
                                                                  funType [S; CacheFormat] (T * CacheFormat)))
        (decode_body_correct :
           forall n,
             (CorrectDecoder_simpl
                (FMap_Target (fun t => bin_measure t < n)
                             (Fix_Format format_body))
                (FueledFix' decode_body n)) ->
             CorrectDecoder_simpl
               (FMap_Target (fun t => bin_measure t < Datatypes.S n)
                            (format_body (Fix_Format format_body)))
               (decode_body (FueledFix' decode_body n)))
        (decode_body_continuous :
           forall decode,
             (forall t env s env',
                 decode t env = Some (s, env') ->
                 decode_body decode t env = Some (s, env')) ->
             forall t env s env',
               decode_body decode t env = Some (s, env') ->
               decode_body (decode_body decode) t env = Some (s, env'))
    : CorrectDecoder_simpl
        (Fix_Format format_body)
        (Fix_Decode decode_body).
  Proof.
    split; intros.
    - destruct (CorrectDecoder_Fix'
                  decode_body format_body format_body_OK bin_measure
                  decode_body_correct (Datatypes.S (bin_measure bin))) as [? _]; eauto.
      eapply H1 in H;
        try solve [unfold FMap_Target; apply unfold_computes; split; eauto].
      destruct_ex; split_and;  eexists; intuition eauto.
    - destruct (CorrectDecoder_Fix'
                  decode_body format_body format_body_OK bin_measure
                  decode_body_correct (Datatypes.S (bin_measure bin))) as [_ ?]; eauto.
      eapply H1 in H;
        try solve [simpl; unfold Fix_Decode in H0; eauto].
      destruct_ex; split_and;  eexists; intuition eauto.
      unfold FMap_Target in H2; apply_in_hyp @unfold_computes; intuition.
  Qed.
  
  Definition Fix_Encode
             (measure : S -> nat)
             (encode_body : EncodeM S T -> EncodeM S T)
    : EncodeM S T :=
    fun s env => FueledFix' encode_body (Datatypes.S (measure s)) s env.

    Lemma CorrectEncoder_Fix'
        (encode_body : EncodeM S T -> EncodeM S T)
        (format_body : FormatM S T -> FormatM S T)
        (format_body_OK : Frame.monotonic_function (format_body : funType [S; CacheFormat] (T * CacheFormat) ->
                                                                  funType [S; CacheFormat] (T * CacheFormat)))
        (measure : S -> nat)        
        (encode_body_correct :
           forall n,
             (CorrectEncoder
                (Restrict_Format (fun s => measure s < n) (Fix_Format format_body))
                (FueledFix' encode_body n)) ->
             CorrectEncoder
               (Restrict_Format (fun s => measure s < Datatypes.S n)
                                (format_body (Fix_Format format_body)))
               (encode_body (FueledFix' encode_body n)))
    : forall n,
      CorrectEncoder
        (Restrict_Format (fun s => measure s < n) (Fix_Format format_body))
        (FueledFix' encode_body n).
    Proof.
    induction n; simpl; intros.
    - split; unfold Restrict_Format, FMap_Format; intros.
      + discriminate.
      + intro; apply_in_hyp @unfold_computes;
          destruct_ex; omega.
    - split; unfold Restrict_Format, FMap_Format in *; intros.
      + apply unfold_computes; intuition eauto.
        eapply encode_body_correct in H; eauto.
        apply_in_hyp @unfold_computes; destruct_ex; split_and.
        apply_in_hyp (unroll_LeastFixedPoint' format_body_OK); eauto.
      + intro; eapply encode_body_correct in H; eauto; eapply H.
        repeat apply_in_hyp @unfold_computes.
        destruct_ex; split_and.
        apply unfold_computes.
        eexists; subst; intuition eauto.
        eapply (unroll_LeastFixedPoint format_body_OK); eauto.
  Qed.

    Lemma CorrectEncoder_Fix
          (encode_body : EncodeM S T -> EncodeM S T)
        (format_body : FormatM S T -> FormatM S T)
        (format_body_OK : Frame.monotonic_function (format_body : funType [S; CacheFormat] (T * CacheFormat) ->
                                                                  funType [S; CacheFormat] (T * CacheFormat)))
        (measure : S -> nat)        
        (encode_body_correct :
           forall n,
             (CorrectEncoder
                (Restrict_Format (fun s => measure s < n) (Fix_Format format_body))
                (FueledFix' encode_body n)) ->
             CorrectEncoder
               (Restrict_Format (fun s => measure s < Datatypes.S n)
                                (format_body (Fix_Format format_body)))
               (encode_body (FueledFix' encode_body n)))
        (encode_body_continuous :
           forall encode,
             (forall t env s env',
                 encode t env = Some (s, env') ->
                 encode_body encode t env = Some (s, env')) ->
             forall t env s env',
               encode_body encode t env = Some (s, env') ->
               encode_body (encode_body encode) t env = Some (s, env'))
    : CorrectEncoder
        (Fix_Format format_body)
        (Fix_Encode measure encode_body).
  Proof.
    split; intros.
    - destruct (CorrectEncoder_Fix'
                  encode_body format_body format_body_OK measure
                  encode_body_correct (Datatypes.S (measure a))) as [? _]; eauto.
      eapply H0 in H;
        try solve [unfold FMap_Target; apply unfold_computes; split; eauto].      
      unfold Restrict_Format, FMap_Format in H.
      repeat apply_in_hyp @unfold_computes.
      destruct_ex; split_and; subst; eauto.
    - destruct (CorrectEncoder_Fix'
                  encode_body format_body format_body_OK measure
                  encode_body_correct (Datatypes.S (measure a))) as [_ ?]; eauto.
      eapply H0 in H;
        try solve [simpl; unfold Fix_Encode in H0; eauto].
      intro; eapply H.
      unfold Restrict_Format, FMap_Format; apply unfold_computes.
      eexists; split_and; eauto.
  Qed.

End FixFormat.
