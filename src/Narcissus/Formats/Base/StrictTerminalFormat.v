Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs.

Section StrictTerminalFormat.

  Context {S : Type}. (* Source type *)
  Context {T : Type}. (* Target type *)
  Context {cache : Cache}. (* State type *)
  Context {monoid : Monoid T}. (* Target type is a monoid *)

  Definition StrictTerminal_Format
    : FormatM S T :=
    fun a env =>
      t <- {t | bin_measure t = 0};
      ret (t, env).

  Definition StrictTerminal_Decode
             (s : S)
    : DecodeM S T :=
    fun t env =>
      If (beq_nat (bin_measure t) 0)
         Then Some (s, env)
         Else None.

  Definition StrictTerminal_Encode
    : EncodeM S T :=
    fun a env => Some (mempty, env).

  Lemma CorrectDecoder_StrictTerminal
        (s : S)
        (Singleton_Format : forall s' env tenv',
            computes_to (StrictTerminal_Format s env) tenv' ->
            s = s')
    : CorrectDecoder_simpl StrictTerminal_Format (StrictTerminal_Decode s).
  Proof.
    unfold CorrectDecoder_simpl, StrictTerminal_Decode, StrictTerminal_Format in *; split; intros.
    { computes_to_inv; injections; subst.
      rewrite H0; simpl.
      eexists; intuition eauto.
      erewrite Singleton_Format with (env := xenv); eauto.
    }
    { destruct (beq_nat (bin_measure bin) 0) eqn: ?; simpl in *;
        try discriminate.
      apply_in_hyp beq_nat_true.
      injections.
      eexists env; intuition eauto.
    }
  Qed.

  Lemma CorrectEncoder_Enqueue
    : CorrectEncoder StrictTerminal_Format StrictTerminal_Encode.
  Proof.
    unfold CorrectEncoder, StrictTerminal_Format, StrictTerminal_Encode;
      split; intros.
    -  injections;
         repeat computes_to_econstructor; eauto using measure_mempty.
    - discriminate.
  Qed.

End StrictTerminalFormat.

Notation "'ϵ'" := (StrictTerminal_Format) (at level 99) : format_scope.
