Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs.

Section LaxTerminalFormat.

  Context {S : Type}. (* Source type *)
  Context {T : Type}. (* Target type *)
  Context {cache : Cache}. (* State type *)
  Context {monoid : Monoid T}. (* Target type is a monoid *)

  Definition LaxTerminal_Format
    : FormatM (S * T) T :=
    fun st env => ret (snd st, env).

  Definition LaxTerminal_Decode
             (s : S)
    : DecodeM (S * T) T :=
    fun t env => Some (s, t, env).

  Definition LaxTerminal_Encode
    : EncodeM (S * T) T :=
    fun st env => Some (snd st, env).

  Lemma CorrectDecoder_LaxTerminal
        (s : S)
        (Singleton_Format : forall s' env tenv',
            LaxTerminal_Format s' env ∋ tenv' ->
            s = fst s')
    : CorrectDecoder_simpl LaxTerminal_Format (LaxTerminal_Decode s).
  Proof.
    unfold CorrectDecoder_simpl, LaxTerminal_Decode, LaxTerminal_Format in *; split; intros.
    { computes_to_inv; injections; subst.
      destruct data; eexists; simpl; intuition eauto.
      erewrite Singleton_Format with (s' := (s0, t)) (env := xenv); eauto.
    }
    { injections.
      eexists env; intuition eauto.
    }
  Qed.

  Lemma CorrectEncoder_LaxTerminal
    : CorrectEncoder LaxTerminal_Format LaxTerminal_Encode.
  Proof.
    unfold CorrectEncoder, LaxTerminal_Format, LaxTerminal_Encode;
      split; intros.
    -  injections;
         repeat computes_to_econstructor; eauto using measure_mempty.
    - discriminate.
  Qed.

End LaxTerminalFormat.

Notation "'?*'" := (LaxTerminal_Format) (at level 99) : format_scope.
