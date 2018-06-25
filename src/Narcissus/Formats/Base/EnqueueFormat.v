Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs.

Section EnqueueFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {cache : Cache}. (* State Type *)
  Context {monoid : Monoid T}. (* T is a monoid *)
  Context {queue : QueueMonoidOpt monoid S}. (* T has an enqueue operation *)

  Definition Enqueue_Format
    : FormatM S T :=
    fun a env => ret (enqueue_opt a mempty, env).

  Definition Enqueue_Decode
    : DecodeM (S * T) T :=
    fun t env =>
      Ifopt dequeue_opt t as st Then Some (st, env) Else None.

  Definition Enqueue_Encode
    : EncodeM S T :=
    fun a env => Some (enqueue_opt a mempty, env).

  (* Lemma CorrectDecoder_Enqueue
    : CorrectDecoder_simpl (Enqueue_Format (decode).
  Proof.
    unfold CorrectDecoder_simpl, FMap_Decode, FMap_Format in *; split; intros.
    { repeat (apply_in_hyp @unfold_computes; destruct_ex; intuition).
      pose proof (g_inverts_f  _ _ _ _ H3 H4).
      rewrite <- unfold_computes in H3.
      eapply H1 in H3; destruct_ex; intuition eauto.
      eexists; rewrite H5; simpl; intuition eauto.
      subst; eauto.
    }
    { apply_in_hyp DecodeBindOpt_inv; destruct_ex; intuition.
      eapply H2 in H3; eauto; injections.
      destruct_ex; eexists; intuition eauto.
      apply unfold_computes.
      eexists; intuition eauto.
    }
  Qed. *)

End EnqueueFormat.
