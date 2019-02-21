Require Import
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs.

Unset Implicit Arguments.

Section Bool.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Definition format_bool (b : bool) (ctx : CacheFormat) :=
    ret (enqueue_opt b mempty, addE ctx 1).

  Definition decode_bool (b : B) (ctx : CacheDecode) : option (bool * B * CacheDecode) :=
    Ifopt dequeue_opt b as decoded Then Some (decoded, addD ctx 1) Else None.

  Theorem bool_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      CorrectDecoder monoid (fun _ => True)
                     (fun _ => True)
                     eq
                     format_bool decode_bool P format_bool.
  Proof.
    unfold CorrectDecoder, format_bool, decode_bool; split.
    - intros env env' xenv w w' ext ? Eeq _ Penc.
      computes_to_inv; injections.
      unfold If_Opt_Then_Else.
      erewrite dequeue_mappend_opt;
      try apply dequeue_head_opt.
      rewrite mempty_left.
      injections; eexists _, _; split; intuition eauto using add_correct.
    - intros;
        destruct (dequeue_opt t) as [ [? ?] | ] eqn: ? ;
        simpl in *; try discriminate; injections; intuition.
     eexists _, _; repeat split.
     eapply dequeue_opt_inj; eauto.
     rewrite <- (mempty_left t') at -1;
       auto using dequeue_mappend_opt, dequeue_head_opt.
     apply add_correct; eauto.
  Qed.

End Bool.
