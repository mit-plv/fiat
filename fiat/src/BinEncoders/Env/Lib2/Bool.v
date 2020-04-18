Require Import
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.BinEncoders.Env.Common.Specs.

Unset Implicit Arguments.

Section Bool.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  Definition encode_bool_Spec (b : bool) (ctx : CacheEncode) :=
    ret (transform_push_opt b transform_id, addE ctx 1).

  Definition decode_bool (b : B) (ctx : CacheDecode) : option (bool * B * CacheDecode) :=
    Ifopt transform_pop_opt b as decoded Then Some (decoded, addD ctx 1) Else None.

  Theorem bool_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      encode_decode_correct_f cache transformer (fun _ => True)
                              (fun _ _ => True)
                              encode_bool_Spec decode_bool P.
  Proof.
    unfold encode_decode_correct_f, encode_bool_Spec, decode_bool; split.
    - intros env env' xenv w w' ext Eeq _ _ Penc.
      computes_to_inv; injections.
      rewrite transform_push_step_opt, transform_push_pop_opt; simpl.
      rewrite transform_id_left.
      injections; eexists; split; eauto using add_correct.
    -intros;
       destruct (transform_pop_opt bin) as [ [? ?] | ] eqn: ? ;
       simpl in *; try discriminate; injections; intuition.
     eexists; eexists; repeat split.
     setoid_rewrite transform_push_step_opt.
     rewrite transform_id_left.
     eapply transform_pop_opt_inj; eauto.
     rewrite transform_push_pop_opt; reflexivity.
     apply add_correct; eauto.
  Qed.

End Bool.
