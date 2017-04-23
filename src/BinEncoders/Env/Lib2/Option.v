Require Import
        Fiat.Common
        Fiat.Computation
        Fiat.Computation.Notations
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts.

Unset Implicit Arguments.
Section Option.

  Context {sz : nat}.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.

  Definition encode_option_Spec
             (encode_Some : A -> CacheEncode -> Comp (B * CacheEncode))
             (encode_None : () -> CacheEncode -> Comp (B * CacheEncode))
             (a_opt : option A)
    := If_Opt_Then_Else a_opt encode_Some (encode_None ()).

  Lemma option_encode_correct
      {P  : CacheDecode -> Prop}
      {P_invT P_invE : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_invT P /\ P_invE P))
      (predicate_Some : A -> Prop)
      (predicate_None : () -> Prop)
      (b' : bool)
      (predicate :=
         fun a_opt =>
           decides (negb b') (a_opt = None)
           /\ match a_opt with
              | Some a => predicate_Some a
              | None => predicate_None ()
              end)
      (predicate_rest_Some : A -> B -> Prop)
      (predicate_rest_None : () -> B -> Prop)
      (predicate_rest :=
         fun a_opt =>
           match a_opt with
           | Some a => predicate_rest_Some a
           | None => predicate_rest_None ()
           end)
      (encode_Some : A -> CacheEncode -> Comp (B * CacheEncode))
      (decode_Some : B -> CacheDecode -> option (A * B * CacheDecode))
      (encode_None : () -> CacheEncode -> Comp (B * CacheEncode))
      (decode_None : B -> CacheDecode -> option (() * B * CacheDecode))
      (decode_Some_pf :
         cache_inv_Property P P_invT
         -> encode_decode_correct_f
              cache transformer predicate_Some predicate_rest_Some
              encode_Some decode_Some P)
      (decode_None_pf :
         cache_inv_Property P P_invE
         -> encode_decode_correct_f
              cache transformer predicate_None predicate_rest_None
              encode_None decode_None P)
  : encode_decode_correct_f
      cache transformer
      predicate
      predicate_rest
      (encode_option_Spec encode_Some encode_None)%comp
      (fun (b : B) (env : CacheDecode) =>
         If b' Then
            match decode_Some b env with
            | Some (a, b, c) => Some (Some a, b, c)
            | None => None
            end
            Else
            match decode_None b env with
            | Some (a, b, c) => Some (None, b, c)
            | None => None
            end
      ) P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold encode_option_Spec in com_pf; computes_to_inv;
      destruct data;
      find_if_inside; unfold predicate in *; simpl in *;
        intuition; try discriminate.
    - eapply H3 in com_pf; destruct_ex;
        intuition eauto; rewrite H6; eauto.
    - eapply H4 in com_pf; destruct_ex;
        intuition eauto; rewrite H6; eauto.
  }
  { intros.
    find_if_inside; simpl in *.
    - destruct (decode_Some bin env') as [ [ [? ?] ?] | ] eqn : ? ;
        simpl in *; try discriminate; injections; simpl.
      eapply decode_Some_pf in Heqo; intuition eauto.
      destruct_ex; intuition; subst.
      eexists _; eexists _; unfold predicate; intuition eauto.
      discriminate.
    - destruct (decode_None bin env') as [ [ [? ?] ?] | ] eqn : ? ;
        simpl in *; try discriminate; injections; destruct u.
      eapply decode_None_pf in Heqo; intuition eauto; destruct_ex;
        intuition eauto; subst.
      eexists _; eexists _; unfold predicate; intuition eauto.
  }
Qed.

End Option.
