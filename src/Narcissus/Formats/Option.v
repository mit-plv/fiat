Require Import
        Fiat.Common
        Fiat.Computation
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts.

Unset Implicit Arguments.
Section Option.

  Context {sz : nat}.
  Context {S : Type}.
  Context {T : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid T}.

  Definition format_option
             (format_Some : FormatM S T)
             (format_None : FormatM () T)
    : FormatM (option S) T :=
    fun a_opt => If_Opt_Then_Else a_opt format_Some (format_None ()).

  Definition option_encode
             (encode_Some : EncodeM S T)
             (encode_None : EncodeM () T)
    : EncodeM (option S) T :=
    fun a_opt => If_Opt_Then_Else a_opt encode_Some (encode_None ()).

  Definition option_decode
             (decode_Some : DecodeM (S * T) T)
             (decode_None : DecodeM (() * T) T)
             (b' : bool)
    : DecodeM ((option S) * T) T :=
    (fun (b : T) (env : CacheDecode) =>
       If b' Then
          match decode_Some b env with
          | Some (a, b, c) => Some ((Some a, b), c)
          | None => None
          end
          Else
          match decode_None b env with
          | Some (a, b, c) => Some ((None, b), c)
          | None => None
          end).

  Lemma option_format_correct
      {P  : CacheDecode -> Prop}
      {P_invT P_invE : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_invT P /\ P_invE P))
      (predicate_Some : S -> Prop)
      (predicate_None : () -> Prop)
      (b' : bool)
      (predicate :=
         fun a_opt =>
           decides (negb b') (a_opt = None)
           /\ match a_opt with
              | Some a => predicate_Some a
              | None => predicate_None ()
              end)
      (predicate_rest_Some : S -> T -> Prop)
      (predicate_rest_None : () -> T -> Prop)
      (predicate_rest :=
         fun a_opt =>
           match a_opt with
           | Some a => predicate_rest_Some a
           | None => predicate_rest_None ()
           end)
      (format_Some : FormatM S T)
      (format_None : FormatM () T)
      (decode_Some : DecodeM (S * T) T)
      (decode_None : DecodeM (() * T) T)
      (decode_Some_pf :
         cache_inv_Property P P_invT
         -> CorrectDecoder
              monoid predicate_Some predicate_rest_Some
              format_Some decode_Some P)
      (decode_None_pf :
         cache_inv_Property P P_invE
         -> CorrectDecoder
              monoid predicate_None predicate_rest_None
              format_None decode_None P)
  : CorrectDecoder
      monoid
      predicate
      predicate_rest
      (format_option format_Some format_None)%comp
      (option_decode decode_Some decode_None b')
 P.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold format_option in com_pf; computes_to_inv;
      unfold option_decode; destruct data;
      find_if_inside; unfold predicate in *; simpl in *;
        intuition; try discriminate.
    - eapply H3 in com_pf; destruct_ex;
        intuition eauto; rewrite H6; eauto.
    - eapply H4 in com_pf; destruct_ex;
        intuition eauto; rewrite H6; eauto.
  }
  { unfold option_decode; intros.
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
