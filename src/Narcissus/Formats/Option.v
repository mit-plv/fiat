Require Import
        Fiat.Common
        Fiat.Computation
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.BaseFormats.

Unset Implicit Arguments.
Section Option.

  Context {sz : nat}.
  Context {S VS VN : Type}.
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

  Definition option_decode'
             (decode_Some : DecodeM (VS * T) T)
             (decode_None : DecodeM (VN * T) T)
             (b' : bool)
    : DecodeM ((VS + VN) * T) T :=
    (fun (b : T) (env : CacheDecode) =>
       If b' Then
          match decode_Some b env with
          | Some (a, b, c) => Some ((inl a, b), c)
          | None => None
          end
          Else
          match decode_None b env with
          | Some (a, b, c) => Some ((inr a, b), c)
          | None => None
          end).

  Lemma option_format_correct'
      {P  : CacheDecode -> Prop}
      {P_invT P_invE : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_invT P /\ P_invE P))
      (Source_Predicate : option S -> Prop)
      (Some_View_Predicate : VS -> Prop)
      (None_View_Predicate : VN -> Prop)
      (viewS : S -> VS -> Prop)
      (viewN : () -> VN -> Prop)
      (b' : bool)
      (predicate :=
         fun a_opt =>
           decides (negb b') (a_opt = None)
           /\ Source_Predicate a_opt)
      (format_Some : FormatM S T)
      (format_None : FormatM () T)
      (decode_Some : DecodeM (VS * T) T)
      (decode_None : DecodeM (VN * T) T)
      (view_format_Some : FormatM VS T)
      (view_format_None : FormatM VN T)
      (decode_Some_pf :
         cache_inv_Property P P_invT
         -> CorrectDecoder
              monoid (fun s => Source_Predicate (Some s))
              Some_View_Predicate
              viewS
              format_Some decode_Some P
              view_format_Some)
      (decode_None_pf :
         cache_inv_Property P P_invE
         -> CorrectDecoder
              monoid
              (fun _ => Source_Predicate None)
              None_View_Predicate
              viewN
              format_None decode_None P
              view_format_None)
  : CorrectDecoder
      monoid
      predicate
      (fun v_opt =>
         match v_opt with
         | inl vs => Some_View_Predicate vs /\ b' = true
         | inr vn => None_View_Predicate vn /\ b' = false
         end)
      (fun s_opt v_opt =>
         match s_opt, v_opt with
         | Some s, inl vs => viewS s vs
         | None, inr vn => viewN () vn
         | _, _ => False
         end)
      (format_option format_Some format_None)
      (option_decode' decode_Some decode_None b')
      P (fun v_opt =>
           match v_opt with
           | inl vs => view_format_Some vs
           | inr vn => view_format_None vn
           end
        ).
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm com_pf.
    unfold format_option in com_pf; computes_to_inv;
      unfold option_decode'; destruct data;
      find_if_inside; unfold predicate in *; simpl in *;
        intuition; try discriminate.
    - eapply H3 in com_pf; destruct_ex;
        subst; intuition eauto; rewrite H6; eauto.
      subst; eexists _, _; eauto.
    - eapply H4 in com_pf; destruct_ex;
        intuition eauto; rewrite H6; eauto.
      subst; eexists _, _; eauto.
  }
  { unfold option_decode'; intros.
    find_if_inside; simpl in *.
    - destruct (decode_Some t env') as [ [ [? ?] ?] | ] eqn : ? ;
        simpl in *; try discriminate; injections; simpl.
      eapply decode_Some_pf in Heqo; intuition eauto.
      destruct_ex; split_and; eexists _, _; intuition eauto.
    - destruct (decode_None t env') as [ [ [? ?] ?] | ] eqn : ? ;
        simpl in *; try discriminate; injections.
      eapply decode_None_pf in Heqo; intuition eauto; destruct_ex;
        intuition eauto; subst.
      destruct_ex; split_and; eexists _, _; intuition eauto.
  }
Qed.

End Option.

Definition option_decode
           {S T}
           {cache : Cache}
           {cacheAddNat : CacheAdd cache nat}
           (monoid : Monoid T)
           (decode_Some : DecodeM (S * T) T)
           (decode_None : DecodeM (() * T) T)
           (b' : bool)
    : DecodeM (option S * T) T :=
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
      {S T}
      {cache : Cache}
      {cacheAddNat : CacheAdd cache nat}
      (monoid : Monoid T)
      {P : CacheDecode -> Prop}
      {P_invT P_invE : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_invT P /\ P_invE P))
      (Some_Predicate : S -> Prop)
      (None_Predicate : Prop)
      (None_View_Predicate : () -> () -> Prop)
      (b' : bool)
      (predicate :=
         fun a_opt =>
           decides (negb b') (a_opt = None)
           /\ match a_opt with
              | Some s => Some_Predicate s
              | None => None_Predicate
              end)
      (format_Some : FormatM S T)
      (format_None : FormatM () T)
      (decode_Some : DecodeM (S * T) T)
      (decode_None : DecodeM (() * T) T)
      (decode_Some_pf :
         cache_inv_Property P P_invT
         -> CorrectDecoder
              monoid
              Some_Predicate
              Some_Predicate
              eq
              format_Some decode_Some P
              format_Some)
      (decode_None_pf :
         cache_inv_Property P P_invE
         -> CorrectDecoder
              monoid
              (fun _ => None_Predicate)
              (fun _ => None_Predicate)
              None_View_Predicate
              format_None decode_None P
              format_None)
  : CorrectDecoder
      monoid
      predicate
      predicate
      eq
      (format_option format_Some format_None)
      (option_decode monoid decode_Some decode_None b')
      P
      (format_option format_Some format_None).
  Proof.
    eapply format_decode_correct_alt.
    2: instantiate (1 := predicate).
    7: {
      eapply injection_decode_correct
        with (inj := fun v =>
                       match v with
                       | inl vs => Some vs
                       | inr _ => None
                       end).
      eapply option_format_correct' with (b'0 := b')
                                         (Source_Predicate :=
                                            fun s => match s with
                                                     | Some s => _ s
                                                     | None => _
                                                     end);
        eauto.
      - simpl; intros.
        instantiate (1 := fun s v => match s with
                                     | Some s => match v with
                                                 | Some vs => s = vs
                                                 | None => False
                                                 end
                                     | None => match v with
                                               | Some vs => False
                                               | None => True
                                               end
                                     end).
        simpl; destruct s; destruct v; eauto.
      - intros.
        unfold predicate; destruct v; destruct b'; intuition eauto;
          simpl; try congruence.
      - intros.
        instantiate (1 := fun v_opt => match v_opt with
                            | Some vs => format_Some vs
                            | _ => format_None ()
                            end); simpl.
        destruct v; eauto.
        destruct u; apply unfold_computes; eauto.
    }
    - unfold flip, pointwise_relation; intros.
      unfold predicate; intuition eauto.
    - unfold flip, pointwise_relation, impl; intros.
        unfold predicate in *; intuition eauto.

    - unfold flip, pointwise_relation; intros; intuition eauto.
      subst; destruct a0; eauto.
      destruct a; destruct a0; intuition; try congruence.
    - unfold flip, pointwise_relation; intros; intuition eauto.
      unfold EquivFormat; intros; reflexivity.
    - unfold flip, pointwise_relation; intros; intuition eauto.
      unfold Compose_Decode, option_decode, option_decode'.
      destruct b'; simpl.
      destruct (decode_Some a a0) as [ [ [? ?] ?] | ]; simpl; eauto.
      destruct (decode_None a a0) as [ [ [? ?] ?] | ]; simpl; eauto.
    - unfold flip, pointwise_relation; intros; intuition eauto.
      unfold EquivFormat; intros.
      unfold format_option; destruct s; simpl.
      reflexivity.
      reflexivity.
  Qed.
