Require Import
        Coq.ZArith.ZArith
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Computation.Refinements.General
        Fiat.Narcissus.BaseFormats.

Definition empty_Format
           {S T : Type}
           {monoid : Monoid T}
           {cache : Cache}
  : FormatM S T := fun s ce => ret (mempty, ce).

Lemma ExtractViewFrom {S V T}
  : forall (cache : Cache)
           (monoid : Monoid T)
           (Source_Predicate : S -> Prop)
           (View_Predicate : V -> Prop)
           (view : S -> V -> Prop)
           (View_Format : FormatM V T)
           (decode_inv : CacheDecode -> Prop)
           (v : V)
           (v_OK : View_Predicate v),
    (forall s', Source_Predicate s' ->
                view s' v)
    -> (forall env,
           View_Format v env ∋ (mempty, env))
    -> CorrectDecoder
         monoid
         Source_Predicate
         View_Predicate
         view
         empty_Format
         (fun t' ctxD => Some (v, t', ctxD))
         decode_inv
         View_Format.
Proof.
  unfold CorrectDecoder; split; intros.
  -  eexists v, env'; pose proof (H _ H2); subst.
     unfold empty_Format in H3; computes_to_inv;
       injections.
     intuition eauto.
     rewrite mempty_left; eauto.
  - injections.
    intuition eauto.
    eexists mempty, _; intuition eauto.
    rewrite mempty_left; reflexivity.
Qed.

Corollary CorrectDecoderEmpty {S T}
  : forall (cache : Cache)
           (monoid : Monoid T)
           (Source_Predicate : S -> Prop)
           (decode_inv : CacheDecode -> Prop)
           (s : S)
           (b : bool),
    (forall s', Source_Predicate s' -> s' = s)
    -> decides b (Source_Predicate s)
    -> CorrectDecoder
         monoid
         Source_Predicate
         Source_Predicate
         eq
         empty_Format
         (fun t' ctxD => if b then Some (s, t', ctxD) else None)
         decode_inv
         empty_Format.
Proof.
  intros.
  find_if_inside.
  - eapply ExtractViewFrom; eauto; unfold empty_Format; eauto.
  - unfold CorrectDecoder, empty_Format; split; intros.
    + exfalso; eapply H0.
      rewrite <- (H _ H2); eassumption.
    + discriminate.
Qed.

Lemma ExtractViewFromRefined {S V T}
  : forall (cache : Cache)
           (monoid : Monoid T)
           (Source_Predicate : S -> Prop)
           (View_Predicate : V -> Prop)
           (view : S -> V -> Prop)
           (format : FormatM S T)
           (decode_inv : CacheDecode -> Prop)
           (v : V)
           (v_OK : View_Predicate v),
    (forall s', Source_Predicate s' ->
                view s' v)
    -> CorrectRefinedDecoder
         monoid
         Source_Predicate
         View_Predicate
         view
         format
         empty_Format
         (fun t' ctxD => Some (v, t', ctxD))
         decode_inv
         empty_Format.
Proof.
  intros; eapply ExtractViewFrom; eauto.
    intros; apply unfold_computes; intros.
    intuition.
    unfold empty_Format; apply unfold_computes; eauto.
Qed.
