Require Import
        Coq.omega.Omega
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

Lemma CorrectDecoderEmpty {S T}
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
  unfold CorrectDecoder, empty_Format; split; intros.
  -  eexists s, env'; pose proof (H _ H2); subst; find_if_inside;
      simpl in *; intuition eauto; computes_to_inv; injections.
     rewrite mempty_left; eauto.
     eassumption.
  - find_if_inside; injections; try discriminate;
      simpl in *; intuition eauto.
    eexists; eexists; intuition eauto.
    rewrite mempty_left; reflexivity.
Qed.
