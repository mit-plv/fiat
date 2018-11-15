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

Lemma CorrectDecoderEmpty {A B}
  : forall (cache : Cache)
           (monoid : Monoid B)
           (predicate : A -> Prop)
           (rest_predicate : A -> B -> Prop)
           (decode_inv : CacheDecode -> Prop)
           (a : A)
           (b : bool),
    (forall a', predicate a' -> a' = a)
    -> decides b (predicate a)
    -> CorrectDecoder
         monoid
         predicate
         rest_predicate
         empty_Format
         (fun b' ctxD => if b then Some (a, b', ctxD) else None)
         decode_inv.
Proof.
  unfold CorrectDecoder, empty_Format; split; intros.
  -  eexists env'; pose proof (H _ H2); subst; find_if_inside;
      simpl in *; intuition eauto; computes_to_inv; injections.
    rewrite mempty_left; eauto.
    eassumption.
  - find_if_inside; injections; try discriminate;
      simpl in *; intuition eauto.
    eexists; eexists; intuition eauto.
    rewrite mempty_left; reflexivity.
Qed.
