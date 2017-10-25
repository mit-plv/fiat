Require Import
        Fiat.Computation
        Fiat.Common.DecideableEnsembles
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Notations.

Section ComplementaryFormats.

  Variable A : Type.  (* Source Type, i.e. in-memory data *)
  Variable NA : Type. (* Not Source Type used to generate invalid target data *)
  Variable B : Type.  (* Target Type, usually ByteStrings *)
  Context {monoid_B : Monoid B}. (* Target type needs to be a monoid. *)

  Variable store : Cache. (* Store Type *)
  Variable Nstore : Cache. (* Not Store Type *)

  Variable Format : @FormatM A B store. (* The source format *)
  Variable NFormat : @FormatM NA B Nstore. (* The format of invalid bytestrings *)
  Variable NA_OK : NA -> Prop. (* Not source data property that ensures it will
                                generate invalid bytestrings *)
  
  Notation "a ∋ b" := (@computes_to _ a b) (at level 90).
  Notation "a ∌ b" := (~ @computes_to _ a b) (at level 90).

  (* To start, we define the set of invalid bytestrings for a format. *)
  Definition ComplementaryFormat
             (decode_inv : @CacheDecode store -> Prop) :=
    forall na b ns ns',
      NFormat na ns ∋ (b, ns') (* If a bytestring is in the invalid format *)
      -> NA_OK na              (* and the data was not okay *)
      -> forall a s s' s'',
        decode_inv s'' (* The binary string could not have been produced by *)
        -> Equiv s s'' (* an encoder that was started in a state equivalent to a *)
        -> Format a s ∌ (b, s')  (* valid decoder state (this should be the empty state) *).
        
  (* Now, we want to be able to derive conditions on the invalid format that ensure
     it is complementary. *)
  Definition CorrectDecoderComplement
    : forall (predicate : A -> Prop)
             (predicate_OK :
                forall a s b s',
                  Format a s ∋ (b, s')
                  -> predicate a)
             (rest_predicate : A -> B -> Prop := fun _ _ => True)
             (decode : @DecodeM A B store)
             (decode_inv : CacheDecode -> Prop),
      CorrectDecoder _ predicate rest_predicate Format decode decode_inv
      -> (forall na b ns ns',
             NA_OK na
             -> NFormat na ns ∋ (b, ns')
             -> forall s b',
               decode_inv s
               -> decode (mappend b b') s = None)
      -> ComplementaryFormat decode_inv.
  Proof.
    unfold ComplementaryFormat, CorrectDecoder; intros.
    intro.
    eapply H0 in H1; eauto.
    exact (@CorrectDecoderNone _ _ _ _ _ _ _ _ _ H _ mempty _ H3 H1 _ _ _ H4 (predicate_OK _ _ _ _ H5) I H5).
  Qed.

End ComplementaryFormats.
