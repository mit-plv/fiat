Require Import
        Coq.Bool.Bool
        Coq.omega.Omega
        Fiat.Common.DecideableEnsembles
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Common.IterateBoundedIndex
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Formats.Option
        Fiat.Narcissus.Formats.Empty
        Fiat.Narcissus.Formats.Sequence
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.Bool
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Common.Sig.

(* Automation for normalizing formats using the monad laws. *)

Open Scope format_scope.

Locate "++".

Lemma sequence_assoc
      {S T : Type}
      {monoid : Monoid T}
  : forall (format1 format2 format3 : FormatM S T),
    EquivFormat ((format1 ++ format2) ++ format3)%format
                (format1 ++ format2 ++ format3).
Proof.
  unfold sequence_Format, EquivFormat; intros.
  apply refineEquiv_compose_compose.
Qed.

Lemma sequence_mempty
      {S T : Type}
      {m : Monoid T}
  : forall (format : FormatM S T),
    EquivFormat (empty_Format ++ format) format.
Proof.
  unfold sequence_Format, EquivFormat; intros.
  apply refineEquiv_compose_Done.
Qed.

Lemma EquivFormat_ComposeIf
      {S T : Type}
      {monoid : Monoid T}
  : forall (formatT formatT' formatE formatE' : FormatM S T),
    EquivFormat formatT formatT'
    -> EquivFormat formatE formatE'
    -> EquivFormat (Either formatT Or formatE)
                   (Either formatT' Or formatE').
Proof.
  unfold EquivFormat; intros.
  eapply refineEquiv_ComposeIf; eauto.
Qed.

Lemma EquivFormat_UnderSequence
      {S T : Type}
      {monoid : Monoid T}
  : forall (format1 format2 format2' : FormatM S T),
    EquivFormat format2 format2'
    -> EquivFormat (format1 ++ format2)
                   (format1 ++ format2').
Proof.
  unfold EquivFormat; intros.
  eapply refineEquiv_under_compose; eauto.
Qed.

Lemma EquivFormat_If_Then_Else
      {S T : Type}
      {monoid : Monoid T}
  : forall b (formatT formatE format2 : FormatM S T),
    EquivFormat ((If b Then formatT Else formatE) ++ format2)
                (If b Then formatT ++ format2 Else formatE ++ format2).
Proof.
  unfold EquivFormat; intros.
  destruct b; simpl; reflexivity.
Qed.

Lemma EquivFormat_If_Then_Else_Proper
      {S T : Type}
      {monoid : Monoid T}
  : forall (c : bool), Proper (@EquivFormat S T _ ==> @EquivFormat S T _ ==> @EquivFormat S T _) (If_Then_Else c).
Proof.
  unfold Proper, EquivFormat, respectful; simpl; intros.
  destruct c; simpl; eauto.
Qed.

Add Parametric Morphism
    A B
    (cache : Cache)
    (monoid : Monoid B)
    (predicate : A -> Prop)
    rest_predicate
    (decode : B -> CacheDecode -> option (A * B * CacheDecode))
    (decode_inv : CacheDecode -> Prop)
  : (fun format =>
       @CorrectDecoder A B cache monoid predicate
                       rest_predicate format decode decode_inv)
    with signature (EquivFormat --> impl)
      as format_decode_correct_refineEquiv.
Proof.
  unfold EquivFormat, impl, pointwise_relation, CorrectDecoder;
    intuition eauto; intros.
  - eapply H1; eauto; apply H; eauto.
  - eapply H2; eauto.
  - destruct (H2 _ _ _ _ _ _ H0 H3 H4) as [ ? [? [? ?] ] ];
      intuition.
    repeat eexists; intuition eauto; apply H; eauto.
Qed.

Lemma EquivFormat_Projection_Format_Empty_Format
      {S S' T : Type}
      {monoid : Monoid T}
  : forall (format : FormatM S' T) (f : S -> S'), EquivFormat (format ◦ f) ((format ◦ f) ++ empty_Format).
Proof.
  unfold EquivFormat, refineEquiv, sequence_Format, compose, Bind2, empty_Format; split;
    intros ? ?.
  - computes_to_inv; subst.
    destruct v0; simpl; rewrite mempty_right; assumption.
  - computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    simpl.
    destruct v; rewrite mempty_right; computes_to_econstructor.
Qed.



Ltac normalize_step BitStringT :=
  (first [ etransitivity; [apply sequence_assoc with (monoid := BitStringT)| ]
         | etransitivity; [apply sequence_mempty with (monoid := BitStringT) | ]
         | eapply EquivFormat_ComposeIf; intros
         | etransitivity; [apply EquivFormat_If_Then_Else with (monoid := BitStringT) | ]
         | apply EquivFormat_If_Then_Else_Proper
         | eapply (@EquivFormat_UnderSequence _ _ BitStringT)
         | eapply EquivFormat_Projection_Format_Empty_Format]; intros).

Ltac normalize_format :=
  (* Normalize formats by performing algebraic simplification. *)
  match goal with
  | |- CorrectDecoder ?monoid _ _ _ _ _ =>
    intros; eapply format_decode_correct_refineEquiv; unfold flip;
    repeat (normalize_step monoid)
  end.
