Require Import
        Coq.Bool.Bool
        Coq.ZArith.ZArith
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
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Common.Sig.

Require Export Fiat.Narcissus.Common.EquivFormat.

(* Automation for normalizing formats using the monad laws. *)

Open Scope format_scope.

Ltac normalize_step BitStringT :=
  (first
     [ (* Always solve the goal if the first format is an evar *)
       match goal with
         |- EquivFormat ?z ?x =>
         is_evar z; apply EquivFormat_reflexive
       end
     | eapply EquivFormat_trans; [ apply sequence_assoc |  ]
     | eapply EquivFormat_trans; [ apply sequence_mempty with (monoid := BitStringT) |  ]
     | eapply EquivFormat_ComposeIf; intros
     | eapply EquivFormat_trans; [ apply EquivFormat_If_Then_Else with (monoid := BitStringT) |  ]
     | apply EquivFormat_If_Then_Else_Proper
     | eapply EquivFormat_UnderSequence';
       [ repeat (eapply EquivFormat_trans; [ eapply EquivFormat_compose_map |  ]); apply EquivFormat_reflexive
       |  ]
     | eapply EquivFormat_Projection_Format_Empty_Format';
       [ repeat eapply EquivFormat_compose_map; apply EquivFormat_reflexive ]
     | unfold EquivFormat; intros; reflexivity ]); intros.

Ltac normalize_format :=
  (* Normalize formats by performing algebraic simplification. *)
  intros;
  repeat progress
         match goal with
         | |- CorrectDecoder ?monoid _ _ _ _ _ _ _ =>
           intros; eapply format_decode_correct_refineEquiv; unfold flip;
           repeat (normalize_step monoid)
         | |- Prefix_Format ?monoid _ _ =>
           intros; eapply prefix_format_refineEquiv; unfold flip;
           repeat (normalize_step monoid)
         | |- CorrectRefinedDecoder ?monoid _ _ _ _ _ _ _ _ =>
           intros; eapply format_decode_refined_correct_refineEquiv; unfold flip;
           repeat (normalize_step monoid)
         end.
