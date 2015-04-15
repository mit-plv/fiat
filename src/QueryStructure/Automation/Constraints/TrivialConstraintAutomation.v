Require Export Fiat.QueryStructure.Specification.Representation.QueryStructureNotations Fiat.QueryStructure.Specification.Operations.Query.
Require Import Coq.Lists.List Coq.Arith.Compare_dec Coq.Bool.Bool Coq.Strings.String
        Fiat.Common.BoolFacts
        Fiat.Common.List.PermutationFacts
        Fiat.Common.List.ListMorphisms
        Fiat.QueryStructure.Specification.Operations.FlattenCompList
        Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.List.ListFacts
        Fiat.Common.LogicFacts
        Fiat.Common.DecideableEnsembles
        Fiat.QueryStructure.Specification.Constraints.tupleAgree
        Fiat.QueryStructure.Specification.Operations.Mutate
        Fiat.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements.

Ltac simplify_trivial_SatisfiesSchemaConstraints :=
  simpl;
  try rewrite refine_tupleAgree_refl_True;
  try setoid_rewrite decides_True;
  try setoid_rewrite decides_2_True; reflexivity.

Ltac simplify_trivial_SatisfiesCrossRelationConstraints :=
  simpl map; simpl;
    repeat match goal with
             | |- context [if _ then ret true else ret false] =>
               setoid_rewrite refine_if_bool_eta at 1
             | |- refine (Bind (Pick (fun b => decides b True)) _) _ =>
             etransitivity; [ apply refine_bind;
                              [ apply decides_True
                              | unfold pointwise_relation;
                                intro; higher_order_reflexivity ]
                            | rewrite refineEquiv_bind_unit at 1;
                              unfold If_Then_Else ]
             | |- refine (Bind (Pick (fun b' => decides b' (forall _ _ _, True))) _ ) _ =>
               etransitivity;
                 [ apply refine_bind;
                   [ apply decides_3_True
                   | unfold pointwise_relation;
                     intro; higher_order_reflexivity ]
                 | rewrite refineEquiv_bind_unit at 1;
                   unfold If_Then_Else ]

    end.
