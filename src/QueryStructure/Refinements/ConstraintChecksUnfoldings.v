Require Import List String Ensembles Arith
        Common.ilist ADTNotation.StringBound
        QueryStructureSchema QueryStructure
        ConstraintChecksRefinements.

(* We put all these simplification hints into a distinct file
   so we're not unfolding things all willy-nilly. *)
Arguments Iterate_Decide_Comp _ _ / .
Arguments Iterate_Decide_Comp' _ _ _ _ / .
Arguments Ensemble_BoundedIndex_app_comm_cons  _ _ _ _ _ _ / .
Arguments SatisfiesCrossRelationConstraints  _ _ _ _ _ / .
Arguments BuildQueryStructureConstraints  _ _ _ / .
Arguments BuildQueryStructureConstraints'  _ _ _ _ / .
Arguments BuildQueryStructureConstraints_cons / .
Arguments GetNRelSchemaHeading  _ _ / .
Arguments Ensemble_BoundedIndex_app_comm_cons  _ _ _ _ _ _ / .
Arguments id  _ _ / .

Create HintDb refine_keyconstraints discriminated.
(*Hint Rewrite refine_Any_DecideableSB_True : refine_keyconstraints.*)

Arguments ith_Bounded _ _ _ _ _ _ _ / .
Arguments SatisfiesSchemaConstraints _ _ _ _ / .
Arguments GetUnConstrRelation : simpl never.
Arguments UpdateUnConstrRelation : simpl never.
Arguments replace_BoundedIndex : simpl never.
