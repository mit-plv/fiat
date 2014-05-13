Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        QueryQSSpecs InsertQSSpecs QueryStructure.

Lemma tupleAgree_refl :
  forall (h : Heading)
         (tup : @Tuple h)
         (attrlist : list (Attributes h)),
    tupleAgree tup tup attrlist.
Proof.
  unfold tupleAgree; auto.
Qed.

Lemma refine_tupleAgree_refl_True :
  forall (h : Heading)
         (tup : @Tuple h)
         (attrlist attrlist' : list (Attributes h)),
    refine {b |
            decides b (tupleAgree tup tup attrlist'
                       -> tupleAgree tup tup attrlist)}
           (ret true).
Proof.
  unfold refine; intros; inversion_by computes_to_inv.
  subst; econstructor; simpl; auto using tupleAgree_refl.
Qed.

Ltac simplify_trivial_SatisfiesSchemaConstraints :=
  simpl;
  try rewrite refine_tupleAgree_refl_True;
  try setoid_rewrite decides_True;
  try setoid_rewrite decides_2_True; reflexivity.

Ltac simplify_trivial_SatisfiesCrossRelationConstraints :=
  simpl; try setoid_rewrite decides_True;
  try setoid_rewrite decides_3_True;
  repeat setoid_rewrite refineEquiv_bind_unit;
  unfold If_Then_Else;
  try setoid_rewrite refine_if_bool_eta; reflexivity.

Tactic Notation "remove" "trivial" "insertion" "checks" :=
  intros; setoid_rewrite QSInsertSpec_UnConstr_refine; eauto;
  [ | simplify_trivial_SatisfiesSchemaConstraints
    | simplify_trivial_SatisfiesSchemaConstraints
    | simplify_trivial_SatisfiesSchemaConstraints
    | simplify_trivial_SatisfiesCrossRelationConstraints
    | simplify_trivial_SatisfiesCrossRelationConstraints ];
  repeat setoid_rewrite refineEquiv_bind_unit;
  repeat setoid_rewrite refineEquiv_bind_bind;
  repeat setoid_rewrite refineEquiv_bind_unit.

Tactic Notation "Split" "Constraint" "Checks" :=
  let b := match goal with
             | [ |- context[if ?X then _ else _] ] => constr:(X)
             | [ H : context[if ?X then _ else _] |- _ ]=> constr:(X)
           end in
  let b_eq := fresh in
  eapply (@refine_if _ _ b); intros b_eq;
  repeat setoid_rewrite b_eq;
  repeat rewrite b_eq.

Tactic Notation "implement" "failed" "insert" :=
  repeat (rewrite refine_pick_val, refineEquiv_bind_unit; eauto);
  reflexivity.
