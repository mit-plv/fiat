Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        BuildADTRefinements QueryQSSpecs InsertQSSpecs QueryStructure.

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
  simpl map; (* this shaves off 3-9 seconds in some cases *)
  simpl; try setoid_rewrite decides_True;
  try setoid_rewrite decides_3_True;
  repeat setoid_rewrite refineEquiv_bind_unit;
  unfold If_Then_Else;
  try setoid_rewrite refine_if_bool_eta; reflexivity.

Tactic Notation "remove" "trivial" "insertion" "checks" :=
  (* Move all the binds we can outside the exists / computes
   used for abstraction, stopping when we've rewritten
         the bind in [QSInsertSpec]. *)
      repeat
        (setoid_rewrite refineEquiv_pick_ex_computes_to_bind_and;
         match goal with
           | |- context [(Insert _ into ?R)%QuerySpec] => idtac
           | _ => fail
         end);
  etransitivity;
  [ (* drill under the binds so that we can rewrite [QSInsertSpec]
     (we can't use setoid_rewriting because there's a 'deep metavariable'
     *)
    repeat (apply refine_bind;
            [ reflexivity
            | unfold pointwise_relation; intros] );
    (* Pull out the relation we're inserting into and then
     rewrite [QSInsertSpec] *)
            match goal with
                H : DropQSConstraints_SiR _ ?r_n
                |- context [(Insert ?n into ?R)%QuerySpec] =>
                eapply (@QSInsertSpec_UnConstr_refine
                          _ r_n {|bindex := R |} n)
            end;
            (* try to discharge the trivial constraints *)
            [  simplify_trivial_SatisfiesSchemaConstraints
             | simplify_trivial_SatisfiesSchemaConstraints
             | simplify_trivial_SatisfiesSchemaConstraints
             | simplify_trivial_SatisfiesCrossRelationConstraints
             | simplify_trivial_SatisfiesCrossRelationConstraints
             | eauto ]
  | simplify with monad laws;
    try rewrite <- GetRelDropConstraints;
    repeat match goal with
             | H : DropQSConstraints_SiR ?qs ?uqs |- _ =>
               rewrite H in *; clear qs H
           end
    ].

Tactic Notation "Split" "Constraint" "Checks" :=
  repeat (let b := match goal with
                     | [ |- context[if ?X then _ else _] ] => constr:(X)
                     | [ H : context[if ?X then _ else _] |- _ ]=> constr:(X)
                   end in
          let b_eq := fresh in
          eapply (@refine_if _ _ b); intros b_eq;
          simpl in *; repeat rewrite b_eq; simpl).

Tactic Notation "implement" "failed" "insert" :=
  repeat (rewrite refine_pick_val, refineEquiv_bind_unit; eauto);
  reflexivity.

Tactic Notation "drop" "constraints" "from" "insert" constr(methname) :=
  hone method methname;
  [ remove trivial insertion checks ;
    repeat remove_trivial_insertion_constraints;
    finish honing | ].
