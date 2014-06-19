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
  simpl map; simpl;
    repeat match goal with
             | |- context [if _ then ret true else ret false] =>
               setoid_rewrite refine_if_bool_eta at 1
             | |- refine (Bind (Pick (fun b => decides b True)) _) _ =>
             etransitivity; [ apply refine_bind;
                              [ apply decides_True
                              | unfold pointwise_relation;
                                intro; higher_order_1_reflexivity ]
                            | rewrite refineEquiv_bind_unit at 1;
                              unfold If_Then_Else ]
             | |- refine (Bind (Pick (fun b' => decides b' (forall _ _ _, True))) _ ) _ =>
               etransitivity;
                 [ apply refine_bind;
                   [ apply decides_3_True
                   | unfold pointwise_relation;
                     intro; higher_order_1_reflexivity ]
                 | rewrite refineEquiv_bind_unit at 1;
                   unfold If_Then_Else ]

    end.

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
                H : DropQSConstraints_AbsR _ ?r_n
                |- context [(Insert ?n into ?R)%QuerySpec] =>
                let H' := fresh in
                (* If we try to eapply [QSInsertSpec_UnConstr_refine] directly
                   after we've drilled under a bind, this tactic will fail because
                   typeclass resolution breaks down. Generalizing and applying gets
                   around this problem for reasons unknown. *)
                      generalize (@QSInsertSpec_UnConstr_refine
                                    _ r_n {|bindex := R |} n) as H';
                        intro H'; apply H';
                        [  simplify_trivial_SatisfiesSchemaConstraints
                         | simplify_trivial_SatisfiesSchemaConstraints
                         | simplify_trivial_SatisfiesSchemaConstraints
                         | simplify_trivial_SatisfiesCrossRelationConstraints;
                           reflexivity
                         | intros;
                           simplify_trivial_SatisfiesCrossRelationConstraints;
                           higher_order_1_reflexivity
                         | eauto ]
            end
  | simplify with monad laws;
    try rewrite <- GetRelDropConstraints;
    repeat match goal with
             | H : DropQSConstraints_AbsR ?qs ?uqs |- _ =>
               rewrite H in *
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
  [ remove trivial insertion checks;
    (* The trivial insertion checks involve the fresh id,
       so we need to drill under the binder before
       attempting to remove them.
     *)
    setoid_rewrite refine_bind;
    [ | reflexivity |
      unfold pointwise_relation; intros;
      repeat remove_trivial_insertion_constraints;
      higher_order_1_reflexivity ];
    finish honing
  | ].
