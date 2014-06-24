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

Ltac subst_strings :=
  repeat match goal with
           | [ H : string |- _ ] => subst H
           | [ H : BoundedIndex _ |- _ ] => subst H
         end.

Ltac pose_string_ids :=
  subst_strings;
  repeat match goal with
           | |- context [String ?R ?R'] =>
             let str := fresh "StringId" in
             set (String R R') as str in *
           | |- context [ ``(?R) ] =>
             let idx := fresh in
             set ``(R) as fresh in *
         end.

  (* When we insert a tuple into a relation which has another relation has
     a foreign key into, we need to show that we haven't messed up any
     references (which is, of course, trivial. We should bake this into
     our the [QSInsertSpec_refine'] refinement itself by filtering out the
     irrelevant constraints somehow, but for now we can use the following
     tactic to rewrite them away. *)

  Ltac remove_trivial_insertion_constraints :=
          repeat match goal with
          |- context[EnsembleInsert _ (GetUnConstrRelation _ _) ] =>
          match goal with
              AbsR : DropQSConstraints_AbsR ?or ?nr
              |- context [
                     Pick
                       (fun b =>
                          decides b
                                  (forall tup' ,
                           GetUnConstrRelation ?r ?Ridx tup' ->
                           exists tup2,
                             EnsembleInsert ?tup (GetUnConstrRelation ?r ?Ridx') tup2 /\
                             (indexedTuple tup') ?attr = (indexedTuple tup2) ?attr'))] =>
              let neq := fresh in
              assert (Ridx <> Ridx') by (subst_strings; congruence);
              let refine_trivial := fresh in
              assert
                (refine {b' |
                         decides b'
                                 (forall tup',
                                    (GetUnConstrRelation r Ridx) tup' ->
                                    exists
                                      tup2,
                                      EnsembleInsert tup (GetUnConstrRelation r Ridx') tup2 /\
                                      (indexedTuple tup') attr = (indexedTuple tup2) attr')} (ret true))
                as refine_trivial;
                [ let v := fresh in
                  let Comp_v := fresh in
                  intros v Comp_v;
                    apply computes_to_inv in Comp_v;
                    rewrite <- AbsR; subst;
                    repeat rewrite GetRelDropConstraints;
                    let tup' := fresh in
                    let In_tup' := fresh in
                    econstructor; simpl map; simpl; intros tup' In_tup';
                    unfold EnsembleInsert;
                    let H' := fresh in
                    pose proof (@crossConstr _ or Ridx Ridx' tup' neq In_tup') as H';
                      simpl map in *; simpl in *;
                      destruct H' as [? [? ?]]; eauto |
                  subst_strings; setoid_rewrite refine_trivial;
                  clear refine_trivial;
                  pose_string_ids; simplify with monad laws
                ] end end .

Tactic Notation "remove" "trivial" "insertion" "checks" :=
  (* Move all the binds we can outside the exists / computes
   used for abstraction, stopping when we've rewritten
         the bind in [QSInsertSpec]. *)
  repeat
    (apply refine_bind;
     match goal with
       | |- context [Bind (Insert _ into ?R)%QuerySpec _] =>
         apply refine_bind;
         [ reflexivity
         | unfold pointwise_relation; intros ]
       | _ => fail
     end);
       etransitivity;
    [ (* Pull out the relation we're inserting into and then
     rewrite [QSInsertSpec] *)
      match goal with
          H : DropQSConstraints_AbsR _ ?r_n
          |- context [(Insert ?n into ?R)%QuerySpec] =>
          let H' := fresh in
          (* If we try to eapply [QSInsertSpec_UnConstr_refine] directly
                   after we've drilled under a bind, this tactic will fail because
                   typeclass resolution breaks down. Generalizing and applying gets
                   around this problem for reasons unknown. *)
          let H' := fresh in
        pose proof (@QSInsertSpec_UnConstr_refine_opt
                      _ r_n {| bindex := R |} n _ H) as H';
          apply H'
      end
    | cbv beta; simpl schemaConstraints; cbv iota;
      simpl map; simpl app;
      simpl relName in *; simpl schemaHeading in *;
      pose_string_ids; simpl;
      simplify with monad laws;
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
       attempting to remove them. *)
    rewrite refine_bind;
    [ | reflexivity |
      unfold pointwise_relation; intros;
      repeat remove_trivial_insertion_constraints;
      higher_order_1_reflexivity ];
    finish honing
  | ].
