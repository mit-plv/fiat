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
