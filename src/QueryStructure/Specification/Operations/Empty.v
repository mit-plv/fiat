Require Import Coq.Lists.List Coq.Strings.String Coq.Sets.Ensembles Coq.Arith.Arith
        ADTSynthesis.Computation.Core
        ADTSynthesis.ADT.ADTSig ADTSynthesis.ADT.Core
        ADTSynthesis.Common.ilist ADTSynthesis.Common.StringBound
        ADTSynthesis.ADTNotation.BuildADT ADTSynthesis.ADTNotation.BuildADTSig
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema  ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure.

Local Obligation Tactic := intuition.

Program Definition EmptyRelation (sch : Schema) : Relation sch :=
  Build_Relation sch (fun T : @IndexedTuple (schemaHeading sch) => False) _ _.
Next Obligation.
  destruct (attrConstraints sch); intuition.
Qed.
Next Obligation.
  destruct (tupleConstraints sch); intuition.
Qed.

Fixpoint Build_EmptyRelations (schemas : list NamedSchema) :
  ilist (fun ns : NamedSchema => Relation (relSchema ns))
        schemas :=
  match schemas with
    | [] => inil _
    | sch :: schemas' =>
      icons _ (EmptyRelation (relSchema sch)) (Build_EmptyRelations schemas')
  end.

Lemma Build_EmptyRelation_IsEmpty qsSchema :
  forall idx,
    ith_Bounded relName (Build_EmptyRelations qsSchema) idx
    = EmptyRelation _.
Proof.
  intro.
  eapply (ith_Bounded_ind (B' := fun _ => unit)
            _
            (fun As idx il a b b' => b = EmptyRelation (relSchema a))
         idx (Build_EmptyRelations qsSchema) tt).
  destruct idx as [idx [n nth_n] ]; simpl in *; subst.
  revert qsSchema nth_n;
    induction n; destruct qsSchema; simpl; eauto;
    intros; icons_invert; simpl; auto.
  unfold Some_Dep_Option; simpl; eapply IHn.
Qed.

Program Definition QSEmptySpec (qsSchema : QueryStructureSchema) :
  QueryStructure qsSchema :=
  {| rels := Build_EmptyRelations (qschemaSchemas qsSchema) |}.
Next Obligation.
  rewrite Build_EmptyRelation_IsEmpty in *; simpl in *;
  destruct (BuildQueryStructureConstraints qsSchema idx idx');
  intuition.
Qed.


Notation "'empty'" :=
  (ret (QSEmptySpec qsSchemaHint))
    (at level 80) : QuerySpec_scope.
