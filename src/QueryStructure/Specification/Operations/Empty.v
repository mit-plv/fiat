Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Sets.Ensembles
        Coq.Arith.Arith
        Fiat.Common.StringBound
        Fiat.Computation.Core
        Fiat.Common.ilist2
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildADTSig
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure.

Local Obligation Tactic := intuition.

Program Definition EmptyRelation (sch : RawSchema) : RawRelation sch :=
  Build_RawRelation sch (Empty_set _) _ _.
Next Obligation.
  destruct (attrConstraints sch); intuition.
Qed.
Next Obligation.
  destruct (tupleConstraints sch); intuition.
Qed.

Fixpoint Build_EmptyRelations {n} (schemas : Vector.t RawSchema n) :
  ilist2 (B := RawRelation) schemas :=
  match schemas with
    | Vector.nil => inil2
    | Vector.cons sch _ schemas' =>
      icons2 (EmptyRelation sch) (Build_EmptyRelations schemas')
  end.

Lemma Build_EmptyRelation_IsEmpty (qsSchema : RawQueryStructureSchema)
  : forall idx,
    ith2 (Build_EmptyRelations (qschemaSchemas qsSchema)) idx
    = EmptyRelation _.
Proof.
  intro.
  destruct qsSchema; simpl in *.
  clear qschemaConstraints.
  induction qschemaSchemas.
  inversion idx.
  generalize dependent qschemaSchemas.
  pattern n, idx; apply Fin.rectS; simpl; intros; eauto.
Qed.

Program Definition QSEmptySpec (qsSchema : QueryStructureSchema) :
  QueryStructure qsSchema :=
  {| rawRels := Build_EmptyRelations (qschemaSchemas qsSchema) |}.
Next Obligation.
  rewrite Build_EmptyRelation_IsEmpty in *; simpl in *;
  destruct (BuildQueryStructureConstraints qsSchema idx idx');
  intuition.
Qed.

Notation "'empty'" :=
  (ret (QSEmptySpec _))
    (at level 80) : QuerySpec_scope.
