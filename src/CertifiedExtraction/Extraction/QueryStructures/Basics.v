Require Export Fiat.Computation.Notations.
Require Export Fiat.ADT.Core Fiat.Computation.Core.
Require Export Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

Require Export Bedrock.Platform.Facade.examples.TuplesF.
Require Export CertifiedExtraction.Utils.
Require Export Bedrock.Memory.

Notation BedrockWElement := (@TuplesF.IndexedElement (GenericTuple W)).
Notation BedrockWBag := (@TuplesF.IndexedEnsemble (GenericTuple W)).

Fixpoint MakeVectorOfW N : Vector.t Type N :=
  match N with
  | O => Vector.nil Type
  | S x => Vector.cons Type W x (MakeVectorOfW x)
  end.

Definition MakeWordHeading (N: nat) :=
  {| NumAttr := N;
     AttrList := MakeVectorOfW N |}.

Notation FiatWTuple N := (@RawTuple (MakeWordHeading N)).
Notation FiatWElement N := (@IndexedEnsembles.IndexedElement (FiatWTuple N)).
Notation FiatWBag N := (@IndexedEnsembles.IndexedEnsemble (FiatWTuple N)).

Lemma MakeWordHeading_allWords :
  forall {N} (idx: Fin.t N),
    Domain (MakeWordHeading N) idx = W.
Proof.
  unfold MakeWordHeading; induction idx.
  - reflexivity.
  - unfold Domain in *; simpl in *; assumption.
Defined.
