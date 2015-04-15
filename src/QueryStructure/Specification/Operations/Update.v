Require Import Coq.Lists.List Coq.Strings.String Coq.Sets.Ensembles Coq.Arith.Arith
        Fiat.Computation.Core
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.Common.ilist
        Fiat.Common.StringBound
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildADTSig
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Specification.Operations.Mutate.

(* Definitions for updating query structures. *)

(* This update is fairly constrained:
   If the update is consistent with the constraints, it is
   applied to the table,
   OTHERWISE
   No tables are changed. *)
Definition QSUpdate
           (qs : QueryStructureHint)
           (Ridx : _)
           (UpdatedTuples : @Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (UpdateFunction :  (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))) ->
                              (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
: Comp (QueryStructure qsSchemaHint' * list Tuple) :=
  QSMutate qs Ridx (IndexedEnsembleUpdate (GetRelation qsHint Ridx) UpdatedTuples UpdateFunction).

Opaque QSUpdate.

Variable UpdateTuple : forall (attrs: list Attribute) (attr: Attribute),
                         (Component attr -> Component attr) ->
                         @Tuple (BuildHeading attrs) -> @Tuple (BuildHeading attrs).

Notation "a |= b" := (@UpdateTuple _ {|attrName := a; attrType := _|}
                             (fun _ => Build_Component (_::_) b%list)) (at level 80).
Notation "a ++= b" := (@UpdateTuple _ {|attrName := a; attrType := string|}
                             (fun o => Build_Component (_::_) (append (value o) b))) (at level 80).
Notation "a :+= b" := (@UpdateTuple _ {|attrName := a; attrType := list _|}
                             (fun o => Build_Component (_::_) (cons b (value o)))) (at level 80).
Notation "[ a ; .. ; c ]" := (compose a .. (compose c id) ..) : Update_scope.

Delimit Scope Update_scope with Update.
Notation "'Update' b 'from' Ridx 'making' Trans 'where' Ens" :=
  (QSUpdate _ {|bindex := Ridx%comp |} (fun b => Ens) Trans%Update)
    (at level 80) : QuerySpec_scope.
