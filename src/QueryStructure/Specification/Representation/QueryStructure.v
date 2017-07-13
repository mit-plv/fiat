Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Logic.FunctionalExtensionality
        Coq.Sets.Ensembles
        Coq.Arith.Arith
        Fiat.Computation.Core
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.Common.StringBound
        Fiat.Common.ilist2
        Fiat.Common.ilist
        Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildADTSig
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.Schema
        Fiat.QueryStructure.Specification.Representation.Relation
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema.

Section BuildQueryStructureConstraints.
  (* Query Structures maintain a set of constraints that enforce
     cross-relation data integrity. Query Structure Schemas encode
     these as a list of dependent products, which
     [BuildQueryStructureConstraints] uses to build the actual constraints.
   *)

  Local Obligation Tactic := intros.

  (* [BuildQueryStructureConstraints_cons] searches the *)

  Program Definition BuildQueryStructureConstraints_cons
          {n}
          (namedSchemas : Vector.t RawSchema n)
          (constr : sigT (crossRelationProdR namedSchemas))
          (constraints :
             list (sigT (crossRelationProdR namedSchemas)))
          (idx idx' : _)
          (HInd : option (crossRelationR namedSchemas idx idx'))
    : option (crossRelationR namedSchemas idx idx')
    :=
      if (fin_eq_dec idx (fst (projT1 constr))) then
        if (fin_eq_dec idx' (snd (projT1 constr))) then
          _
        else HInd
      else HInd.
  Next Obligation.
    destruct constr; simpl in *.
    (* No need to check if the indices are in the list of Relations, because
     they are Bounded Strings. *)
    unfold crossRelationR, GetNRelSchemaHeading, GetNRelSchema; simpl.
    rewrite H, H0;  exact (Some c).
  Defined.

  Fixpoint BuildQueryStructureConstraints'
           {n}
           (namedSchemas : Vector.t RawSchema n)
           (constraints :
              list (sigT (crossRelationProdR namedSchemas)))
           {struct constraints}
    : forall (idx idx' : _), option (crossRelationR namedSchemas idx idx') :=
    match constraints with
    | idx'' :: constraints' =>
      fun idx idx' => @BuildQueryStructureConstraints_cons _
                                                           namedSchemas idx'' constraints' idx idx'
                                                           (BuildQueryStructureConstraints' constraints' idx idx')
    | nil => fun _ _ => None
    end.

  Definition BuildQueryStructureConstraints qsSchema :=
    BuildQueryStructureConstraints' (qschemaConstraints qsSchema).

End BuildQueryStructureConstraints.

(* A Query Structure is a collection of relations
   (described by a proposition) which satisfy the
   schema and the cross-relation constraints. *)

Record RawQueryStructure (QSSchema : RawQueryStructureSchema) :=
  { rawRels : ilist2 (B := RawRelation) (qschemaSchemas QSSchema);
    crossConstr :
      forall (idx idx' : _),
        match (BuildQueryStructureConstraints QSSchema idx idx') with
        | Some CrossConstr =>
          forall (tup : @IndexedRawTuple (GetNRelSchemaHeading (qschemaSchemas QSSchema) idx)),
            idx <> idx' ->
            (* These are cross-relation constraints which only need to be
           enforced on distinct relations. *)
            (rawRel (ith2 rawRels idx )) tup ->
            CrossConstr (indexedElement tup) (rawRel (ith2 rawRels idx'))
        | None => True
        end
  }.

Definition QueryStructure (QSSchema : QueryStructureSchema) := RawQueryStructure QSSchema.

(* Notation "t ! R" := (rels t R%string): QueryStructure_scope. *)

(* This typeclass allows our method definitions to infer the
   the QueryStructure [r] they are called with. *)

(* Class QueryStructureSchemaHint :=
  { qsSchemaHint : QueryStructureSchema
  }.

Class QueryStructureHint :=
  { qsSchemaHint' : QueryStructureSchema;
    qsHint :> @QueryStructure qsSchemaHint'
  }. *)

(*Notation "'query' id ( r : 'rep' , x : dom ) : cod := bod" :=
  (Build_methDef {| methID := id; methDom := dom; methCod := cod |}
                 (fun (r : rep) x =>
                    let _ := {| codHint := cod |} in
                    queryRes <- bod%QuerySpec;
                  ret (r, queryRes)))%comp
                                     (no associativity, id at level 0, x at level 0, dom at level 0,
                                      r at level 0, cod at level 0, only parsing,
                                      at level 94, format "'query'  id  (  r  : 'rep'  ,  x  :  dom )  :  cod  :=  '[  '   bod ']' " ) :
    queryDef_scope.

Notation "'update' id ( r : 'rep' , x : dom ) : cod := bod" :=
  (Build_methDef {| methID := id; methDom := dom; methCod := cod |}
                 (fun (r : rep) x =>
                    bod%QuerySpec))
    (no associativity, id at level 0, x at level 0, dom at level 0,
     r at level 0, cod at level 0, only parsing,
     at level 94, format "'update'  id  (  r  :  'rep'  ,  x  :  dom )  :  cod  :=  '[  '   bod ']' " ) :
    queryDef_scope. *)

(* Notation for ADTs built from [BuildADT]. *)

(*Notation "'QueryADTRep' r { cons1 , meth1 , .. , methn } " :=
  (let _ := {| rep := (QueryStructure r) |}
   in @BuildADT (QueryStructure r) _ _ _ _
             (icons cons1%consDef (inil (B := @consDef (QueryStructure r))))
             (icons (B := @methDef (QueryStructure r)) (meth1%queryDef%methDefParsing ) .. (icons (B := @methDef (QueryStructure r)) methn%queryDef%methDefParsing (inil (B := @methDef (QueryStructure r)))) ..))
    (no associativity, at level 96, r at level 0, only parsing,
     format "'QueryADTRep'  r  '/' '[hv  ' {  cons1 , '//' '//' meth1 , '//' .. , '//' methn  ']' }") : QueryStructure_scope. *)

Definition GetRelation
           (QSSchema : QueryStructureSchema)
           (qs : QueryStructure QSSchema)
           (idx : Fin.t _)
  : @IndexedEnsemble (@RawTuple (GetNRelSchemaHeading (qschemaSchemas QSSchema) idx)) := rawRel (ith2 (rawRels qs) idx).

Definition GetRelationBnd
           (QSSchema : QueryStructureSchema)
           (qs : QueryStructure QSSchema)
           (idx : BoundedIndex (QSschemaNames QSSchema))
  : @IndexedEnsemble (@RawTuple (GetNRelSchemaHeading (qschemaSchemas QSSchema) (ibound (indexb idx)))) := @GetRelation QSSchema qs (ibound (indexb idx)).

(* This lets us drop the constraints from the reference implementation
   for easier refinements. *)

Definition UnConstrQueryStructure (qsSchema : RawQueryStructureSchema) :=
  ilist2 (B := fun ns => RawUnConstrRelation (rawSchemaHeading ns))
        (qschemaSchemas qsSchema).

Definition GetUnConstrRelation
           {QSSchema : RawQueryStructureSchema}
           (qs : UnConstrQueryStructure QSSchema)
           (idx : _)
  : @IndexedEnsemble (@RawTuple (GetNRelSchemaHeading (qschemaSchemas QSSchema) idx)) :=
      ith2 qs idx.

Definition GetUnConstrRelationBnd
           {QSSchema : QueryStructureSchema}
           (qs : UnConstrQueryStructure QSSchema)
           (idx : BoundedIndex (QSschemaNames QSSchema))
  : @IndexedEnsemble (@RawTuple (GetNRelSchemaHeading (qschemaSchemas QSSchema) (ibound (indexb idx)))) :=
      ith2 qs (ibound (indexb idx)).

Definition DropQSConstraints
           {qsSchema : QueryStructureSchema}
           (qs : QueryStructure qsSchema)
  : UnConstrQueryStructure qsSchema :=
  @imap2 _
        (fun ns => RawRelation ns)
        (fun ns => RawUnConstrRelation (rawSchemaHeading ns))
        (fun ns => @rawRel ns) _ (qschemaSchemas qsSchema) (rawRels qs).

Definition DropQSConstraints_AbsR (qsSchema : QueryStructureSchema)
           (qs : QueryStructure qsSchema)
           (qs' : UnConstrQueryStructure qsSchema)
  : Prop :=
  DropQSConstraints qs = qs'.

Lemma GetRelDropConstraints
      {qsSchema : QueryStructureSchema}
      (qs : QueryStructure qsSchema)
      (Ridx : _)
  : GetUnConstrRelation (DropQSConstraints qs) Ridx = GetRelation qs Ridx.
Proof.
  unfold GetUnConstrRelation, DropQSConstraints, GetRelation.
  rewrite <- ith_imap2; reflexivity.
Qed.

(* Typeclass + notations for declaring abstraction relation for
   QueryStructure Implementations. *)



Definition SatisfiesAttributeConstraints
           {qsSchema}
           (Ridx : Fin.t _)
           (tup : @RawTuple (GetNRelSchemaHeading (qschemaSchemas qsSchema) Ridx))
  :=
    match (attrConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)) with
      Some Constr => Constr tup
    | None => True
    end.

Definition SatisfiesTupleConstraints
           {qsSchema}
           (Ridx : Fin.t _)
           (tup tup' : @RawTuple (GetNRelSchemaHeading (qschemaSchemas qsSchema) Ridx)) :=
  match (tupleConstraints (GetNRelSchema (qschemaSchemas qsSchema) Ridx)) with
    Some Constr => Constr tup tup'
  | None => True
  end.

Definition SatisfiesCrossRelationConstraints
           {qsSchema}
           (Ridx Ridx' : Fin.t _)
           (tup : @RawTuple (GetNRelSchemaHeading (qschemaSchemas qsSchema) Ridx)) R :=
  match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
  | Some CrossConstr => CrossConstr tup R
  | None => True
  end.

Definition UpdateUnConstrRelation
           {qsSchema : RawQueryStructureSchema}
           (rels : UnConstrQueryStructure qsSchema)
           (Ridx : _)
           newRel :
  UnConstrQueryStructure qsSchema :=
  replace_Index2 _ rels Ridx newRel.

Definition UpdateRelation
           {qsSchema : QueryStructureSchema}
           (rels : ilist2 (B := RawRelation) (qschemaSchemas qsSchema))
           (Ridx : _)
           newRel :
  ilist2 (qschemaSchemas qsSchema) :=
  replace_Index2 _ rels Ridx newRel.

(* Consequences of ith_replace_BoundIndex_neq and ith_replace_BoundIndex_eq on updates *)

Lemma get_update_unconstr_eq :
  forall (db_schema : RawQueryStructureSchema) (qs : UnConstrQueryStructure db_schema)
         (index : _) ens,
    GetUnConstrRelation (UpdateUnConstrRelation qs index ens) index = ens.
Proof.
  unfold UpdateUnConstrRelation, GetUnConstrRelation.
  intros; rewrite ith_replace2_Index_eq; reflexivity.
Qed.

Lemma get_update_unconstr_neq :
  forall (db_schema : RawQueryStructureSchema) (qs : UnConstrQueryStructure db_schema)
         (index1 index2 : _) ens,
    index1 <> index2 ->
    GetUnConstrRelation
      (UpdateUnConstrRelation qs index1 ens) index2 =
    GetUnConstrRelation qs index2.
Proof.
  unfold UpdateUnConstrRelation, GetUnConstrRelation;
  intros; simpl; rewrite ith_replace2_Index_neq; eauto using string_dec.
Qed.

Notation "ro ≃ rn" := (@UnConstrRelationAbsR _ _ _ ro%QueryImpl rn) : QueryImpl_scope.

Notation "qs ! R" :=
  (GetUnConstrRelationBnd qs {|bindex := R%string |}): QueryImpl_scope.

Arguments BuildQueryStructureConstraints _ _ _.
Arguments BuildQueryStructureConstraints_cons [_ _] _ _ _ _ (*/*) _ .
Arguments BuildQueryStructureConstraints_cons_obligation_1 [_ _] _ (*/*) _ _ _ _ .
