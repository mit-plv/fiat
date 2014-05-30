Require Import List String FunctionalExtensionality
        Computation.Core
        ADT.ADTSig ADT.Core
        ADTNotation.ilist ADTNotation.StringBound
        ADTNotation.BuildADT ADTNotation.BuildADTSig
        QueryStructure.Notations
        QueryStructure.Heading QueryStructure.Tuple QueryStructure.Schema QueryStructure.Relation
        QueryStructure.QueryStructureSchema.

(* A Query Structure is a collection of relations
   (described by a proposition) which satisfy the
   schema and the cross-relation constraints. *)

Record QueryStructure (QSSchema : QueryStructureSchema) :=
  { rels : ilist (fun ns => Relation (relSchema ns))
             (qschemaSchemas QSSchema);
    crossConstr :
      forall (idx idx' : @BoundedString (map relName (qschemaSchemas QSSchema)))
             (tup :
                @Tuple (QSGetNRelSchemaHeading QSSchema idx)),
        idx <> idx' ->
        (* These are cross-relation constraints which only need to be
           enforced on distinct relations. *)
                (rel
                   (ith_Bounded _ rels idx )) tup ->
        BuildQueryStructureConstraints
          QSSchema idx idx' tup
          (rel (ith_Bounded _ rels idx'))
  }.

Notation "t ! R" := (rels t R%string): QueryStructure_scope.

(* This typeclass allows our method definitions to infer the
   the QueryStructure [r] they are called with. *)

Class QueryStructureSchemaHint :=
  { qsSchemaHint : QueryStructureSchema
  }.

Class QueryStructureHint :=
  { qsSchemaHint' : QueryStructureSchema;
    qsHint :> @QueryStructure qsSchemaHint'
  }.

Notation "'query' id ( x : dom ) : cod := bod" :=
  (Build_methDef {| methID := id; methDom := dom; methCod := cod |}
                (fun (r : QueryStructure qsSchemaHint) x =>
                   let _ := {| qsHint := r |} in
                   queryRes <- bod%QuerySpec;
                    ret (r, queryRes)))%comp
    (no associativity, id at level 0, x at level 0, dom at level 0,
     cod at level 0, only parsing,
     at level 94, format "'query'  id  ( x  :  dom )  :  cod  :=  '[  '   bod ']' " ) :
queryDef_scope.

Notation "'update' id ( x : dom ) : cod := bod" :=
  (Build_methDef {| methID := id; methDom := dom; methCod := cod |}
                (fun (r : QueryStructure qsSchemaHint) x =>
                   let _ := {| qsHint := r |} in
                   bod%QuerySpec))
    (no associativity, id at level 0, x at level 0, dom at level 0,
     cod at level 0, only parsing,
     at level 94, format "'update'  id  ( x  :  dom )  :  cod  :=  '[  '   bod ']' " ) :
queryDef_scope.

(* Notation for ADTs built from [BuildADT]. *)

Notation "'QueryADTRep' r { cons1 , meth1 , .. , methn } " :=
  (let _ := {| qsSchemaHint := r |} in
    @BuildADT (QueryStructure r)
             _
             _
             (icons _ cons1%consDef (inil (@consDef (QueryStructure r))))
             (icons _ meth1%queryDef .. (icons _ methn%queryDef (inil (@methDef (QueryStructure r)))) ..))
    (no associativity, at level 96, r at level 0, only parsing,
     format "'QueryADTRep'  r  '/' '[hv  ' {  cons1 , '//' '//' meth1 , '//' .. , '//' methn  ']' }") : QueryStructure_scope.

Notation GetRelationKey QSSchema index :=
  (@Build_BoundedIndex _ (map relName (qschemaSchemas QSSchema))
                      index%string _).

Notation GetAttributeKey Rel index :=
  ((fun x : Attributes (GetNRelSchemaHeading (qschemaSchemas _) Rel) => x)  {| bindex := index%string |}).

Definition GetRelation
           (QSSchema : QueryStructureSchema)
           (qs : QueryStructure QSSchema)
           (idx : @BoundedString (map relName (qschemaSchemas QSSchema)))
  := rel (ith_Bounded _ (rels qs) idx).

(* This lets us drop the constraints from the reference implementation
   for easier refinements. *)

Definition GetUnConstrRelation
           (QSSchema : QueryStructureSchema)
           (qs : UnConstrQueryStructure QSSchema)
           (idx : @BoundedString (map relName (qschemaSchemas QSSchema)))
  := ith_Bounded _ qs idx.

Definition DropQSConstraints
           (qsSchema : QueryStructureSchema)
           (qs : QueryStructure qsSchema)
: UnConstrQueryStructure qsSchema :=
    @imap NamedSchema
        (fun ns => Relation (relSchema ns))
        (fun ns => UnConstrRelation (relSchema ns))
        (fun ns => @rel (relSchema ns)) _ (rels qs).

Definition DropQSConstraints_SiR (qsSchema : QueryStructureSchema)
           (qs : QueryStructure qsSchema)
           (qs' : UnConstrQueryStructure qsSchema)
           : Prop :=
  DropQSConstraints qs = qs'.

Lemma GetRelDropConstraints
      (qsSchema : QueryStructureSchema)
      (qs : QueryStructure qsSchema)
      (Ridx : _)
: GetUnConstrRelation (DropQSConstraints qs) Ridx = GetRelation qs Ridx.
Proof.
  unfold GetUnConstrRelation, DropQSConstraints, GetRelation.
  rewrite <- ith_Bounded_imap; reflexivity.
Qed.
