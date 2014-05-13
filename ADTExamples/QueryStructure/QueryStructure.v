Require Import List String FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation Program.
Require Export
        ADTExamples.QueryStructure.Notations
        Heading Tuple Schema Relation QueryStructureSchema
        Sorting.Permutation.

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

Class QueryStructureHint :=
  { qsSchemaHint : QueryStructureSchema;
    qsHint :> @QueryStructure qsSchemaHint
  }.

(* This lets us drop the constraints from the reference implementation
   for easier refinements. *)

Notation "'def' 'query' id ( x : dom ) : cod := bod" :=
  (Build_obsDef {| obsID := id; obsDom := dom; obsCod := cod |}
                (fun (r : repHint) x =>
                   let _ := {| qsHint := r |} in
                   bod%QuerySpec))
    (no associativity, id at level 0, x at level 0, dom at level 0,
     cod at level 0, only parsing,
     at level 94, format "'def'  'query'  id  ( x  :  dom )  :  cod  :=  '[  '   bod ']' " ) :
queryDefParsing_scope.

Notation "'def' 'query' id ( x : dom ) : cod := bod" :=
  (Build_obsDef {| obsID := id; obsDom := dom; obsCod := cod |}
                (fun r x => (bod%QuerySpec)))
    (no associativity, id at level 0, r at level 0, x at level 0, dom at level 0,
     cod at level 0,
     at level 94, format "'def'  'query'  id  ( x  :  dom )  :  cod  :=  '[  '   bod ']' " ) :
queryDef_scope.

Notation "'def' 'update' id ( x : dom ) : 'rep' := bod" :=
  (Build_mutDef {| mutID := id; mutDom := dom |}
                (fun (r : repHint) x =>
                   let _ := {| qsHint := r |} in
                   bod%QuerySpec))
    (no associativity, at level 94, id at level 0,
     x at level 0, dom at level 0, only parsing,
     format "'def'  'update'  id  ( x :  dom )  :  'rep'  :=  '[  '   bod ']' " ) :
updateDefParsing_scope.

Notation "'def' 'update' id ( x : dom ) : 'rep' := bod" :=
  (Build_mutDef (id%string : rep × dom → rep)%mutSig
                   (fun r x => bod%QuerySpec))
    (no associativity, at level 94, id at level 0, r at level 0,
     x at level 0, dom at level 0,
     format "'def'  'update'  id  ( x :  dom )  :  'rep'  :=  '[  '   bod ']' " ) :
updateDef_scope.

(* Notation for ADTs built from [BuildADT]. *)

Notation "'QueryADTRep' r { mut1 , .. , mutn ; obs1 , .. , obsn } " :=
  (let _ := {| repHint := r |} in
    @BuildADT r
             _
             _
             (icons _ mut1%updateDefParsing .. (icons _ mutn%updateDefParsing (inil (@mutDef r))) ..)
             (icons _ obs1%queryDefParsing .. (icons _ obsn%queryDefParsing (inil (@obsDef r))) ..))
    (no associativity, at level 96, r at level 0, only parsing,
     format "'QueryADTRep'  r  '/' '[hv  ' {  mut1 , '//' .. , '//' mutn ; '//' obs1 , '//' .. , '//' obsn  ']' }") : QueryStructureParsing_scope.

Notation "'QueryADTRep' r { mut1 , .. , mutn ; obs1 , .. , obsn } " :=
  (@BuildADT r
             _
             _
             (icons _ mut1%updateDef .. (icons _ mutn%updateDef (inil (@mutDef r))) ..)
             (icons _ obs1%queryDef .. (icons _ obsn%queryDef (inil (@obsDef r))) ..))
    (no associativity, at level 96, r at level 0,
     format "'QueryADTRep'  r  '/' '[hv  ' {  mut1 , '//' .. , '//' mutn ; '//' obs1 , '//' .. , '//' obsn  ']' }") : QueryStructure_scope.

Notation GetRelationKey QSSchema index :=
  (@Build_BoundedIndex _ (map relName (qschemaSchemas QSSchema))
                      index%string _).

Notation GetAttributeKey Rel index :=
  ((fun x : Attributes (GetNRelSchemaHeading (qschemaSchemas _) Rel) => x)  {| bindex := index%string |}).

Definition GetUnConstrRelation
           (QSSchema : QueryStructureSchema)
           (qs : UnConstrQueryStructure QSSchema)
           (idx : @BoundedString (map relName (qschemaSchemas QSSchema)))
  := ith_Bounded _ qs idx.

Definition GetRelation
           (QSSchema : QueryStructureSchema)
           (qs : QueryStructure QSSchema)
           (idx : @BoundedString (map relName (qschemaSchemas QSSchema)))
  := rel (ith_Bounded _ (rels qs) idx).

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
