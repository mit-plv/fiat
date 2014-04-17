Require Import List String FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation Program.
Require Export
        ADTExamples.QueryStructure.Notations
        Heading Tuple Schema Relation QueryStructureSchema
        Sorting.Permutation.

(* A Query Structure is a collection of relations
   (described by a proposition) which satisfy the
   schema and the cross-relation constraints. *)

Program Definition defaultRelation : Relation (relSchema defaultSchema) :=
  {| rel := nil;
     constr := fun (_ : Tuple <"null" : ()>%Heading) (_ : False) => I |}.

Record QueryStructure (QSSchema : QueryStructureSchema) :=
  { rels : ilist (fun ns => Relation (relSchema ns))
             (qschemaSchemas QSSchema);
    crossConstr :
      forall (idx idx' : string)
             (tup :
                Tuple (QSGetNRelSchemaHeading QSSchema idx)),
        idx <> idx' ->
        (* These are cross-relation constraints which only need to be
           enforced on distinct relations. *)
        List.In tup
                (rel
                   (ith NamedSchema_eq rels idx defaultSchema
                        defaultRelation)) ->
        BuildQueryStructureConstraints
          QSSchema idx idx' tup
          (rel (ith NamedSchema_eq rels idx' defaultSchema
                    defaultRelation))
  }.

Notation "t ! R" := (rels t R%string): QueryStructure_scope.

(* This typeclass allows our method definitions to infer the
   the QueryStructure [r] they are called with. *)

Class QueryStructureHint :=
  { qsSchemaHint : QueryStructureSchema;
    qsHint :> @QueryStructure qsSchemaHint
  }.

Definition indistinguishable {A: Type} (a b: list A) := (Permutation a b).

Notation "'def' 'query' id ( x : dom ) : cod := bod" :=
  (Build_obsDef {| obsID := id; obsDom := dom; obsCod := cod |}
                (fun (r : repHint) x =>
                   let _ := {| qsHint := r |} in
                   Pick (fun u => indistinguishable u (bod%QuerySpec))))
    (no associativity, id at level 0, x at level 0, dom at level 0,
     cod at level 0, only parsing,
     at level 94, format "'def'  'query'  id  ( x  :  dom )  :  cod  :=  '[  '   bod ']' " ) :
queryDefParsing_scope.

Notation "'def' 'query' id ( x : dom ) : cod := bod" :=
  (Build_obsDef {| obsID := id; obsDom := dom; obsCod := cod |} (fun r x => Pick (fun u => indistinguishable u (bod%QuerySpec))))
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

Definition GetRelation
           (QSSchema : QueryStructureSchema)
           (qs : QueryStructure QSSchema)
           (idx : string) :=
  rel (ith NamedSchema_eq (rels qs) idx defaultSchema defaultRelation).

(* This lets us drop the constraints right off the bat. *)

Definition UnConstrQueryStructure (qsSchema : QueryStructureSchema) :=
  ilist (fun ns => UnConstrRelation (relSchema ns))
        (qschemaSchemas qsSchema).

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
