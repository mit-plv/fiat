Require Import List String FunctionalExtensionality Ensembles
        ADTNotation.ilist ADTNotation Program.
Require Export
        ADTExamples.QueryStructure.Notations
        Heading Tuple Schema Relation QueryStructureSchema.

(* A Query Structure is a collection of relations
   (described by a proposition) which satisfy the
   schema and the cross-relation constraints. *)

Record QueryStructure (QSSchema : QueryStructureSchema) :=
  { rels : forall idx : qschemaIndex QSSchema,
             Relation (qschemaSchema QSSchema idx);
    crossConstr :
      forall (idx idx' : qschemaIndex QSSchema)
             (tup : Tuple (schemaHeading (qschemaSchema QSSchema idx))),
        List.In tup (rel (rels idx)) ->
        qschemaConstraints QSSchema idx idx' tup (rels idx')
  }.

Notation "t ! R" := (rels t R%string): QueryStructure_scope.

(* This typeclass allows our method definitions to infer the
   the QueryStructure [r] they are called with. *)

Class QueryStructureHint :=
  { qsSchemaHint : QueryStructureSchema;
    qsHint :> @QueryStructure qsSchemaHint
  }.

Notation "'def' 'query' id ( x : dom ) : cod := bod" :=
  (Build_obsDef {| obsID := id; obsDom := dom; obsCod := cod |}
                (fun (r : repHint) x =>
                   let _ := {| qsHint := r |} in
                   Pick (bod%QuerySpec)))
    (no associativity, id at level 0, x at level 0, dom at level 0,
     cod at level 0, only parsing,
     at level 94, format "'def'  'query'  id  ( x  :  dom )  :  cod  :=  '[  '   bod ']' " ) :
queryDefParsing_scope.

Notation "'def' 'query' id ( x : dom ) : cod := bod" :=
  (Build_obsDef {| obsID := id; obsDom := dom; obsCod := cod |} (fun r x => Pick (bod%QuerySpec)))
    (no associativity, id at level 0, r at level 0, x at level 0, dom at level 0,
     cod at level 0,
     at level 94, format "'def'  'query'  id  ( x  :  dom )  :  cod  :=  '[  '   bod ']' " ) :
queryDef_scope.

Notation "'def' 'update' id ( x : dom ) : 'rep' := bod" :=
  (Build_mutDef {| mutID := id; mutDom := dom |}
                (fun (r : repHint) x =>
                   let _ := {| qsHint := r |} in
                   Pick (bod%QuerySpec)))
    (no associativity, at level 94, id at level 0,
     x at level 0, dom at level 0, only parsing,
     format "'def'  'update'  id  ( x :  dom )  :  'rep'  :=  '[  '   bod ']' " ) :
updateDefParsing_scope.

Notation "'def' 'update' id ( x : dom ) : 'rep' := bod" :=
  (Build_mutDef {| mutID := id; mutDom := dom |} (fun r x => Pick (bod%QuerySpec)))
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
