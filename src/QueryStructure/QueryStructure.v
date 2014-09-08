Require Import List String FunctionalExtensionality Ensembles Arith
        Computation.Core
        ADT.ADTSig ADT.Core
        Common.ilist ADTNotation.StringBound
        ADTNotation.BuildADT ADTNotation.BuildADTSig
        QueryStructure.Notations QueryStructure.Heading
        QueryStructure.Tuple QueryStructure.Schema QueryStructure.Relation
        QueryStructure.QueryStructureSchema.

Section BuildQueryStructureConstraints.
  (* Query Structures maintain a set of constraints that enforce
     cross-relation data integrity. Query Structure Schemas encode
     these as a list of dependent products, which
     [BuildQueryStructureConstraints] uses to build the actual constraints.
   *)

  Local Obligation Tactic := intros.

  (* [BuildQueryStructureConstraints_cons] searches the *)
  Program Definition BuildQueryStructureConstraints_cons
          (namedSchemas : list NamedSchema)
          (constr : sigT (crossRelationProdR namedSchemas))
          (constraints :
             list (sigT (crossRelationProdR namedSchemas)))
          (idx idx' : _)
          (HInd : option (crossRelationR namedSchemas idx idx'))
  : option (crossRelationR namedSchemas idx idx')
    :=
      if (eq_nat_dec (ibound idx) (ibound (indexb (fst (projT1 constr))))) then
        if (eq_nat_dec (ibound idx') (ibound (indexb (snd (projT1 constr))))) then
          _
        else HInd
      else HInd.
  Next Obligation.
    destruct constr; simpl in *.
    (* No need to check if the indices are in the list of Relations, because
     they are Bounded Strings. *)
    unfold crossRelationR, GetNRelSchemaHeading, GetNRelSchema; simpl.
    erewrite nth_Bounded_eq by (exact H).
    erewrite nth_Bounded_eq with (idx0 := idx') by (exact H0).
    exact (Some c).
  Defined.

  Fixpoint BuildQueryStructureConstraints'
           (namedSchemas : list NamedSchema)
           (constraints :
            list (sigT (crossRelationProdR namedSchemas)))
           {struct constraints}
  : forall (idx idx' : _), option (crossRelationR namedSchemas idx idx') :=
    match constraints with
      | idx'' :: constraints' =>
        fun idx idx' => @BuildQueryStructureConstraints_cons
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

Record QueryStructure (QSSchema : QueryStructureSchema) :=
  { rels : ilist (fun ns => Relation (relSchema ns))
             (qschemaSchemas QSSchema);
    crossConstr :
      forall (idx idx' : @BoundedString (map relName (qschemaSchemas QSSchema))),
      match (BuildQueryStructureConstraints QSSchema idx idx') with
        | Some CrossConstr =>
          forall (tup :
                    @IndexedTuple (QSGetNRelSchemaHeading QSSchema idx)),
            idx <> idx' ->
            (* These are cross-relation constraints which only need to be
           enforced on distinct relations. *)
            (rel (ith_Bounded _ rels idx )) tup ->
            CrossConstr tup (rel (ith_Bounded _ rels idx'))
        | None => True
      end
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
                   let _ := {| codHint := cod |} in
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

Definition GetRelation
           (QSSchema : QueryStructureSchema)
           (qs : QueryStructure QSSchema)
           (idx : @BoundedString (map relName (qschemaSchemas QSSchema)))
  := rel (ith_Bounded _ (rels qs) idx).

(* This lets us drop the constraints from the reference implementation
   for easier refinements. *)

Definition UnConstrQueryStructure (qsSchema : QueryStructureSchema) :=
  ilist (fun ns => UnConstrRelation (schemaHeading (relSchema ns )))
        (qschemaSchemas qsSchema).

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
        (fun ns => UnConstrRelation (schemaHeading (relSchema ns)))
        (fun ns => @rel (relSchema ns)) _ (rels qs).

Definition DropQSConstraints_AbsR (qsSchema : QueryStructureSchema)
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

(* Typeclass + notations for declaring abstraction relation for
   QueryStructure Implementations. *)

Class UnConstrRelationAbsRClass {A B : Type} :=
  { UnConstrRelationAbsR : Ensemble A -> B -> Prop }.

Definition decides (b : bool) (P : Prop) := if b then P else ~ P.

Definition SatisfiesSchemaConstraints
           {qsSchema} Ridx tup tup' :=
  match (schemaConstraints (QSGetNRelSchema qsSchema Ridx)) with
      Some Constr => Constr tup tup'
    | None => True
  end.

Definition SatisfiesCrossRelationConstraints
           {qsSchema} Ridx Ridx' tup R :=
  match (BuildQueryStructureConstraints qsSchema Ridx Ridx') with
      | Some CrossConstr => CrossConstr tup R
      | None => True
  end.

Definition UpdateUnConstrRelation
           (qsSchema : QueryStructureSchema)
           (rels : UnConstrQueryStructure qsSchema)
           (Ridx : _)
           newRel :
  UnConstrQueryStructure qsSchema :=
  replace_BoundedIndex relName rels Ridx newRel.

Definition UpdateRelation
           (qsSchema : QueryStructureSchema)
           (rels : ilist (fun ns => Relation (relSchema ns))
                         (qschemaSchemas qsSchema))
           (Ridx : _)
           newRel :
  ilist (fun ns => Relation (relSchema ns))
        (qschemaSchemas qsSchema) :=
  replace_BoundedIndex relName rels Ridx newRel.

  (* Consequences of ith_replace_BoundIndex_neq and ith_replace_BoundIndex_eq on updates *)

  Lemma get_update_unconstr_eq :
    forall (db_schema : QueryStructureSchema) (qs : UnConstrQueryStructure db_schema)
           (index : BoundedString) ens,
      GetUnConstrRelation
        (UpdateUnConstrRelation qs index ens) index = ens.
  Proof.
    unfold UpdateUnConstrRelation, GetUnConstrRelation;
    intros; simpl; rewrite ith_replace_BoundIndex_eq; eauto using string_dec.
  Qed.

  Lemma get_update_unconstr_neq :
    forall (db_schema : QueryStructureSchema) (qs : UnConstrQueryStructure db_schema)
           (index1 index2 : BoundedString) ens,
      index1 <> index2 ->
      GetUnConstrRelation
        (UpdateUnConstrRelation qs index1 ens) index2 =
      GetUnConstrRelation qs index2.
  Proof.
    unfold UpdateUnConstrRelation, GetUnConstrRelation;
    intros; simpl; rewrite ith_replace_BoundIndex_neq; eauto using string_dec.
  Qed.

Notation "ro ≃ rn" := (@UnConstrRelationAbsR _ _ _ ro%QueryImpl rn) : QueryImpl_scope.

Notation "qs ! R" :=
  (GetUnConstrRelation qs {|bindex := R%string |}): QueryImpl_scope.

Arguments BuildQueryStructureConstraints _ _ _.
Arguments BuildQueryStructureConstraints_cons [_] _ _ _ _ (*/*) _ .
Arguments BuildQueryStructureConstraints_cons_obligation_1 [_] _ (*/*) _ _ _ _ _ _ .
