Require Import Coq.Sorting.Mergesort Coq.Structures.Orders
        Coq.Arith.Arith
        Coq.Structures.OrderedType Coq.Structures.OrderedTypeEx
        Coq.Strings.String Coq.FSets.FMapAVL
        Fiat.Common.String_as_OT
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.Operations
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Automation.Common.

Module AttrCountOrder <: TotalLeBool.
                          Definition t := (prod (string * (string * string)) nat).

                          (* Largest element first *)
                          Definition leb (x y : t) :=
                            leb (snd y) (snd x).

                          Theorem leb_total : forall a1 a2 : t, leb a1 a2 = true \/ leb a2 a1 = true.
                          Proof.
                            unfold t; intros; intuition; unfold leb; simpl.
                            case_eq (Compare_dec.leb b b0); intuition.
                            case_eq (Compare_dec.leb b0 b); intuition.
                            apply leb_iff_conv in H; apply leb_iff_conv in H0.
                            omega.
                          Qed.

End AttrCountOrder.

Module PairOfString_As_OT := (PairOrderedType String_as_OT String_as_OT).
Module TripleOfString_As_OT := (PairOrderedType String_as_OT PairOfString_As_OT).

Module RelationAttributeCounter := FMapAVL.Make TripleOfString_As_OT.
Module Import AttrCountSort := Sort AttrCountOrder.

Record KindName
  := { KindNameKind : string;
       KindNameName : string }.

Definition OccurenceCountT {n}
           (qsSchema : Vector.t RawHeading n) :=
  ilist (B := fun heading => list (prod string (Attributes heading))) qsSchema.

Definition IncrementAttrCount
           (idx : string * (string * string))
           (cnt : RelationAttributeCounter.t nat)
  : RelationAttributeCounter.t nat :=
  match RelationAttributeCounter.find idx cnt with
  | Some n => RelationAttributeCounter.add idx (S n) cnt
  | _ => RelationAttributeCounter.add idx 1 cnt
  end.

Definition CountAttributes (l : list (string * (string * string)))
  : list ((string * (string * string)) * nat)  :=
  sort (RelationAttributeCounter.elements
          (fold_right IncrementAttrCount
                      (RelationAttributeCounter.empty nat)
                      l)).

(*Definition GetIndexes
           (qsSchema : RawQueryStructureSchema)
           (indices : list ((string * (string * string)) * nat))
: list (list (string * string)) :=
  map (fun ns : NamedSchema =>
         map (fun index => (fst (fst index), snd (snd (fst index))))
             (filter (fun index => if (fin_eq_dec (fst (snd (fst index)))) (relName ns)
                                   then true
                                   else false)
                     indices))
      (qschemaSchemas qsSchema). *)

(* Add a new occurence to AttrCount *)
Fixpoint InsertOccurence {n}
         {qsSchema : Vector.t RawHeading n}
         (idx : Fin.t n)
         (NewOccurence : prod string (Attributes (Vector.nth qsSchema idx)))
         (AttrCount : OccurenceCountT qsSchema)
         {struct idx}
  : OccurenceCountT qsSchema.
Proof.
  refine (match idx in (Fin.t m') return
                forall (qsSchema : Vector.t _ m'),
                  OccurenceCountT qsSchema
                  -> prod string (Attributes (Vector.nth qsSchema idx))
                  -> OccurenceCountT qsSchema with
          | Fin.F1 q =>
            fun v il new => _
          | Fin.FS q p' =>
            fun v il new => _
          end qsSchema AttrCount NewOccurence).
  - revert il new; pattern q, v; apply Vector.caseS; intros.
    exact (icons (new :: ilist_hd il) (ilist_tl il)).
  - revert p' il new; pattern q, v; apply Vector.caseS; intros.
    exact (icons (ilist_hd il) (InsertOccurence _ _ p' new (ilist_tl il))).
Defined.

Arguments InsertOccurence [_ _ _] _ _.
Fixpoint MergeOccurence {n}
         (qsSchema : Vector.t RawHeading n)
         (AttrCount1 AttrCount2 : OccurenceCountT qsSchema)
         {struct qsSchema}
  : OccurenceCountT qsSchema :=
  match qsSchema return
        forall (AttrCount1 AttrCount2 : OccurenceCountT qsSchema),
          OccurenceCountT qsSchema with
  | Vector.nil => fun AttrCount1 AttrCount2 => inil
  | Vector.cons _ _ qsSchema' =>
    fun AttrCount1 AttrCount2 =>
      icons (ilist_hd AttrCount1 ++ ilist_hd AttrCount2)
            (MergeOccurence qsSchema' (ilist_tl AttrCount1) (ilist_tl AttrCount2))
  end AttrCount1 AttrCount2.

Arguments MergeOccurence [_ _] _ _.

Fixpoint InitOccurence {n}
         (qsSchema : Vector.t RawHeading n)
         {struct qsSchema}
  : OccurenceCountT qsSchema :=
  match qsSchema return OccurenceCountT qsSchema with
  | Vector.nil => inil
  | Vector.cons _ _ qsSchema' =>
    icons nil (InitOccurence qsSchema')
  end.

Definition GetOccurence {n}
           {qsSchema : Vector.t RawHeading n}
           (AttrCount : OccurenceCountT qsSchema)
           (idx : Fin.t n)
  : list (prod string (Attributes (Vector.nth qsSchema idx))) :=
  ith AttrCount idx.

Ltac TermAttributes Term k :=
  match Term with
  | fun tups => @GetAttributeRaw _ (@?f tups) ?BAidx =>
    let Aidx := eval simpl in BAidx in
        match type of f with
        | _ -> @RawTuple (Vector.nth _ ?Ridx) =>
          k Ridx Aidx
        end
  end.

Ltac ClauseAttributes qsSchema WhereClause OtherClauses k :=
  match WhereClause with
  | fun tups => @?C1 tups /\ @?C2 tups =>
    ClauseAttributes qsSchema C1 OtherClauses
                     ltac:(fun attrs1 =>
                             ClauseAttributes qsSchema C2 OtherClauses
                                              ltac:(fun attrs2 =>
                                                      k (MergeOccurence attrs2 attrs1)))
  | fun tups => @?C1 tups = @?C2 tups =>
    TermAttributes C1 ltac:(fun Ridx1 attr1 =>
                              TermAttributes C2 ltac:(fun Ridx2 attr2 =>
                                                        k (@InsertOccurence _ qsSchema Ridx1 (EqualityIndex, attr1) (@InsertOccurence _ qsSchema Ridx2 (EqualityIndex, attr2) (InitOccurence qsSchema)))))
  | fun tups => @?C1 tups = _ =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurence _ qsSchema Ridx (EqualityIndex, attr) (InitOccurence _)))
  | fun tups => _ = @?C1 tups =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurence _ qsSchema Ridx (EqualityIndex, attr) (InitOccurence _)))
  | _ => OtherClauses WhereClause k
  | _ => k (InitOccurence qsSchema)
  end.

Ltac QueryAttributes qsSchema QueryBody OtherClauses k :=
  match QueryBody with
  | @UnConstrQuery_In _ _ _ ?Ridx ?QueryBody' => (* Initial "Naked" Case *)
    let Ridx' := eval compute in Ridx in
        let QueryBody'' := eval cbv beta in (fun tup : @RawTuple (Vector.nth qsSchema Ridx') => QueryBody' tup) in
            QueryAttributes qsSchema QueryBody'' OtherClauses k  (* Simply recurse under binder *)

  | fun tups : ?A =>
      @UnConstrQuery_In _ _ _ ?Ridx
                        (@?f tups) => (* Already Under binder *)
    let Ridx' := eval compute in Ridx in
        let join := eval cbv beta in
        (fun joinedtups : prod A (@RawTuple (Vector.nth qsSchema Ridx')) =>
           f (fst joinedtups) (snd joinedtups)) in
            QueryAttributes qsSchema join OtherClauses k
  | fun tups => Where (@?P tups) (@?QueryBody' tups) =>
    ClauseAttributes qsSchema P OtherClauses
                     ltac:(fun attrs =>
                             QueryAttributes qsSchema QueryBody' OtherClauses ltac:(fun attrs' => k (MergeOccurence attrs attrs')))
  | _ => k (InitOccurence qsSchema)
  end.

Ltac MethodAttributes meth qsSchema OtherClauses l :=
  hone method meth;
  [ match goal with
      |- context[For ?Q] =>
      QueryAttributes qsSchema Q OtherClauses
                      ltac:(fun attrs =>
                              let l' := eval simpl in attrs in
                                  unify l l')
    | _ => unify l (InitOccurence qsSchema )
    end; finish honing | ].

Ltac MethodsAttributes' meths qsSchema OtherClauses l :=
  match meths with
  | Vector.cons _ ?meth _ ?meths' =>
    makeEvar (OccurenceCountT qsSchema)
             ltac:(fun l1 =>
                     makeEvar (OccurenceCountT qsSchema)
                              ltac:(fun l2 =>
                                      unify l (MergeOccurence l1 l2);
                                    MethodAttributes meth qsSchema  OtherClauses l1;
                                    MethodsAttributes' meths' qsSchema  OtherClauses l2))
  | Vector.nil _ => unify l (InitOccurence qsSchema)
  end.

Ltac GenerateIndexesFor meths OtherClauses k :=
  match goal with
    |- Sharpened
         (@BuildADT (UnConstrQueryStructure ?qsSchema) _ _ _ _ _ _) =>
    let rels := eval simpl in (Vector.map rawSchemaHeading (qschemaSchemas qsSchema)) in
        makeEvar (OccurenceCountT rels)
                 ltac:(fun l => MethodsAttributes' meths rels OtherClauses l; let l' := eval simpl in l in k l')
  end.

Ltac GenerateIndexesForAll OtherClauses k :=
  match goal with
    |- Sharpened
         (@BuildADT (UnConstrQueryStructure ?qsSchema) _ _ _ ?methSigs _ _) =>
    let meths := eval compute in (Vector.map methID methSigs) in
        GenerateIndexesFor meths OtherClauses k
  end.

Tactic Notation "make" "simple" "indexes" "using" constr(attrlist) :=
  match goal with
  | [ |- Sharpened (@BuildADT (UnConstrQueryStructure ?sch) _ _ _ _ _ _ )] =>
    let sch' := eval simpl in (qschemaSchemas sch) in
        makeIndex' sch' attrlist
                   ltac:(fun l =>
                           pose_string_hyps; pose_heading_hyps;
                         let index := fresh "Index" in
                         pose l as index;
                         simpl in index;
                         pose_string_hyps_in index; pose_heading_hyps_in index;
                         pose_search_term_in index;
                         pose_SearchUpdateTerms_in index;
                         hone representation using (@DelegateToBag_AbsR sch index))
  end.

(*Tactic Notation "make" "indexes" "using" tactic(ClauseMatchers) :=
  GenerateIndexesForAll
    ClauseMatchers
    ltac:(fun attrlist => make simple indexes using attrlist). *)

(* Recurse over [fds] to find an attribute matching s *)
Ltac findMatchingTerm fds kind s k :=
  match fds with
  | ({| KindIndexKind := ?IndexType;
        KindIndexIndex := ?fd |}, ?X) =>
    (* Check if this field name is equal to s; process [X] with [k] if so. *)
    pose fds;
      unify s fd;
      unify kind IndexType;
      k X
  | (?fds1, ?fds2) => findMatchingTerm fds1 kind s k || findMatchingTerm fds2 kind s k
  end.
