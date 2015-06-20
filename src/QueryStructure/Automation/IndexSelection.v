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

Module OccCountOrder <: TotalLeBool.
   Definition t := (prod string nat).

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

End OccCountOrder.

Module AttrCountOrder <: TotalLeBool.
   Variable n : nat.
   Definition t := (prod (prod string (Fin.t n))  nat).

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

Module RelationAttributeCounter := FMapAVL.Make String_as_OT.
Module OccCountSort := Sort OccCountOrder.
Module AttrCountSort := Sort AttrCountOrder.

Record KindName
  := { KindNameKind : string;
       KindNameName : string }.

Definition OccurenceCountT {n}
           (qsSchema : Vector.t RawHeading n) :=
  ilist3 (B := fun heading => list (prod string (Attributes heading))) qsSchema.
Definition OccurenceRankT {n}
           (qsSchema : Vector.t RawHeading n) :=
  ilist3 (B := fun heading => Vector.t (RelationAttributeCounter.t nat) (NumAttr heading)) qsSchema.

Definition OccurencesCountT {n}
           (qsSchema : Vector.t RawHeading n) :=
  prod (OccurenceCountT qsSchema) (OccurenceCountT qsSchema).
Definition OccurencesRankT {n}
           (qsSchema : Vector.t RawHeading n) :=
  prod (OccurenceRankT qsSchema) (OccurenceRankT qsSchema).

Fixpoint InitAttrCount n
  : Vector.t (RelationAttributeCounter.t nat) n :=
  match n return Vector.t (RelationAttributeCounter.t nat) n with
  | 0 => Vector.nil _
  | S n' => Vector.cons _ (RelationAttributeCounter.empty nat) _ (InitAttrCount n')
  end.

Fixpoint IncrementAttrCount {n}
           (AttrRank : Vector.t (RelationAttributeCounter.t nat) n)
           (idx : Fin.t n)
           (NewOccurence : string)
           {struct idx}
  : Vector.t (RelationAttributeCounter.t nat) n.
Proof.
  refine (match idx in (Fin.t m') return
                Vector.t (RelationAttributeCounter.t nat) m'
                -> string
                -> Vector.t (RelationAttributeCounter.t nat) m' with
          | Fin.F1 q =>
            fun v new => _
          | Fin.FS q p' =>
            fun v new => _
          end AttrRank NewOccurence).
  - revert new; pattern q, v; apply Vector.caseS; intros.
    refine (match RelationAttributeCounter.find new h with
            | Some cnt => (Vector.cons _ (RelationAttributeCounter.add new (S cnt) h) _ t)
            | None => (Vector.cons _ (RelationAttributeCounter.add new 1 h) _ t)
            end).
  - revert p' new; pattern q, v; apply Vector.caseS; intros.
    exact (Vector.cons _ h _ (IncrementAttrCount _ t p' new)).
Defined.

Fixpoint InitOccRank {n}
         (qsSchema : Vector.t RawHeading n)
         {struct qsSchema}
  : OccurenceRankT qsSchema :=
  match qsSchema return OccurenceRankT qsSchema with
  | Vector.nil => inil3
  | Vector.cons sch _ qsSchema' =>
    icons3 (InitAttrCount _) (InitOccRank qsSchema')
  end.

Definition InitOccsRank {n}
           (qsSchema : Vector.t RawHeading n)
  : OccurencesRankT qsSchema :=
  (InitOccRank qsSchema, InitOccRank qsSchema).

Definition CountAttributes {n}
           (qsSchema : Vector.t RawHeading n)
           (OccCount : OccurenceCountT qsSchema)
  : OccurenceRankT qsSchema :=
  imap3 _ _ (fun heading (OccCount : list (string * (Attributes heading))) =>
               fold_right (fun attrC AttrRank => IncrementAttrCount AttrRank (snd attrC) (fst attrC)) (InitAttrCount _) OccCount) _ OccCount.

Definition CountAttributes' {n}
           (qsSchema : Vector.t RawHeading n)
           (OccCounts : OccurencesCountT qsSchema)
  : OccurencesRankT qsSchema :=
  (CountAttributes qsSchema (fst OccCounts),
   CountAttributes qsSchema (snd OccCounts)).

Fixpoint PickIndex {n}
           (AttrRank : Vector.t (RelationAttributeCounter.t nat) n)
  : list ((string * Fin.t n) * nat) :=
  match AttrRank in Vector.t _ n return
                list ((string * Fin.t n) * nat) with
          | Vector.cons attr _ AttrRank' =>
            match OccCountSort.sort (RelationAttributeCounter.elements attr) with
            | nil => (map (fun a => (fst (fst a), Fin.FS (snd (fst a)), (snd a))) (PickIndex AttrRank'))
            | a :: a' => cons (fst a, Fin.F1, snd a) (map (fun a => (fst (fst a), Fin.FS (snd (fst a)), (snd a))) (PickIndex AttrRank'))
            end
          | Vector.nil => nil
          end.

Fixpoint PickIndexes {n}
           (qsSchema : Vector.t RawHeading n)
           (OccRank : OccurencesRankT qsSchema)
           {struct qsSchema}
  : ilist3 (B := fun heading => list (prod string (Attributes heading))) qsSchema :=
  match qsSchema return
        OccurencesRankT qsSchema
        -> ilist3 (B := fun heading => list (prod string (Attributes heading))) qsSchema with
  | Vector.cons heading _ qsSchema' =>
    fun OccRank =>
      let bestLastIndex :=
          match (PickIndex ((ilist3_hd (snd OccRank)))) with
          | idx :: _ => [fst idx]
          | _ => [ ]
          end in
      icons3 (map (@fst _ _) (PickIndex ((ilist3_hd (fst OccRank))) ) ++ bestLastIndex) (PickIndexes (ilist3_tl (fst OccRank), ilist3_tl (snd OccRank)))
  | Vector.nil => fun OccRank => inil3
  end OccRank.

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
    exact (icons3 (new :: ilist3_hd il) (ilist3_tl il)).
  - revert p' il new; pattern q, v; apply Vector.caseS; intros.
    exact (icons3 (ilist3_hd il) (InsertOccurence _ _ p' new (ilist3_tl il))).
Defined.

Definition InsertOccurenceOfAny {n}
         {qsSchema : Vector.t RawHeading n}
         (idx : Fin.t n)
         (NewOccurence : prod string (Attributes (Vector.nth qsSchema idx)))
         (AttrCount : OccurencesCountT qsSchema)
  : OccurencesCountT qsSchema :=
  (InsertOccurence idx NewOccurence (fst AttrCount), snd AttrCount).

Definition InsertOccurenceOfLast {n}
         {qsSchema : Vector.t RawHeading n}
         (idx : Fin.t n)
         (NewOccurence : prod string (Attributes (Vector.nth qsSchema idx)))
         (AttrCount : OccurencesCountT qsSchema)
  : OccurencesCountT qsSchema :=
  (fst AttrCount, InsertOccurence idx NewOccurence (snd AttrCount)).

Arguments InsertOccurence [_ _ _] _ _.
Fixpoint MergeOccurence {n}
         (qsSchema : Vector.t RawHeading n)
         (AttrCount1 AttrCount2 : OccurenceCountT qsSchema)
         {struct qsSchema}
  : OccurenceCountT qsSchema :=
  match qsSchema return
        forall (AttrCount1 AttrCount2 : OccurenceCountT qsSchema),
          OccurenceCountT qsSchema with
  | Vector.nil => fun AttrCount1 AttrCount2 => inil3
  | Vector.cons _ _ qsSchema' =>
    fun AttrCount1 AttrCount2 =>
      icons3 (ilist3_hd AttrCount1 ++ ilist3_hd AttrCount2)
            (MergeOccurence qsSchema' (ilist3_tl AttrCount1) (ilist3_tl AttrCount2))
  end AttrCount1 AttrCount2.

Definition MergeOccurences {n}
         (qsSchema : Vector.t RawHeading n)
         (AttrCount1 AttrCount2 : OccurencesCountT qsSchema)
  : OccurencesCountT qsSchema :=
  (MergeOccurence qsSchema (fst AttrCount1) (fst AttrCount2),
   MergeOccurence qsSchema (snd AttrCount1) (snd AttrCount2)).

Arguments MergeOccurence [_ _] _ _.

Fixpoint InitOccurence {n}
         (qsSchema : Vector.t RawHeading n)
         {struct qsSchema}
  : OccurenceCountT qsSchema :=
  match qsSchema return OccurenceCountT qsSchema with
  | Vector.nil => inil3
  | Vector.cons _ _ qsSchema' =>
    icons3 nil (InitOccurence qsSchema')
  end.

Definition InitOccurences {n}
         (qsSchema : Vector.t RawHeading n)
  : OccurencesCountT qsSchema :=
  (InitOccurence qsSchema, InitOccurence qsSchema).

Definition GetOccurence {n}
           {qsSchema : Vector.t RawHeading n}
           (AttrCount : OccurenceCountT qsSchema)
           (idx : Fin.t n)
  : list (prod string (Attributes (Vector.nth qsSchema idx))) :=
  ith3 AttrCount idx.

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
                                                      k (MergeOccurences attrs2 attrs1)))
  | fun tups => @?C1 tups = @?C2 tups =>
    TermAttributes C1 ltac:(fun Ridx1 attr1 =>
                              TermAttributes C2 ltac:(fun Ridx2 attr2 =>
                                                        k (@InsertOccurenceOfAny _ qsSchema Ridx1 (EqualityIndex, attr1) (@InsertOccurenceOfAny _ qsSchema Ridx2 (EqualityIndex, attr2) (InitOccurences qsSchema)))))
  | fun tups => @?C1 tups = _ =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurenceOfAny _ qsSchema Ridx (EqualityIndex, attr) (InitOccurences _)))
  | fun tups => _ = @?C1 tups =>
    TermAttributes C1 ltac:(fun Ridx attr =>
                              k (@InsertOccurenceOfAny _ qsSchema Ridx (EqualityIndex, attr) (InitOccurences _)))
  | _ => OtherClauses qsSchema WhereClause k
  | _ => k (InitOccurences qsSchema)
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
                             QueryAttributes qsSchema QueryBody' OtherClauses ltac:(fun attrs' => k (MergeOccurences attrs attrs')))
  | _ => k (InitOccurences qsSchema)
  end.

Ltac MethodAttributes meth qsSchema OtherClauses l :=
  hone method meth;
  [ match goal with
      |- context[For ?Q] =>
      QueryAttributes qsSchema Q OtherClauses
                      ltac:(fun attrs =>
                              let l' := eval simpl in attrs in
                                  unify l l')
    | _ => unify l (InitOccurences qsSchema )
    end; finish honing | ].

Ltac MethodsAttributes' meths qsSchema OtherClauses l :=
  match meths with
  | Vector.cons _ ?meth _ ?meths' =>
    makeEvar (OccurencesCountT qsSchema)
             ltac:(fun l1 =>
                     makeEvar (OccurencesCountT qsSchema)
                              ltac:(fun l2 =>
                                      unify l (MergeOccurences l1 l2);
                                    MethodAttributes meth qsSchema  OtherClauses l1;
                                    MethodsAttributes' meths' qsSchema  OtherClauses l2))
  | Vector.nil _ => unify l (InitOccurences qsSchema)
  end.

Ltac GenerateIndexesFor meths OtherClauses k :=
  match goal with
    |- Sharpened
         (@BuildADT (UnConstrQueryStructure ?qsSchema) _ _ _ _ _ _) =>
    let rels := eval simpl in (Vector.map rawSchemaHeading (qschemaSchemas qsSchema)) in
        makeEvar (OccurencesCountT rels)
                 ltac:(fun l => MethodsAttributes' meths rels OtherClauses l;
                       let l' := eval compute in (PickIndexes (CountAttributes' l)) in k l')
  end.

Ltac GenerateIndexesForAll OtherClauses k :=
  match goal with
    |- Sharpened
         (@BuildADT (UnConstrQueryStructure ?qsSchema) _ _ _ ?methSigs _ _) =>
    let meths := eval compute in (Vector.map methID methSigs) in
        GenerateIndexesFor meths OtherClauses k
  end.

Tactic Notation "make" "simple" "indexes" "using" constr(attrlist) tactic(BuildEarlyIndex) tactic(BuildLastIndex):=
  match goal with
  | [ |- Sharpened (@BuildADT (UnConstrQueryStructure ?sch) _ _ _ _ _ _ )] =>
    let sch' := eval simpl in (qschemaSchemas sch) in
        makeIndex' sch' attrlist
                   BuildEarlyIndex BuildLastIndex
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

Ltac make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex:=
  match goal with
  | [ |- Sharpened (@BuildADT (UnConstrQueryStructure ?sch) _ _ _ _ _ _ )] =>
    let sch' := eval simpl in (qschemaSchemas sch) in
        makeIndex' sch' attrlist
                   BuildEarlyIndex BuildLastIndex
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
    let H := fresh in
    assert (H : s = fd) by reflexivity; clear H;
    assert (H : kind = IndexType) by reflexivity; clear H;
    k X
  | (?fds1, ?fds2) => findMatchingTerm fds1 kind s k || findMatchingTerm fds2 kind s k
  end.
