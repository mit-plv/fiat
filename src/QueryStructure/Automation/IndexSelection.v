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

Class TermAttributeCounter {A : Type}
      (qsSchema : RawQueryStructureSchema)
      (a : A)
      (Ridx : Fin.t _)
      (BAidx : @Attributes (Vector.nth (Vector.map rawSchemaHeading (qschemaSchemas qsSchema)) Ridx))
  := { }.

Global Instance GetAttributeRawTermCounter {qsSchema}
         {Ridx : Fin.t _}
         {tup : @RawTuple (Vector.nth _ Ridx)}
         {BAidx : _ }
  : (TermAttributeCounter qsSchema (@GetAttributeRaw _ tup BAidx) Ridx BAidx) | 0 := {| |}.

(*Ltac TermAttributes Term k :=
  match Term with
  | fun tups => @GetAttributeRaw _ (@?f tups) ?BAidx =>
    let Aidx := eval simpl in BAidx in
        match type of f with
        | _ -> @RawTuple (Vector.nth _ ?Ridx) =>
          k Ridx Aidx
        end
  end. *)

Class ExpressionAttributeCounter
      {A : Type}
      (qsSchema : RawQueryStructureSchema)
      (a : A)
      (occCount : OccurencesCountT (Vector.map rawSchemaHeading (qschemaSchemas qsSchema))) := { }.

(*Instance ExpressionAttributeCounterAnyT {A}
         {qsSchema}
         {a : A}
  : @ExpressionAttributeCounter _ qsSchema a
                                (InitOccurences _) | 100 :=
  @Build_ExpressionAttributeCounter A qsSchema a (InitOccurences _). *)

Global Instance ExpressionAttributeCounter_And
         {qsSchema : RawQueryStructureSchema}
         {A B}
         {OccCountL OccCountR}
         (ExpCountL : @ExpressionAttributeCounter _ qsSchema A OccCountR)
         (ExpCountR : @ExpressionAttributeCounter _ qsSchema B OccCountL)
  : @ExpressionAttributeCounter _ qsSchema (A /\ B) (MergeOccurences OccCountL OccCountR) := { }.

Instance ExpressionAttributeCounterEqLR {A }
         {qsSchema : RawQueryStructureSchema}
         {a a' : A}
         (RidxL RidxR : Fin.t _)
         (BAidxL : @Attributes (Vector.nth _ RidxL))
         (BAidxR : @Attributes (Vector.nth _ RidxR))
         (ExpCountL : @TermAttributeCounter _ qsSchema a RidxL BAidxL)
         (ExpCountR : @TermAttributeCounter _ qsSchema a' RidxR BAidxR)
  : @ExpressionAttributeCounter _ qsSchema (a = a')
                                (@InsertOccurenceOfAny _ _ RidxL (EqualityIndex, BAidxL) (@InsertOccurenceOfAny _ _ RidxR (EqualityIndex, BAidxR) (InitOccurences _))) | 0 := { }.

Instance ExpressionAttributeCounterEqL {A }
         {qsSchema}
         {a a' : A}
         (RidxL : Fin.t _)
         (BAidxL : @Attributes (Vector.nth _ RidxL))
         (ExpCountL : @TermAttributeCounter _ qsSchema a RidxL BAidxL)
  : @ExpressionAttributeCounter _ qsSchema (a = a')
                                (@InsertOccurenceOfAny _ _ RidxL (EqualityIndex, BAidxL) (InitOccurences _)) | 10 := { }.

Instance ExpressionAttributeCounterEqR {A }
         {qsSchema}
         {a a' : A}
         (RidxR : Fin.t _)
         (BAidxR : @Attributes (Vector.nth _ RidxR))
         (ExpCountL : @TermAttributeCounter _ qsSchema a' RidxR BAidxR)
  : @ExpressionAttributeCounter _ qsSchema (a = a')
                                (@InsertOccurenceOfAny _ _ RidxR (EqualityIndex, BAidxR) (InitOccurences _)) | 10 := { }.

Instance ExpressionAttributeCounterWhere {ResultT}
         {qsSchema : RawQueryStructureSchema}
         {qs : UnConstrQueryStructure qsSchema}
         (P : Prop)
         (WhereBody : Comp (list ResultT))
         OccCountCond
         OccCountBody
         (ExpCountCond : @ExpressionAttributeCounter _ qsSchema P OccCountCond)
         (ExpCountBody : @ExpressionAttributeCounter _ qsSchema WhereBody OccCountBody)
  : @ExpressionAttributeCounter _ qsSchema
                                (Query_Where P WhereBody) (MergeOccurences OccCountCond OccCountBody) | 0 := { }.

Definition ExpressionAttributeCounterPick {A}
         {qsSchema : QueryStructureSchema}
         (P : Ensemble A)
  : ExpressionAttributeCounter qsSchema (Pick P)
                                (InitOccurences _) :=
  Build_ExpressionAttributeCounter qsSchema (Pick P) (InitOccurences _).

Hint Extern 10 (ExpressionAttributeCounter ?qsSchema (Pick ?P) _) =>
apply ExpressionAttributeCounterPick.

Hint Extern 0 (@TermAttributeCounter _ ?qsSchema (@GetAttributeRaw _ ?tup ?BAidx) ?Ridx' ?BAidx') =>
  match type of tup with
  | @RawTuple (@GetNRelSchemaHeading _ _ ?Ridx) =>
    unify Ridx Ridx'; unify BAidx BAidx'; (* have to unify these evars for the lemma to apply*)
    eapply (@GetAttributeRawTermCounter qsSchema Ridx tup BAidx)
  end : typeclass_instances.

Hint Extern 0 (@TermAttributeCounter
                 _ ?qsSchema
                 (GetAttribute ?tup {| bindex := _;
                                       indexb := {| ibound := ?BAidx;
                                                    boundi := _ |} |} ) ?Ridx' ?BAidx') =>
      match type of tup with
      | @RawTuple (@GetNRelSchemaHeading _ _ ?Ridx) =>
        unify Ridx Ridx'; unify BAidx BAidx'; (* have to unify these evars for the lemma to apply*)
        eapply (@GetAttributeRawTermCounter qsSchema Ridx tup BAidx)
      end : typeclass_instances.


Instance ExpressionAttributeCounterQueryIn {ResultT}
         {qsSchema : RawQueryStructureSchema}
         {qs : UnConstrQueryStructure qsSchema}
         (Ridx : Fin.t _)
         (QueryBody : RawTuple -> Comp (list ResultT))
         OccCount
         (ExpCountBod : forall tup,
             @ExpressionAttributeCounter _ qsSchema (QueryBody tup) OccCount)
  : @ExpressionAttributeCounter _ qsSchema
                                (@UnConstrQuery_In ResultT qsSchema qs Ridx QueryBody) OccCount | 0 := { }.

Instance ExpressionAttributeCounterBind {A B}
         {qsSchema : RawQueryStructureSchema}
         (ca : Comp A)
         (cb : A -> Comp B)
         OccCountA OccCountB
         (ExpCountA : @ExpressionAttributeCounter _ qsSchema ca OccCountA)
         (ExpCountB : forall a, @ExpressionAttributeCounter _ qsSchema (cb a) OccCountB)
  : @ExpressionAttributeCounter _ qsSchema
                                (Bind ca cb)
                                (MergeOccurences OccCountA OccCountB) | 0 := { }.

Instance ExpressionAttributeCounterFor {A}
         {qsSchema : RawQueryStructureSchema}
         (c : Comp (list A))
         OccCountA
         (ExpCountA : @ExpressionAttributeCounter _ qsSchema c OccCountA)
  : @ExpressionAttributeCounter _ qsSchema
                                (For c)
                                OccCountA | 0 := { }.

Instance ExpressionAttributeCounterCount {A}
         {qsSchema : RawQueryStructureSchema}
         (c : Comp (list A))
         OccCountA
         (ExpCountA : @ExpressionAttributeCounter _ qsSchema c OccCountA)
  : @ExpressionAttributeCounter _ qsSchema
                                (Count c)
                                OccCountA | 0 := { }.

Instance ExpressionAttributeCounterMaxN
         {qsSchema : RawQueryStructureSchema}
         (c : Comp (list N))
         OccCountA
         (ExpCountA : @ExpressionAttributeCounter _ qsSchema c OccCountA)
  : @ExpressionAttributeCounter _ qsSchema
                                (MaxN c)
                                OccCountA | 0 := { }.

Instance ExpressionAttributeCounterMaxZ
         {qsSchema : RawQueryStructureSchema}
         (c : Comp (list Z))
         OccCountA
         (ExpCountA : @ExpressionAttributeCounter _ qsSchema c OccCountA)
  : @ExpressionAttributeCounter _ qsSchema
                                (MaxZ c)
                                OccCountA | 0 := { }.

Instance ExpressionAttributeCounterSumN
         {qsSchema : RawQueryStructureSchema}
         (c : Comp (list N))
         OccCountA
         (ExpCountA : @ExpressionAttributeCounter _ qsSchema c OccCountA)
  : @ExpressionAttributeCounter _ qsSchema
                                (SumN c)
                                OccCountA | 0 := { }.

Instance ExpressionAttributeCounterSumZ
         {qsSchema : RawQueryStructureSchema}
         (c : Comp (list Z))
         OccCountA
         (ExpCountA : @ExpressionAttributeCounter _ qsSchema c OccCountA)
  : @ExpressionAttributeCounter _ qsSchema
                                (SumZ c)
                                OccCountA | 0 := { }.

Instance ExpressionAttributeCounterIfThenElse {A}
         {qsSchema : RawQueryStructureSchema}
         (ci : bool)
         (ct ce : Comp A)
         OccCountT (*OccCountE *)
         (ExpCountT : @ExpressionAttributeCounter _ qsSchema ct OccCountT)
         (*ExpCountE : @ExpressionAttributeCounter _ qsSchema ce OccCountE*)
  : @ExpressionAttributeCounter _ qsSchema
                                (If_Then_Else ci ct ce)
                                (MergeOccurences OccCountT OccCountE) | 0 := { }.

Instance ExpressionAttributeCounterifthenelse {A}
         {qsSchema : RawQueryStructureSchema}
         (ci : bool)
         (ct ce : Comp A)
         OccCountT OccCountE
         (ExpCountT : @ExpressionAttributeCounter _ qsSchema ct OccCountT)
         (ExpCountE : @ExpressionAttributeCounter _ qsSchema ce OccCountE)
  : @ExpressionAttributeCounter _ qsSchema
                                (if ci then ct else ce)
                                (MergeOccurences OccCountT OccCountE) | 0 := { }.

Instance ExpressionAttributeCounterIfOptThenElse {A B}
         {qsSchema : RawQueryStructureSchema}
         (ci : option A)
         (ct : A -> Comp B)
         (ce : Comp B)
         OccCountT OccCountE
         (ExpCountT : forall a,
             @ExpressionAttributeCounter _ qsSchema (ct a) OccCountT)
         (ExpCountE : @ExpressionAttributeCounter _ qsSchema ce OccCountE)
  : @ExpressionAttributeCounter _ qsSchema
                                (If_Opt_Then_Else ci ct ce)
                                (MergeOccurences OccCountT OccCountE) | 0 := { }.

Instance ExpressionAttributeCounterReturn {A}
         {qsSchema}
         {a : A}
  : ExpressionAttributeCounter qsSchema (Return a)
                                (InitOccurences _) | 0 :=
  Build_ExpressionAttributeCounter qsSchema (Return a) (InitOccurences _).

Instance ExpressionAttributeCounterRet {A}
         {qsSchema}
         {a : A}
  : ExpressionAttributeCounter qsSchema (ret a)
                                (InitOccurences _) | 0 :=
  Build_ExpressionAttributeCounter qsSchema (ret a) (InitOccurences _).

Instance ExpressionAttributeCounterEmpty
         {qsSchema : QueryStructureSchema}
  : ExpressionAttributeCounter qsSchema (QSEmptySpec qsSchema)
                                (InitOccurences _) | 0 :=
  Build_ExpressionAttributeCounter qsSchema (QSEmptySpec qsSchema) (InitOccurences _).


Instance ExpressionAttributeCounterConstructorsCons
         {qsSchema : RawQueryStructureSchema}
         {Dom}
         {n n'}
         (consSigs : Vector.t consSig n)
         (methSigs : Vector.t methSig n')
         (consDefs : @ilist consSig (@consDef (UnConstrQueryStructure qsSchema)) n consSigs)
         (methDefs : @ilist methSig (@methDef (UnConstrQueryStructure qsSchema)) n' methSigs)
         (con : @consDef _ Dom)
         OccCountC OccCountRest
         (ExpCountC : forall d,
             @ExpressionAttributeCounter _ qsSchema (consBody con d) OccCountC)
         (ExpCountRest : @ExpressionAttributeCounter _ qsSchema
                                (BuildADT (Rep := UnConstrQueryStructure qsSchema) consDefs methDefs)
                                OccCountRest)
  : @ExpressionAttributeCounter _ qsSchema
                                (BuildADT (Rep := UnConstrQueryStructure qsSchema) (icons con consDefs) methDefs)
                                (MergeOccurences OccCountC OccCountRest) | 0 := { }.

Instance ExpressionAttributeCounterMethodsCons
         {qsSchema : RawQueryStructureSchema}
         {mSig}
         {n'}
         (methSigs : Vector.t methSig n')
         (methDefs : @ilist methSig (@methDef (UnConstrQueryStructure qsSchema)) n' methSigs)
         (meth : @methDef (UnConstrQueryStructure qsSchema) mSig)
         OccCountM OccCountRest
         (ExpCountM : forall r d,
             @ExpressionAttributeCounter _ qsSchema (methBody meth r d) OccCountM)
         (ExpCountRest : @ExpressionAttributeCounter _ qsSchema
                                (BuildADT (Rep := UnConstrQueryStructure qsSchema) inil methDefs)
                                OccCountRest)
  : @ExpressionAttributeCounter _ qsSchema
                                (BuildADT (Rep := UnConstrQueryStructure qsSchema) inil (icons meth methDefs))
                                (MergeOccurences OccCountM OccCountRest) | 0 := { }.

Instance ExpressionAttributeCounterMethodsNil
         {qsSchema : RawQueryStructureSchema}
  : @ExpressionAttributeCounter _ qsSchema
                                (BuildADT (Rep := UnConstrQueryStructure qsSchema) inil inil)
                                (InitOccurences _) | 0 := { }.


Instance ExpressionAttributeCounter_True
         {qsSchema : RawQueryStructureSchema}
  : @ExpressionAttributeCounter _ qsSchema True (InitOccurences _) := { }.

Instance ExpressionAttributeCounter_Not
         {qsSchema : RawQueryStructureSchema}
         (P : Prop)
  : @ExpressionAttributeCounter _ qsSchema (~ P) (InitOccurences _) := { }.

Ltac make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex:=
  match goal with
  | [ |- Sharpened (@BuildADT (UnConstrQueryStructure ?sch) _ _ _ _ _ _ ) ] =>
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

  Ltac GenerateIndexesForAll k :=
    match goal with
      |- context [@BuildADT (UnConstrQueryStructure ?qsSchema) _ _ ?consSigs ?methSigs ?consDefs ?methDefs ] =>
      makeEvar (OccurencesCountT
                  (Vector.map rawSchemaHeading (qschemaSchemas qsSchema)))
               ltac:(fun e => let H := fresh in
                              assert (@ExpressionAttributeCounter _ qsSchema (@BuildADT _ _ _ consSigs methSigs consDefs methDefs) e) as H by eauto 200 with typeclass_instances;
                     clear H;
                     k e
                  )
  end.

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
