Require Import Coq.Lists.List Coq.Program.Program
        Coq.Bool.Bool Coq.Strings.String
        Coq.Structures.OrderedTypeEx Coq.Arith.Arith
        Fiat.Common.ilist3
        Fiat.Common.i3list
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Computation
        Fiat.ADT
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT.

Require Export Fiat.Common.ilist3_pair
        Fiat.Common.ilist3
        Fiat.Common.i3list2
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagImplementation.

Import Lists.List.ListNotations.

Ltac list_of_evar B As k :=
  match As with
  | nil => k (@nil B)
  | cons ?a ?As' =>
    makeEvar B ltac:(fun b =>
                       list_of_evar
                         B As' ltac:(fun Bs => k (cons b Bs)))
  end.

Lemma ValidUpdateCorrect
  : forall (A : Prop), false = true -> A.
Proof.
  intros; discriminate.
Qed.

(*Definition foo := (SharpenedBagImpl
                     (fun
                         _ : IndexedTreeUpdateTermType
                               {|
                                 NumAttr := 2;
                                 AttrList := [nat : Type; nat : Type]%NamedSchema |} =>
                         false)
                     (NatTreeBag.IndexedBagAsCorrectBag
                        (CountingListAsBag
                           (IndexedTreebupdate_transform
                              {|
                                NumAttr := 2;
                                AttrList := [nat : Type; nat : Type]%NamedSchema |}))
                        CountingList_RepInv CountingList_ValidUpdate
                        (CountingListAsCorrectBag
                           (IndexedTreebupdate_transform
                              {|
                                NumAttr := 2;
                                AttrList := [nat : Type; nat : Type]%NamedSchema |}))
                        (fun x : RawTuple => GetAttributeRaw x Fin.F1))
                     (fun
                         (a : IndexedTreeUpdateTermType
                                {|
                                  NumAttr := 2;
                                  AttrList := [nat : Type; nat : Type]%NamedSchema |})
                         (b : false = true) =>
                         ValidUpdateCorrect
                           (NatTreeBag.IndexedBag_ValidUpdate
                              (CountingListAsBag
                                 (IndexedTreebupdate_transform
                                    {|
                                      NumAttr := 2;
                                      AttrList := [nat : Type; nat : Type]%NamedSchema |}))
                              CountingList_ValidUpdate
                              (fun x : RawTuple =>
                                 GetAttributeRaw x Fin.F1) a) b)). *)

Section QueryStructureImplementation.

  Variable qs_schema : RawQueryStructureSchema.

  (* Build an index requires search terms and matchers for each schema,
     and update terms and updaters for each schema. *)

  Record SearchUpdateTerms (heading : RawHeading) :=
    {  BagSearchTermType : Type;
       BagMatchSearchTerm : BagSearchTermType -> @RawTuple heading -> bool;
       BagUpdateTermType : Type;
       BagApplyUpdateTerm : BagUpdateTermType -> @RawTuple heading -> @RawTuple heading }.

  Variable BagIndexKeys :
    ilist3 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns))
           (qschemaSchemas qs_schema).

  Definition IndexedQueryStructure
    := i3list  (fun ns index => Rep (BagSpec (BagMatchSearchTerm index)
                                             (BagApplyUpdateTerm index)))
               BagIndexKeys.

  Definition GetIndexedRelation (r_n : IndexedQueryStructure) idx
    := i3th r_n idx.

  Definition BagEmpty
             {heading : RawHeading} {index : SearchUpdateTerms heading}
    : (ConstructorIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := ConstructorNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index))) {| bindex := "Empty" |}).

  Definition BagEnumerate
             {heading : RawHeading} {index : SearchUpdateTerms heading}
    : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
                      {| bindex := "Enumerate" |}).

  Definition BagFind
             {heading : RawHeading} {index : SearchUpdateTerms heading}
    : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
                      {| bindex := "Find" |}).

  Definition BagCount
             {heading : RawHeading} {index : SearchUpdateTerms heading}
    : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index))) {| bindex := "Count" |}).

  Definition BagInsert
             {heading : RawHeading} {index : SearchUpdateTerms heading}
    : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
                      {| bindex := "Insert" |}).

  Definition BagUpdate
             {heading : RawHeading} {index : SearchUpdateTerms heading}
    : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
                      {| bindex := "Update" |}).

  Definition BagDelete
             {heading : RawHeading} {index : SearchUpdateTerms heading}
    : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
                      {| bindex := "Delete" |}).

  Definition CallBagMethod idx midx r_n :=
    Methods (BagSpec (BagMatchSearchTerm (ith3 BagIndexKeys idx))
                     (BagApplyUpdateTerm (ith3 BagIndexKeys idx)))
            midx
            (GetIndexedRelation r_n idx).

  Definition CallBagConstructor {heading} index cidx :=
    Constructors (BagSpec (BagMatchSearchTerm (heading := heading) index)
                          (BagApplyUpdateTerm index))
                 cidx.

  Definition DelegateToBag_AbsR
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : IndexedQueryStructure) :=
    (*forall idx, GetUnConstrRelation r_o idx = GetIndexedRelation r_n idx*)
    (* This invariant allows us to justify refinements which drop
       unused method calls by showing that they are implementable. *)
    (forall idx,
        exists l, EnsembleIndexedListEquivalence (GetUnConstrRelation r_o idx) l /\
                  EnsembleIndexedListEquivalence (GetIndexedRelation r_n idx) l).

  Fixpoint Initialize_IndexedQueryStructure
           {n}
           (ns : Vector.t RawSchema n)
           (indices' : ilist3 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns)) ns)
           {struct ns}
    : Comp (i3list (fun ns index => Rep (BagSpec (BagMatchSearchTerm index)
                                                 (BagApplyUpdateTerm index))) indices').
  Proof.
    refine (match ns in (Vector.t _ n) return
                  forall indices' : ilist3 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns)) ns,
                    Comp (i3list (fun ns index =>
                                    Rep (BagSpec (BagMatchSearchTerm index)
                                                 (BagApplyUpdateTerm index))) indices') with
            | Vector.nil => fun il => ret (i3nil (C := (fun ns index =>
                                                          Rep (BagSpec (BagMatchSearchTerm (heading := ns) index)
                                                                       (BagApplyUpdateTerm index)))))
            | Vector.cons sch _ ns' =>
              fun il =>
                c <- _;
            cs <- (@Initialize_IndexedQueryStructure _ ns' (ilist3_tl il) );
            ret (i3cons c cs)
            end indices').
    exact (CallBagConstructor (ilist3_hd il) BagEmpty).
  Defined.

  Record EquivSearchTerm
        {heading : RawHeading}
        (SearchTerms : SearchUpdateTerms heading)
        (P : Ensemble (@RawTuple heading))
        (Patterns : list _)
    := { OK_search_pattern :
           forall tup Pattern,
             List.In Pattern Patterns
             -> decides (BagMatchSearchTerm SearchTerms Pattern tup) (P tup) }.

  (*Global Instance EquivSearchTerm_DecideableEnsemble
           {heading : RawHeading}
           (SearchTerms : SearchUpdateTerms heading)
           (P : Ensemble (@RawTuple heading))
           Patterns
           (EquivSearchTerm' : EquivSearchTerm SearchTerms P Patterns)
    : DecideableEnsemble P :=
    {| dec := BagMatchSearchTerm SearchTerms search_pattern |}.
  Proof.
    abstract (intros; pose proof (OK_search_pattern a);
              destruct (BagMatchSearchTerm SearchTerms search_pattern a);
              simpl in *; intuition eauto;
              discriminate).
  Defined. *)

  Lemma EquivSearchTerm_True
        {heading : RawHeading}
        (SearchTermT' : SearchUpdateTerms heading)
        Patterns
        {eqv_st' : EquivSearchTerm SearchTermT' (fun _ => True) Patterns}
    : forall tup Pattern,
      List.In Pattern Patterns
      -> BagMatchSearchTerm SearchTermT' Pattern tup = true.
  Proof.
    intros.
    pose proof (OK_search_pattern eqv_st' tup Pattern H).
    destruct (BagMatchSearchTerm SearchTermT' _ tup); eauto.
  Qed.

  Lemma EquivSearchTerm_App
        {heading : RawHeading}
        {SearchTermT' : SearchUpdateTerms heading}
        {P : Ensemble (@RawTuple heading)}
        {Patterns1 Patterns2}
        (eqv_Patterns1 : EquivSearchTerm SearchTermT' P Patterns1)
        (eqv_Patterns2 : EquivSearchTerm SearchTermT' P Patterns2)
    : EquivSearchTerm SearchTermT' P (Patterns1 ++ Patterns2).
  Proof.
    econstructor; intros.
    apply in_app_or in H; intuition.
    eauto using (OK_search_pattern eqv_Patterns1).
    eauto using OK_search_pattern.
  Qed.

  Lemma EquivSearchTerm_App'
        {heading : RawHeading}
        {SearchTermT' : SearchUpdateTerms heading}
        {P : Ensemble (@RawTuple heading)}
        {Patterns1 Patterns2}
        (eqv_Patterns1 : EquivSearchTerm SearchTermT' P (Patterns1 ++ Patterns2))
    : EquivSearchTerm SearchTermT' P Patterns1.
  Proof.
    econstructor; intros.
    eauto using in_or_app, OK_search_pattern.
  Qed.

  Lemma EquivSearchTerm_Permute
        {heading : RawHeading}
        (SearchTermT' : SearchUpdateTerms heading)
        (P : Ensemble (@RawTuple heading))
        Patterns1 Patterns2
        {eqv_Patterns1 : EquivSearchTerm SearchTermT' P Patterns1}
    : Permutation Patterns1 Patterns2
              -> EquivSearchTerm SearchTermT' P Patterns1.
  Proof.
    econstructor; intros.
    eauto using Permutation_in, OK_search_pattern.
  Qed.

  Definition Equiv_Any
             {heading : RawHeading}
             SearchTerms
             P
    : EquivSearchTerm (heading := heading) SearchTerms P [].
  Proof.
    econstructor; intros; simpl in *; intuition.
  Qed.

  Definition Equiv_Any_Dec
           {heading : RawHeading}
           P
           {P_dec : DecideableEnsemble P}
    : EquivSearchTerm
        {| BagSearchTermType := @RawTuple heading -> bool;
           BagMatchSearchTerm :=
             fun f => f;
           BagApplyUpdateTerm :=
             fun upd => upd
        |}
        P
        [dec].
  Proof.
    econstructor; intros; simpl.
    unfold List.In in H; intuition; subst.
    case_eq (dec tup); simpl.
    - intros; eapply dec_decides_P; eauto.
    - intros; eapply Decides_false; eauto.
  Qed.

  Definition Equiv_Any_True
           {heading : RawHeading}
    : EquivSearchTerm
        {| BagSearchTermType := @RawTuple heading -> bool;
           BagMatchSearchTerm :=
             fun f => f;
           BagApplyUpdateTerm :=
             fun upd => upd
        |}
        (fun _ => True)
        [fun _ => true].
  Proof.
    econstructor; unfold List.In;
    intuition; subst; intros; simpl; intuition.
  Qed.

  Definition Equiv_Comm
         {heading : RawHeading}
         P Q BagSearchUpdateTerms Patterns
         {_ : EquivSearchTerm (heading := heading)
                              BagSearchUpdateTerms (fun r => Q r /\ P r) Patterns}
    : EquivSearchTerm BagSearchUpdateTerms (fun r => P r /\ Q r) Patterns.
  Proof.
    econstructor; intros; simpl.
    pose proof (OK_search_pattern H tup Pattern H0).
    destruct (BagMatchSearchTerm BagSearchUpdateTerms Pattern tup); simpl in *;
    intuition.
  Qed.

Definition CombineSearchTerm A B := prod (option A) (option B).
Definition MatchCombineSearchTerm
           {heading}
           {SearchTerm1 SearchTerm2}
           (Matcher1 : SearchTerm1 -> @RawTuple heading -> bool)
           (Matcher2 : SearchTerm2 -> @RawTuple heading -> bool)
           (st : CombineSearchTerm SearchTerm1 SearchTerm2)
           (tup : @RawTuple heading)
    : bool :=
    match st with
    | (Some st1, Some st2) => Matcher1 st1 tup && Matcher2 st2 tup
    | (None, Some st2) => Matcher2 st2 tup
    | (Some st1, None) => Matcher1 st1 tup
    | _ => true
    end.

  Definition filter_None {A} (a : option A) : bool :=
    match a with
    | Some _ => false
    | None => true
    end.

  Definition merge_SearchTerm {A B}
             (st : CombineSearchTerm A B)
             (st' : list B)
    : list (CombineSearchTerm A B) :=
    match st with
    | (a, None) => map (fun b => (a, Some b)) st'
    | _ => []
    end.

  Definition merge_SearchTerms {A B}
             (st : list (CombineSearchTerm A B))
             (st' : list B)
    : list (CombineSearchTerm A B) :=
    fold_right (fun st acc => (merge_SearchTerm st st') ++ acc) [] st.

  Lemma In_mergeSearchTerm_MatchCombineSearchTerm
        {SearchTermT1 SearchTermT2 : Type}
    : forall Pattern (a : CombineSearchTerm SearchTermT1 SearchTermT2) (st : list _),
      List.In Pattern (merge_SearchTerm a st)
      -> exists st' : SearchTermT2,
        List.In st' st /\ Pattern = (fst a, Some st') /\ snd a = None.
  Proof.
    intros.
    destruct a as [a [ ? | ] ]; simpl in *; intuition.
    rewrite in_map_iff in H; destruct_ex; intuition subst; eauto.
  Qed.

  Definition Equiv_Ignore_First
         {heading : RawHeading}
         P
         {SearchTermT1 SearchTermT2 : Type}
         (Matcher1 : SearchTermT1 -> @RawTuple heading -> bool)
         (Matcher2 : SearchTermT2 -> @RawTuple heading -> bool)
         UpdateTermT ApplyUpdateTerm
         (BagSearchUpdateTerms :=
            {| BagSearchTermType := CombineSearchTerm SearchTermT1 SearchTermT2;
               BagMatchSearchTerm := MatchCombineSearchTerm Matcher1 Matcher2;
               BagUpdateTermType := UpdateTermT;
               BagApplyUpdateTerm := ApplyUpdateTerm
            |})
         (BagSearchUpdateTerms' :=
            {| BagSearchTermType := SearchTermT2;
               BagMatchSearchTerm := Matcher2;
               BagUpdateTermType := UpdateTermT;
               BagApplyUpdateTerm := ApplyUpdateTerm
            |})
         (st : list SearchTermT2)
         (Equiv_st : EquivSearchTerm BagSearchUpdateTerms' P st)
    : EquivSearchTerm BagSearchUpdateTerms P (merge_SearchTerms [(None, None)] st).
  Proof.
    econstructor; induction st; simpl in *; intros; intuition eauto.
    - subst; simpl.
      eapply (OK_search_pattern Equiv_st); simpl; intuition.
    - eapply IHst; eauto.
      econstructor; intros; eapply (OK_search_pattern Equiv_st);
      simpl; intuition.
  Qed.

  Definition Equiv_And_SplitL
         {heading : RawHeading}
         P Q
         {SearchTermT1 SearchTermT2 : Type}
         (Matcher1 : SearchTermT1 -> @RawTuple heading -> bool)
         (Matcher2 : SearchTermT2 -> @RawTuple heading -> bool)
         UpdateTermT ApplyUpdateTerm
         (BagSearchUpdateTerms :=
            {| BagSearchTermType := CombineSearchTerm SearchTermT1 SearchTermT2;
               BagMatchSearchTerm := MatchCombineSearchTerm Matcher1 Matcher2;
               BagUpdateTermType := UpdateTermT;
               BagApplyUpdateTerm := ApplyUpdateTerm
            |})
         (BagSearchUpdateTerms' :=
            {| BagSearchTermType := SearchTermT2;
               BagMatchSearchTerm := Matcher2;
               BagUpdateTermType := UpdateTermT;
               BagApplyUpdateTerm := ApplyUpdateTerm
            |})
         (st : list (CombineSearchTerm SearchTermT1 SearchTermT2))
         (st' : list SearchTermT2)
         (Equiv_st : EquivSearchTerm
                       BagSearchUpdateTerms (fun r => P r) st)
         (Equiv_st'' : EquivSearchTerm
                         BagSearchUpdateTerms' (fun r => Q r) st')
    : EquivSearchTerm BagSearchUpdateTerms (fun r => P r /\ Q r) (merge_SearchTerms st st').
  Proof.
    econstructor; induction st; simpl in *; intros; intuition.
    apply in_app_or in H; intuition eauto.
    - eapply In_mergeSearchTerm_MatchCombineSearchTerm in H0;
      destruct_ex; destruct a; destruct o; simpl in *; intuition subst;
      unfold MatchCombineSearchTerm; simpl.
      + pose proof (OK_search_pattern Equiv_st tup (Some s, None)).
        pose proof (OK_search_pattern Equiv_st'' tup x H0).
        simpl in *; unfold MatchCombineSearchTerm in *; simpl in *.
        destruct (Matcher1 s tup); simpl in *; intuition.
        simpl in *; destruct (Matcher2 x tup); simpl in *; intuition.
      + pose proof (OK_search_pattern Equiv_st tup (None, None)).
        pose proof (OK_search_pattern Equiv_st'' tup x H0).
        simpl in *; unfold MatchCombineSearchTerm in *; simpl in *.
        simpl in *; destruct (Matcher2 x tup); simpl in *; intuition.
    - eapply IHst; eauto.
      econstructor; intros; eapply (OK_search_pattern Equiv_st);
      simpl; intuition.
  Qed.

  Definition  Equiv_And_Comm
         {heading : RawHeading}
         P Q
         {SearchTermT1 SearchTermT2 : Type}
         (Matcher1 : SearchTermT1 -> @RawTuple heading -> bool)
         (Matcher2 : SearchTermT2 -> @RawTuple heading -> bool)
         UpdateTermT ApplyUpdateTerm
         (BagSearchUpdateTerms :=
            {| BagSearchTermType := CombineSearchTerm SearchTermT1 SearchTermT2;
               BagMatchSearchTerm := MatchCombineSearchTerm Matcher1 Matcher2;
               BagUpdateTermType := UpdateTermT;
               BagApplyUpdateTerm := ApplyUpdateTerm
            |})
         (st : list (CombineSearchTerm SearchTermT1 SearchTermT2))
         (Equiv_st : EquivSearchTerm BagSearchUpdateTerms (fun r => Q r /\ P r) st)
    : EquivSearchTerm BagSearchUpdateTerms (fun r => P r /\ Q r) st.
  Proof.
    econstructor; simpl in *; intros.
    pose proof (OK_search_pattern Equiv_st tup Pattern H).
    unfold decides, If_Then_Else in *; simpl in *; find_if_inside;
    intuition.
  Qed.

  Definition Equiv_And_Assoc
         {heading : RawHeading}
         P Q R
         {SearchTermT1 SearchTermT2 : Type}
         (Matcher1 : SearchTermT1 -> @RawTuple heading -> bool)
         (Matcher2 : SearchTermT2 -> @RawTuple heading -> bool)
         UpdateTermT ApplyUpdateTerm
         (BagSearchUpdateTerms :=
            {| BagSearchTermType := CombineSearchTerm SearchTermT1 SearchTermT2;
               BagMatchSearchTerm := MatchCombineSearchTerm Matcher1 Matcher2;
               BagUpdateTermType := UpdateTermT;
               BagApplyUpdateTerm := ApplyUpdateTerm
            |})
         (st : list (CombineSearchTerm SearchTermT1 SearchTermT2))
         (Equiv_st : EquivSearchTerm BagSearchUpdateTerms (fun r => (P r /\ Q r) /\ R r) st)
    : EquivSearchTerm BagSearchUpdateTerms (fun r => P r /\ (Q r /\ R r)) st.
  Proof.
    econstructor; simpl in *; intros.
    pose proof (OK_search_pattern Equiv_st tup Pattern H).
    unfold decides, If_Then_Else in *; simpl in *; find_if_inside;
    intuition.
  Qed.

  Definition Equiv_And_SplitR
         {heading : RawHeading}
         P Q
         {SearchTermT1 SearchTermT2 : Type}
         (Matcher1 : SearchTermT1 -> @RawTuple heading -> bool)
         (Matcher2 : SearchTermT2 -> @RawTuple heading -> bool)
         UpdateTermT ApplyUpdateTerm
         (BagSearchUpdateTerms :=
            {| BagSearchTermType := CombineSearchTerm SearchTermT1 SearchTermT2;
               BagMatchSearchTerm := MatchCombineSearchTerm Matcher1 Matcher2;
               BagUpdateTermType := UpdateTermT;
               BagApplyUpdateTerm := ApplyUpdateTerm
            |})
         (BagSearchUpdateTerms' :=
            {| BagSearchTermType := SearchTermT2;
               BagMatchSearchTerm := Matcher2;
               BagUpdateTermType := UpdateTermT;
               BagApplyUpdateTerm := ApplyUpdateTerm
            |})
         (st : list (CombineSearchTerm SearchTermT1 SearchTermT2))
         (st' : list SearchTermT2)
         (Equiv_st : EquivSearchTerm
                       BagSearchUpdateTerms (fun r => Q r) st)
         (Equiv_st'' : EquivSearchTerm
                         BagSearchUpdateTerms' (fun r => P r) st')
    : EquivSearchTerm BagSearchUpdateTerms (fun r => P r /\ Q r) (merge_SearchTerms st st').
  Proof.
    econstructor; induction st; simpl in *; intros; intuition.
    apply in_app_or in H; intuition eauto.
    - eapply In_mergeSearchTerm_MatchCombineSearchTerm in H0;
      destruct_ex; destruct a; destruct o; simpl in *; intuition subst;
      unfold MatchCombineSearchTerm; simpl.
      + pose proof (OK_search_pattern Equiv_st tup (Some s, None)).
        pose proof (OK_search_pattern Equiv_st'' tup x H0).
        simpl in *; unfold MatchCombineSearchTerm in *; simpl in *.
        destruct (Matcher1 s tup); simpl in *; intuition.
        simpl in *; destruct (Matcher2 x tup); simpl in *; intuition.
      + pose proof (OK_search_pattern Equiv_st tup (None, None)).
        pose proof (OK_search_pattern Equiv_st'' tup x H0).
        simpl in *; unfold MatchCombineSearchTerm in *; simpl in *.
        simpl in *; destruct (Matcher2 x tup); simpl in *; intuition.
    - eapply IHst; eauto.
      econstructor; intros; eapply (OK_search_pattern Equiv_st);
      simpl; intuition.
  Qed.

  Definition Equiv_And_SplitBoth
           {heading : RawHeading}
           P Q
           {SearchTermT1 SearchTermT2 : Type}
           (Matcher1 : SearchTermT1 -> @RawTuple heading -> bool)
           (Matcher2 : SearchTermT2 -> @RawTuple heading -> bool)
           UpdateTermT ApplyUpdateTerm
           (BagSearchUpdateTerms :=
              {| BagSearchTermType := CombineSearchTerm SearchTermT1 SearchTermT2;
                 BagMatchSearchTerm := MatchCombineSearchTerm Matcher1 Matcher2;
                 BagUpdateTermType := UpdateTermT;
                 BagApplyUpdateTerm := ApplyUpdateTerm
              |})
           (BagSearchUpdateTerms' :=
              {| BagSearchTermType := SearchTermT2;
                 BagMatchSearchTerm := Matcher2;
                 BagUpdateTermType := UpdateTermT;
                 BagApplyUpdateTerm := ApplyUpdateTerm
              |})
           (l1 l1' : list (CombineSearchTerm SearchTermT1 SearchTermT2))
           (l2 l2' : list SearchTermT2)
           (Equiv_l1 : EquivSearchTerm
                         BagSearchUpdateTerms (fun r => Q r) l1)
           (Equiv_l1' : EquivSearchTerm
                          BagSearchUpdateTerms (fun r => P r) l1')
           (Equiv_l2 : EquivSearchTerm
                         BagSearchUpdateTerms' (fun r => P r) l2)
           (Equiv_l2' : EquivSearchTerm
                         BagSearchUpdateTerms' (fun r => Q r) l2')
    : EquivSearchTerm BagSearchUpdateTerms (fun r => P r /\ Q r)
                      ((merge_SearchTerms l1 l2) ++ (merge_SearchTerms l1' l2')).
  Proof.
    eapply @EquivSearchTerm_App.
    - eapply Equiv_And_SplitR; eauto.
    - eapply Equiv_And_SplitL; eauto.
  Qed.

  Create HintDb EquivSearchTerm_DB.

End QueryStructureImplementation.

(* Hint Extern 10 (EquivSearchTerm _ _ _) => *)
(* eapply Equiv_Any : EquivSearchTerm_DB. *)
(* Hint Extern 3 (EquivSearchTerm _ (fun _ => _ /\ _) _) => *)
(* eapply Equiv_And_Split : EquivSearchTerm_DB. *)
(* Hint Extern 6 (EquivSearchTerm _ (fun _ => _ /\ _) _) => *)
(* eapply Equiv_Comm : EquivSearchTerm_DB. *)

Opaque CallBagMethod.
Arguments CallBagMethod : simpl never.
Arguments CallBagMethod [_ _] _ _ _.
Opaque CallBagConstructor.
Arguments CallBagConstructor : simpl never.
Arguments GetIndexedRelation [_ _ ] _ _ _.
Arguments DelegateToBag_AbsR [_ _] _ _.
