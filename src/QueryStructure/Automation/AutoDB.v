Require Export Coq.Bool.Bool Coq.Strings.String
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.Common.ListMorphisms
        ADTSynthesis.Common.ListFacts
        ADTSynthesis.Common.BoolFacts
        ADTSynthesis.Common.LogicFacts
        ADTSynthesis.Common.FlattenList
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Common.IterateBoundedIndex
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagImplementation
        ADTSynthesis.QueryStructure.Implementation.ListImplementation
        ADTSynthesis.QueryStructure.Specification.Constraints.tupleAgree
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        ADTSynthesis.QueryStructure.Implementation.Operations.BagADT.Refinements
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

Require Export ADTSynthesis.QueryStructure.Implementation.Operations.

Global Opaque binsert benumerate bfind bcount.

Ltac prove_decidability_for_functional_dependencies :=
  simpl; econstructor; intros;
  try setoid_rewrite <- eq_nat_dec_bool_true_iff;
  try setoid_rewrite <- eq_N_dec_bool_true_iff;
  try setoid_rewrite <- eq_Z_dec_bool_true_iff;
  try setoid_rewrite <- string_dec_bool_true_iff;
  setoid_rewrite and_True;
  repeat progress (
           try setoid_rewrite <- andb_true_iff;
           try setoid_rewrite not_true_iff_false;
           try setoid_rewrite <- negb_true_iff);
  rewrite bool_equiv_true;
  reflexivity.

Hint Extern 100 (DecideableEnsemble _) => prove_decidability_for_functional_dependencies : typeclass_instances.

Ltac lmap A f seq :=
  let rec aux seq :=
      match seq with
        | nil => constr:(@nil A)
        | ?h :: ?t =>
          let h' := f h in
          let t' := aux t in
          constr:(h' :: t')
      end
  in aux seq.

Require Import ADTNotation.BuildComputationalADT.
Require Import ADT.ComputationalADT.

Ltac FullySharpenEachMethod delegateSigs delegateSpecs cRep' cAbsR' :=
  match goal with
      |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
      ilist_of_evar
        (ilist (fun nadt => ComputationalADT.cADT (namedADTSig nadt)) delegateSigs)
        (fun DelegateImpl Sig => ComputationalADT.cMethodType (cRep' DelegateImpl) (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths =>
                ilist_of_evar
                  (ilist (fun nadt => ComputationalADT.cADT (namedADTSig nadt)) delegateSigs)
                  (fun DelegateImpl Sig => ComputationalADT.cConstructorType (cRep' DelegateImpl) (consDom Sig))
                  consSigs
                  ltac:(fun cCons =>
                          eapply
                            (@Notation_Friendly_SharpenFully
                               _
                               consSigs
                               methSigs
                               consDefs
                               methDefs
                               delegateSigs
                               cRep'
                               cCons
                               cMeths
                               delegateSpecs
                               cAbsR')));
        unfold Dep_Type_BoundedIndex_app_comm_cons
  end; simpl; repeat split.

Definition Build_IndexedQueryStructure_Impl_Sigs
           {indices : list NamedSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           (idx : @BoundedString (map relName indices))
: ADTSig :=
  BagSig (@Tuple (schemaHeading (relSchema (nth_Bounded relName indices idx))))
         (BagSearchTermType (ith_Bounded _ Index idx))
         (BagUpdateTermType (ith_Bounded _ Index idx)).

Definition Build_IndexedQueryStructure_Impl_Specs
           {indices : list NamedSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           (idx : @BoundedString (map relName indices))
: ADT (@Build_IndexedQueryStructure_Impl_Sigs indices Index idx) :=
  @BagSpec (@Tuple (schemaHeading (relSchema (nth_Bounded relName indices idx))))
           (BagSearchTermType (ith_Bounded _ Index idx))
           (BagUpdateTermType (ith_Bounded _ Index idx))
           (BagMatchSearchTerm (ith_Bounded _ Index idx))
           (BagApplyUpdateTerm (ith_Bounded _ Index idx)).

Print BoundedIndex.

Fixpoint BoundedStringFun2StringFun {A}
         (a : A)
         (l : list string)
         (f : @BoundedString l -> A)
         {struct l} : string -> A :=
match l as l0 return ((BoundedString -> A) -> string -> A) with
  | [] => fun (_ : BoundedString -> A) (_ : string) => a
  | a' :: l' =>
      fun f' a'' =>
        if string_dec a' a''
        then
          f' {| bindex := a';
                indexb := {| ibound := 0;
                             boundi := @eq_refl _ (nth_error (a' :: l') 0)|} |}
        else
          BoundedStringFun2StringFun a 
                                     (fun i => f' {| bindex := bindex i;
                                                     indexb := @IndexBound_tail _ _ a' l' (indexb i) |})
                                     a''
  end f.

Print BoundedStringFun2StringFun.
Print BoundedIndex.


Definition
  Build_IndexedQueryStructure_Impl_cRep
  (indices : list NamedSchema)
  (Index : ilist
             (fun ns : NamedSchema =>
                SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
  (DelegateReps : @BoundedString (map relName indices) -> Type)
: Type :=
  ilist2 (map relName indices).
  forall (idx : @BoundedString (map relName indices)), DelegateReps idx.


Definition Build_IndexedQueryStructure_Impl_AbsR
           {qs_schema : QueryStructureSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
           (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
           (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           (ValidImpls
            : forall idx,
                refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                          (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx))))
           (r_o : IndexedQueryStructure qs_schema Index)
           (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps)
: Prop :=
  forall idx : @BoundedString (map relName (qschemaSchemas qs_schema)),
    AbsR (ValidImpls idx)
         (GetIndexedRelation r_o idx) (r_n idx).

  Definition Update_Build_IndexedQueryStructure_Impl_cRep
             qs_schema Index DelegateReps
             (r_n : Build_IndexedQueryStructure_Impl_cRep (indices := qs_schema) Index DelegateReps)
             TableID (r_n' : DelegateReps TableID)
  : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps.
    unfold Build_IndexedQueryStructure_Impl_cRep.
    refine (fun idx => match BoundedString_eq_dec TableID idx return DelegateReps idx with
                         | left eq' => _
                         | right eq' => r_n idx
                       end).
    rewrite eq' in r_n'; exact r_n'.
  Defined.

  Lemma Update_Build_IndexedQueryStructure_Impl_AbsR
  : forall qs_schema Index DelegateReps DelegateImpls
           ValidImpls r_o r_n TableID r_o' r_n',
      @Build_IndexedQueryStructure_Impl_AbsR qs_schema Index DelegateReps DelegateImpls
                                             ValidImpls r_o r_n
      -> AbsR (ValidImpls TableID) r_o' r_n'
      -> @Build_IndexedQueryStructure_Impl_AbsR
           qs_schema Index DelegateReps DelegateImpls
           ValidImpls (UpdateIndexedRelation r_o TableID r_o')
           (Update_Build_IndexedQueryStructure_Impl_cRep r_n TableID r_n').
  Proof.
    unfold Build_IndexedQueryStructure_Impl_AbsR,
    Update_Build_IndexedQueryStructure_Impl_cRep; intros.
    destruct (BoundedString_eq_dec TableID idx); subst.
    unfold eq_rect, UpdateIndexedRelation, GetIndexedRelation;
      rewrite i2th_replace_BoundIndex_eq; eassumption.
    unfold eq_rect, UpdateIndexedRelation, GetIndexedRelation;
      rewrite i2th_replace_BoundIndex_neq; eauto using string_dec.
  Qed.


Arguments BuildIndexSearchTerm : simpl never.
Arguments MatchIndexSearchTerm : simpl never.
Opaque Initialize_IndexedQueryStructure.

Ltac fields storage :=
  match eval cbv delta [storage] in storage with
    | let src := ?X in _ => X
  end.

Ltac prove_extensional_eq :=
  clear;
  unfold ExtensionalEq;
  destruct_ifs; first [ solve [intuition] | solve [exfalso; intuition] | idtac ].

(* Recurse over [fds] to find an attribute matching s *)
Ltac findMatchingTerm fds s k :=
  match fds with
    | (?fd, ?X) =>
      (* Check if this field name is equal to s; process [X] with [k] if so. *)
      let H := fresh in assert (H : bindex s = fd) by reflexivity; clear H;
                        k X
    | (?fds1, ?fds2) => findMatchingTerm fds1 s k || findMatchingTerm fds2 s k
  end.

(* Recurse over the list of search term attributes [fs],
 consulting the list of attribute name and value pairs in [fds] to
 find matching search terms via [findMatchingTerm].
 *)
Ltac createTerm f fds tail fs k :=
  match fs with
    | nil =>
      k tail
    | ?s :: ?fs' =>
      createTerm f fds tail fs' ltac:(fun rest =>
                                        findMatchingTerm fds s ltac:(fun X =>
                                                                       k (Some X, rest))
                                                                      || k (@None (f s), rest))
  end.

(* Using a list of search term attributes [fs],
   a list of attribute name and value pairs [fds],
   use [createTerm] to recurse over [fs]
   using the schema for [SC]
 *)
Ltac makeTerm fs SC fds tail k :=
  match eval hnf in SC with
    | Build_Heading ?f =>
      createTerm f fds tail fs k
  end.

(* Given a storage schema [SC], a filter [F],
   a list of indexed attributes [search_attrs] and a
   tactic [k] which processes filters, convert [F] into
   a search term (a list of boolean functions over the tuples in
   [SC]). *)

Ltac findGoodTerm SC F indexed_attrs k :=
  match F with
    | fun a => ?[@?f a] =>
      match type of f with
        | forall a, {?X = _!?fd} + {_} =>
          let H := fresh in
          assert (List.In fd indexed_attrs) as H
              by (clear; simpl; intuition);
            k (fd, X) (fun _ : @Tuple SC => true)
        | forall a, {_!?fd = ?X} + {_} =>
          let H := fresh in
          assert (List.In fd indexed_attrs) as H
              by (clear; simpl; intuition);
            k (fd, X) (fun _ : @Tuple SC => true)
        | forall a, {?X = _``?fd} + {_} =>
          let H := fresh in
          assert (List.In fd indexed_attrs) as H
              by (clear; simpl; intuition);
            k (fd, X) (fun _ : @Tuple SC => true)
        | forall a, {_``?fd = ?X} + {_} =>
          let H := fresh in
          assert (List.In fd indexed_attrs) as H
              by (clear; simpl; intuition);
            k (fd, X) (fun _ : @Tuple SC => true)
      end
    | fun a => (@?f a) && (@?g a) =>
      findGoodTerm SC f indexed_attrs
                   ltac:(fun fds1 tail1 =>
                           findGoodTerm SC g indexed_attrs
                                        ltac:(fun fds2 tail2 =>
                                                k (fds1, fds2) (fun tup : @Tuple SC => (tail1 tup) && (tail2 tup))))
    | _ => k tt F
  end.

Ltac find_simple_search_term qs_schema idx filter_dec search_term :=
  match type of search_term with
    | BuildIndexSearchTerm ?indexed_attrs =>
      let indexed_attrs' :=
          eval simpl in (map (@bindex string _) indexed_attrs) in
          let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
          findGoodTerm SC filter_dec indexed_attrs'
                       ltac:(fun fds tail =>
                               let tail := eval simpl in tail in
                                   makeTerm indexed_attrs SC fds tail
                                            ltac:(fun tm => try unify tm search_term;
                                                  unfold ExtensionalEq, MatchIndexSearchTerm;
                                                  simpl; intro; try prove_extensional_eq))
  end.

Ltac implement_QSDeletedTuples find_search_term :=
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[Pick (QSDeletedTuples ?r_o ?idx ?DeletedTuples)] ] =>
      let filter_dec := eval simpl in (@DecideableEnsembles.dec _ DeletedTuples _) in
          let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
              let search_term_type := eval simpl in (BagSearchTermType idx_search_update_term) in
                  let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                      makeEvar search_term_type
                               ltac: (fun search_term =>
                                        let eqv := fresh in
                                        assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                      [ find_search_term qs_schema idx filter_dec search_term
                                      | let H' := fresh in
                                        pose (@refine_BagADT_QSDelete_fst _ _ r_o r_n H idx DeletedTuples _ search_term) as H';
                                          setoid_rewrite (H' eqv); clear H' eqv])
  end.

Ltac implement_EnsembleDelete_AbsR find_search_term :=
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[{r_n' | DelegateToBag_AbsR
                             (UpdateUnConstrRelation ?r_o ?idx
                                                     (EnsembleDelete (GetUnConstrRelation ?r_o ?idx)
                                                                     ?DeletedTuples)) r_n'}]] =>
      let filter_dec := eval simpl in (@DecideableEnsembles.dec _ DeletedTuples _) in
          let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
              let search_term_type := eval simpl in (BagSearchTermType idx_search_update_term) in
                  let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                      makeEvar search_term_type
                               ltac:(fun search_term =>
                                       let eqv := fresh in
                                       assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                     [ find_search_term qs_schema idx filter_dec search_term
                                     | let H' := fresh in
                                       pose (@refine_BagADT_QSDelete_snd _ _ r_o r_n H idx DeletedTuples _ search_term) as H';
                                         setoid_rewrite (H' eqv); clear H' eqv] )
  end.

Ltac implement_Enumerate_filter find_search_term :=
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[For (l <- CallBagMethod ?idx {| bindex := "Enumerate"|} ?r_n0 ();
                        (List_Query_In (filter (@DecideableEnsembles.dec _ ?DeletedTuples _) (snd l))
                                       ?resultComp))]] =>
      let filter_dec := eval simpl in (@DecideableEnsembles.dec _ DeletedTuples _) in
          let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
              let search_term_type := eval simpl in (BagSearchTermType idx_search_update_term) in
                  let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                      makeEvar search_term_type
                               ltac:(fun search_term =>
                                       let eqv := fresh in
                                       assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                     [ find_search_term qs_schema idx filter_dec search_term
                                     | let H' := fresh in
                                       pose (@refine_Query_For_In_Find _ _ string _ _ H idx filter_dec
                                                                       search_term resultComp) as H';
                                         setoid_rewrite (H' eqv); clear H'])
  end.

Ltac implement_Pick_DelegateToBag_AbsR_observer :=
  match goal with
      [H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
       |- context[{r_n' : IndexedQueryStructure ?qs_schema ?indices | DelegateToBag_AbsR ?r_o r_n'}] ]
      => setoid_rewrite (refine_pick_val (@DelegateToBag_AbsR qs_schema indices r_o) H)
  end.

Add Parametric Morphism
    (A : Type)
    (f : A -> Type)
    (As : list A)
    (a : A)
    (l' : list (ilist f As))
: (@Join_Lists A f As a l')
    with signature
    (pointwise_relation _ refine) ==> refine
      as refine_Join_Lists.
Proof.
  unfold pointwise_relation; simpl; intros.
  induction l'; unfold Join_Lists; simpl.
  - reflexivity.
  - rewrite H; setoid_rewrite IHl'; reflexivity.
Qed.

Lemma refine_Join_Enumerate_Swap
      qs_schema BagIndexKeys
      (ResultT : Type) :
  forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
    DelegateToBag_AbsR r_o r_n ->
    forall (idx idx' : BoundedString)
           (resultComp : _ -> Comp (list ResultT)),
      refine (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
              l' <- (Join_Lists (Build_single_Tuple_list (snd l))
                                (fun _ => l <- (CallBagMethod idx' {|bindex := "Enumerate" |} r_n ());
                                 ret (snd l)));
              List_Query_In l' resultComp)
             (l <- CallBagMethod idx' {|bindex := "Enumerate" |} r_n ();
              l' <- (Join_Lists (Build_single_Tuple_list (snd l))
                                (fun _ => l <- (CallBagMethod idx {|bindex := "Enumerate" |} r_n ());
                                 ret (snd l)));
              List_Query_In l' (fun tup_pair => (resultComp (icons _ (ilist_hd (ilist_tl tup_pair)) (icons _ (ilist_hd tup_pair) (inil _)))))).
Proof.
Admitted.

(* implement_In' implements [UnConstrQuery_In] in a variety of contexts. *)
Ltac implement_In' :=
  match goal with
    (* Implement a List_Query_In of a list [l] applied to a UnConstrQuery_In [idx]
        by enumerating [idx] with a method call and joining the result with [l] *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- context[fun b' : ?ElementT => List_Query_In (@?l b') (fun b => UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx (@?f b' b) )] ] =>
      let H' := eval simpl in
      (fun (b' : ElementT) => refine_Join_Query_In_Enumerate' H idx (f b') (l b')) in
          setoid_rewrite H'

    (* Implement a 'naked' UnConstrQuery_In as a call to enumerate *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- context[UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx ?f] ] =>
      let H' := eval simpl in (refine_Query_In_Enumerate H (idx := idx) f) in
          setoid_rewrite H'

    (* Implement a UnConstrQuery_In under a single binder as a call to enumerate *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- context[fun b => UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx (@?f b) ] ] =>
      let H' := eval simpl in
      (fun b => @refine_Query_In_Enumerate qs_schema indexes _ r_o r_n H idx (f b)) in
          setoid_rewrite H'
  end.

Ltac implement_In :=
  (* First simplify any large terms [i.e. Rep, BagSpec, snd, and MethodDomCod
     that might slow down setoid rewriting *)
  simpl in *;
  (* The repeatedly implement [In]s *)
  repeat implement_In'.


Fixpoint Join_ListsT (Ts : list Type) : Type
  :=
    match Ts with
      | [] => unit
      | [A] => A
      | A :: Cs => prod A (Join_ListsT Cs)
    end.

Lemma ExtensionalEq_andb {A} :
  forall (f g f' g' : A -> bool),
    ExtensionalEq f f'
    -> ExtensionalEq g g'
    -> ExtensionalEq (fun a => f a && g a) (fun a => f' a && g' a).
Proof.
  unfold ExtensionalEq; intros; congruence.
Qed.

Lemma ExtensionalEq_andb_true {A} :
  forall (f f' : A -> bool),
    ExtensionalEq f f'
    -> ExtensionalEq f (fun a => f' a && (fun _ => true) a).
Proof.
  unfold ExtensionalEq; intros.
  rewrite andb_true_r; apply H.
Qed.

Ltac split_filters k :=
  match goal with
    | |- ExtensionalEq (fun a => (@?f a) && (@?g a)) ?b =>
      let fT := type of f in
      let gT := type of g in
      makeEvar
        fT
        ltac:(fun f' =>
                makeEvar gT ltac:(fun g' =>
                                    apply (@ExtensionalEq_andb _ f g f' g');
                                  [ first [split_filters | k ] | first [split_filters | k]] ))
    | |- ExtensionalEq (fun a => (@?f a)) ?b => k
  end.

(* Convert List_Query_In Where Clauses into a filter using search terms. *)

Ltac convert_Where_to_search_term :=
  (* First replace the Where clause with a test function. *)
  simpl;
  match goal with
      |- context[List_Query_In _ (fun b : ?QueryT => Where (@?P b) (@?resultComp b))]
      =>
      let P_dec := fresh in
      setoid_rewrite (fun l => @refine_List_Query_In_Where QueryT _ l P resultComp _)
  end; simpl;
  (* Find search term replacements for the function. *)
  match goal with
      |- context [List_Query_In (filter ?f _) _] =>
      let T := type of f in
      makeEvar T
               ltac:(fun g =>
                       let eqv := fresh in
                       assert (ExtensionalEq f g) as eqv;
                     [ apply ExtensionalEq_andb_true
                     | setoid_rewrite (filter_by_equiv f g eqv)])
  end.

Lemma if_duplicate_cond_eq {A}
: forall (i : bool) (t e : A),
    (if i then (if i then t else e) else e) = if i then t else e.
Proof.
  destruct i; reflexivity.
Qed.

Lemma Bind_refine_If_Then_Else {A B}
: forall i (t e : A -> Comp B) (ca : Comp A),
    refine (a <- ca;
            If i Then t a Else e a)
           (If i Then (a <- ca;
                       t a)
               Else (a <- ca;
                     e a)).
Proof.
  intros; destruct i; simpl; reflexivity.
Qed.

Ltac equate X Y := let H := fresh in assert (H : X = Y) by reflexivity; clear H.

Definition unit_Heading :=
  {| Attributes := unit;
     Domain := fun _ => unit |}.

Definition unit_Tuple : @Tuple unit_Heading := id.

Ltac get_ithDefault f n k :=
  match type of f with
    | ilist (@Tuple) ?A -> ?C =>
      let G := fresh "G" in
      let p := fresh "p" in
      let H := fresh "H" in
      let proj := fresh "proj" in
      let proj := eval simpl in
      (fun b : ilist (@Tuple) A => ith_default unit_Heading unit_Tuple b n) in
          evar (G : @Tuple (nth_default unit_Heading A n) -> C);
        assert (H : forall p,
                      f p = G (proj p)) by
          (subst G; intro p;
           let p' := eval simpl in (proj p) in
               pattern p';
           match goal with
             | [ |- (fun t => @?f t = @?g t) _ ] => equate g f; reflexivity
           end); clear H;
        let G' := eval unfold G in G in clear G; k G'
  end.

Ltac get_ithDefault_pair f m n k :=
  match type of f with
    | ilist (@Tuple) ?A -> ?C =>
      let G := fresh "G" in
      let p := fresh "p" in
      let H := fresh "H" in
      let proj1 := fresh "proj" in
      let proj2 := fresh "proj" in
      let proj1 := eval simpl in
      (fun b : ilist (@Tuple) A => ith_default unit_Heading unit_Tuple b m) in
          let proj2 := eval simpl in
          (fun b : ilist (@Tuple) A => ith_default unit_Heading unit_Tuple b n)
            in evar (G : @Tuple (nth_default unit_Heading A m)
                         -> @Tuple (nth_default unit_Heading A n)
                         -> C);
            assert (H : forall p,
                          f p = G (proj1 p) (proj2 p)) by
              ( subst G; intro p;
                let p1 := eval simpl in (proj1 p) in
                    let p2 := eval simpl in (proj2 p) in
                        pattern p1, p2;
                match goal with
                  | [ |- (fun t t' => @?f t t' = @?g t t') _ _ ] => equate f g; reflexivity
                end); clear H;
            let G' := eval unfold G in G in clear G; k G'
  end.

(* Build pairs of fields + their values. *)
Ltac findGoodTerm_dep SC F k :=
  match F with
    | fun (a : ?T) b => ?[@?f a b] =>
      match type of f with
        | forall a b, {@?X a = _!?fd} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
        | forall a b, {_!?fd = @?X a} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
        | forall a b, {@?X a = _``?fd} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
        | forall a b, {_``?fd = @?X a} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
      end
    | fun (a : ?T) b => (@?f a b) && (@?g a b) =>
      findGoodTerm_dep SC f ltac:(fun fds1 tail1 =>
                                    findGoodTerm_dep SC g ltac:(fun fds2 tail2 =>
                                                                  k (fds1, fds2) (fun tup : @Tuple SC => (tail1 tup) && (tail2 tup))))
    | _ => k tt F
  end.

(* Build search a search term from the list of attribute + value pairs in fs. *)
Ltac createTerm_dep dom fs f fds tail k :=
  match fs with
    | nil =>
      k (fun x : dom => tail)
    | ?s :: ?fs' =>
      createTerm_dep dom fs' f fds tail
                     ltac:(fun rest =>
                             findMatchingTerm fds s
                                              ltac:(fun X =>
                                                      k (fun x : dom => (Some (X x), rest x)))
                                                     || k (fun x : dom => (@None (f s), rest x)))
  end.

(* Get the heading of [SC] before building the search term. *)
Ltac makeTerm_dep dom fs SC fds tail k :=
  match eval hnf in SC with
    | Build_Heading ?f =>
      createTerm_dep dom fs f fds tail k
  end.

Definition Dep_SearchTerm_Wrapper {A} {heading}
           (search_term_dep : @Tuple heading -> A)
           (tup : @Tuple heading) : A := search_term_dep tup.

Ltac find_simple_search_term_dep qs_schema idx dom filter_dec search_term :=
  match type of search_term with
    | ?dom -> BuildIndexSearchTerm ?attr =>
      let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
      findGoodTerm_dep SC filter_dec
                       ltac:(fun fds tail =>
                               let tail := eval simpl in tail in
                                   makeTerm_dep dom attr SC fds tail
                                                ltac:(fun tm => pose tm;
                                                      (* unification fails if I don't pose tm first... *)
                                                      unify (Dep_SearchTerm_Wrapper tm) search_term;
                                                      unfold ExtensionalEq, MatchIndexSearchTerm;
                                                      simpl; intros;
                                                      try prove_extensional_eq))
  end.

(* Find the name of a schema [schemas] with the same heading as [heading] *)

Ltac find_equivalent_tuple schemas heading k :=
  match schemas with
    | nil => fail
    | ?sch' :: ?schemas' =>
      (let H := fresh in
       assert (schemaHeading (relSchema sch') = heading) as H
           by reflexivity;
       clear H;  k (relName sch'))
        || find_equivalent_tuple schemas' heading k
  end.

Ltac find_equivalent_search_term_pair m n build_search_term_dep :=
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- ExtensionalEq ?f _ ] =>
      get_ithDefault_pair f m n
                          ltac:(fun filter_dec =>
                                  let dom := match type of filter_dec with
                                               | ?A -> ?B -> bool => constr:(A)
                                             end in
                                  let heading := match type of filter_dec with
                                                   | ?A -> @Tuple ?heading -> bool => constr:(heading)
                                                 end in
                                  let schemas := eval simpl in (qschemaSchemas qs_schema) in
                                      find_equivalent_tuple schemas heading
                                                            ltac:(fun id => let idx' := constr:({| bindex := id |} : BoundedIndex (map relName (qschemaSchemas qs_schema)))
                                                                            in let idx := eval simpl in idx' in
                                                                                   let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
                                                                                       let search_term_type := eval simpl in (BagSearchTermType idx_search_update_term) in
                                                                                           let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                                                                                               makeEvar (dom -> search_term_type)
                                                                                                        ltac: (fun search_term =>
                                                                                                                 let eqv := fresh in
                                                                                                                 assert (forall a b, filter_dec a b
                                                                                                                                     = search_term_matcher (search_term a) b) as eqv;
                                                                                                               [ build_search_term_dep qs_schema idx
                                                                                                                                       dom filter_dec search_term
                                                                                                               | match goal with
                                                                                                                     |- ExtensionalEq ?f ?search_term' =>
                                                                                                                     match type of f with
                                                                                                                       | ?A -> _ =>
                                                                                                                         unify search_term' (fun a : A => search_term_matcher (search_term (ith_default unit_Heading unit_Tuple a m))
                                                                                                                                                                              ((ith_default unit_Heading unit_Tuple a n)))
                                                                                                                     end
                                                                                                                 end;
                                                                                                                 unfold ExtensionalEq in *; intros;
                                                                                                                 simpl in *; rewrite eqv; reflexivity
                                                                                                               ]))) end.

Ltac find_equivalent_search_term m build_search_term :=
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- ExtensionalEq ?f _ ] =>
      get_ithDefault f m
                     ltac:(fun filter_dec =>
                             let heading := match type of filter_dec with
                                              | @Tuple ?heading -> bool => constr:(heading)
                                            end in
                             let schemas := eval simpl in (qschemaSchemas qs_schema) in
                                 find_equivalent_tuple schemas heading
                                                       ltac:(fun id => let idx' := constr:({| bindex := id |} : BoundedIndex (map relName (qschemaSchemas qs_schema)))
                                                                       in let idx := eval simpl in idx' in
                                                                              let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
                                                                                  let search_term_type := eval simpl in (BagSearchTermType idx_search_update_term) in
                                                                                      let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                                                                                          makeEvar (search_term_type)
                                                                                                   ltac: (fun search_term =>
                                                                                                            let eqv := fresh in
                                                                                                            assert (forall a, filter_dec a
                                                                                                                              = search_term_matcher search_term a) as eqv;
                                                                                                          [ build_search_term qs_schema idx
                                                                                                                              filter_dec search_term
                                                                                                          | match goal with
                                                                                                                |- ExtensionalEq ?f ?search_term' =>
                                                                                                                match type of f with
                                                                                                                  | ?A -> _ =>
                                                                                                                    unify search_term' (fun a : A => search_term_matcher search_term (ith_default unit_Heading unit_Tuple a m))
                                                                                                                end
                                                                                                            end;
                                                                                                            unfold ExtensionalEq in *; intros;
                                                                                                            simpl in *; rewrite eqv; reflexivity
                                                                                                          ]))) end.


Corollary refine_Join_Lists_filter_filter_search_term_snd_dep'
          qs_schema BagIndexKeys
          (ResultT : Type) :
  forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
         idx idx'
         (search_pattern : _ -> _)
         (resultComp : ilist (@Tuple) [_; _] -> Comp (list ResultT))
         filter_rest st,
    refine (cl <- CallBagMethod idx {| bindex := "Find" |} r_n st;
            l' <- (Join_Lists (Build_single_Tuple_list (snd cl))
                              (fun _ => l <- CallBagMethod idx' {| bindex := "Enumerate" |} r_n ();
                               ret (snd l)));
            List_Query_In (filter (fun a : ilist (@Tuple) [_ ; _] => BagMatchSearchTerm _ (search_pattern (ilist_tl a)) (ilist_hd a) && filter_rest a) l')
                          resultComp)
           (cl <- CallBagMethod idx {| bindex := "Find" |} r_n st;
            l' <- (Join_Lists (Build_single_Tuple_list (snd cl))
                              (fun tup => l <- CallBagMethod idx' {| bindex := "Find" |} r_n (search_pattern tup);
                               ret (snd l)));
            List_Query_In (filter filter_rest l') resultComp).
Proof.
  intros; f_equiv; intro;
  apply refine_Join_Lists_filter_search_term_snd_dep.
Qed.

Ltac convert_filter_to_find' :=
  try match goal with
          |- context[filter (fun a => (_ && _) && true) _] =>
          setoid_rewrite <- andb_assoc; simpl
      end;
  match goal with
    | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- context[l <- CallBagMethod ?idx ``("Enumerate") ?r_n ();
                  List_Query_In (filter (fun a => ?MatchIndexSearchTerm ?st (ilist_hd a) && @?filter_rest a)
                                        (Build_single_Tuple_list (snd l))) ?resultComp] =>
      let b := fresh in
      pose proof (@refine_Query_For_In_Find_single _ _ _ r_o r_n H idx st resultComp filter_rest) as b;
        simpl in b; setoid_rewrite b; clear b

    | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- context[l <- CallBagMethod ?idx ``("Enumerate") ?r_n ();
                  l' <- Join_Lists (Build_single_Tuple_list (snd l)) ?cl;
                  List_Query_In (filter (fun a => ?MatchIndexSearchTerm ?st (ilist_hd (ilist_tl a)) && @?filter_rest a)
                                        l') ?resultComp] =>
      let b := fresh in
      pose proof (fun foo => @refine_Join_Lists_filter_search_term_fst _ _ _ r_n idx _ cl st resultComp foo filter_rest) as b;
        simpl in b; setoid_rewrite b;
        [ clear b
        | match goal with
            | |- context [CallBagMethod ?idx' ``("Enumerate") _ _] =>
              intros; eapply (realizeable_Enumerate (r_o := r_o) (r_n := r_n) idx' H)
            | |- context [CallBagMethod ?idx' ``("Find") _ _] =>
              intros; eapply (realizeable_Find (r_o := r_o) (r_n := r_n) idx' H)
          end]
    | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- context[l <- CallBagMethod ?idx ``("Find") ?r_n ?st;
                  l' <- Join_Lists (Build_single_Tuple_list (snd l))
                     (fun _ : ilist (@Tuple) [?heading] =>
                        l <- CallBagMethod ?idx' ``("Enumerate") ?r_n ();
                      ret (snd l));
                  List_Query_In (filter (fun a => ?MatchIndexSearchTerm (Dep_SearchTerm_Wrapper ?st' (ilist_hd (ilist_tl a)))
                                                                       (ilist_hd a) && @?filter_rest a) l') ?resultComp] =>
      let b := fresh in
      pose proof (@refine_Join_Lists_filter_filter_search_term_snd_dep' _ _ _ r_n idx idx'
                                                                        (fun a => Dep_SearchTerm_Wrapper st' (ilist_hd a))
                                                                        resultComp filter_rest st) as b;
        unfold Dep_SearchTerm_Wrapper in b; simpl in b; setoid_rewrite b; clear b
    (* The final case replaces the last filter and the Return statement. *)
    | _ => setoid_rewrite filter_true; setoid_rewrite refine_List_Query_In_Return
  end.

Ltac convert_filter_to_find :=
  simpl; repeat convert_filter_to_find'.

(* This also implements Fors *)
Ltac Implement_Aggregates :=
  repeat
    match goal with
      | |- context[For _] => setoid_rewrite refine_For_List
      | |- context[Count _] => setoid_rewrite refine_Count
    end.

(* Commits the database at the end of a method call. *)
Ltac commit :=
  match goal with
    | [H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
       |- context[{r_n' : IndexedQueryStructure ?qs_schema ?indices | DelegateToBag_AbsR ?r_o r_n'}] ]
      => setoid_rewrite (refine_pick_val (@DelegateToBag_AbsR qs_schema indices r_o) H);
        simplify with monad laws
  end.

Ltac ilist_of_dep_evar C D B As k :=
  match As with
    | nil => k (fun (c : C) (d : D c) => inil (B c d))
    | cons ?a ?As' =>
      makeEvar (forall c (d : D c), B c d a)
               ltac:(fun b =>
                       ilist_of_dep_evar
                         C D B As'
                         ltac:(fun Bs' => k (fun c (d : D c) => @icons _ _ a As' (b c d) (Bs' c d))))
  end.

Definition Initialize_IndexedQueryStructureImpls'
           {indices}
           Index
           (DelegateReps : @BoundedString (map relName indices) -> Type)
           (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
: @Build_IndexedQueryStructure_Impl_cRep _ Index DelegateReps :=
  (fun idx => ComputationalADT.pcConstructors (DelegateImpls idx)
                                              {| bindex := "Empty" |} ()).

Ltac higher_order_1_reflexivity'' :=
  let x := match goal with |- ?R (ret ?x) (ret (?f ?a)) => constr:(x) end in
  let f := match goal with |- ?R (ret ?x) (ret (?f ?a)) => constr:(f) end in
  let a := match goal with |- ?R (ret ?x) (ret (?f ?a)) => constr:(a) end in
  let x' := (eval pattern a in x) in
  let f' := match x' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_2_reflexivity'' :=
  let x := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(x) end in
  let f := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(f) end in
  let a := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(a) end in
  let b := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Definition CallBagImplMethod
           {qs_schema : QueryStructureSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
           (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
           (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           idx midx
           (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps) :=
  ComputationalADT.pcMethods (DelegateImpls idx) midx (r_n idx).

Definition CallBagImplConstructor
           {qs_schema : QueryStructureSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
           (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
           (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           idx cidx :=
  ComputationalADT.pcConstructors (DelegateImpls idx) cidx.

Lemma refine_BagImplConstructor
      {qs_schema : QueryStructureSchema}
      (indices := qschemaSchemas qs_schema)
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
      (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
      (DelegateImpls : forall idx,
                         ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
      (ValidImpls
       : forall idx,
           refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx))))
:  forall (ridx : BoundedIndex (map relName (qschemaSchemas qs_schema))) cidx d,
   exists r_o' ,
     refine (@CallBagConstructor _ (bindex ridx) (ith_Bounded relName Index ridx) cidx d)
            (ret r_o') /\
     AbsR (ValidImpls ridx) r_o' (CallBagImplConstructor DelegateReps DelegateImpls cidx d).
Proof.
  intros.
  pose proof (ADTRefinementPreservesConstructors (ValidImpls ridx) cidx d (ReturnComputes _)).
  inversion_by computes_to_inv; subst.
  exists x;
    unfold CallBagImplConstructor; simpl in *.
  split; simpl.
  - intros v Comp_v; inversion_by computes_to_inv; subst.
    generalize d v H0; clear.
    eapply (fun P H => Iterate_Dep_Type_BoundedIndex_equiv_1 P H cidx).
    simpl; intuition.
  - eapply H1.
Qed.

Definition Join_Lists'
           {A : Type} {f : A -> Type} {As : list A} {a : A}
           (l : list (ilist f As)) (c : ilist f As -> list (f a))
  := flatten (map
                (fun l' => map (fun fa : f a => icons _ fa l') (c l')) l).

Lemma Join_Lists_Impl {A : Type} {f : A -> Type} {As : list A} {a : A}
: forall (l : list (ilist f As))
         (c : ilist f As -> Comp (list (f a)))
         (c' : ilist f As -> list (f a)),
    (forall a', refine (c a') (ret (c' a')))
    -> refine (Join_Lists l c) (ret (Join_Lists' l c')).
Proof.
  induction l; unfold Join_Lists, Join_Lists'; simpl; intros.
  - reflexivity.
  - rewrite H; simplify with monad laws.
    setoid_rewrite IHl; eauto; simplify with monad laws.
    reflexivity.
Qed.

Lemma refine_BagImplMethods
      {qs_schema : QueryStructureSchema}
      (indices := qschemaSchemas qs_schema)
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
      (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
      (DelegateImpls : forall idx,
                         ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
      (ValidImpls
       : forall idx,
           refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx))))
:  forall (r_o : IndexedQueryStructure qs_schema Index)
          (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps)
          ridx,
     Build_IndexedQueryStructure_Impl_AbsR DelegateImpls ValidImpls r_o r_n ->
     forall midx
            d,
     exists r_o',
       refine (CallBagMethod ridx midx r_o d)
              (ret (r_o',
                    (snd (CallBagImplMethod DelegateImpls midx r_n d))))
       /\ AbsR (ValidImpls ridx) r_o' (fst (CallBagImplMethod DelegateImpls midx r_n d)).
Proof.
  intros.
  pose proof (ADTRefinementPreservesMethods (ValidImpls ridx) midx
                                            (GetIndexedRelation r_o ridx)
                                            (r_n ridx) d (H ridx) (ReturnComputes _)).
  inversion_by computes_to_inv; subst.
  exists (fst x);
    unfold CallBagImplMethod; simpl in *.
  split; simpl.
  - pose proof (f_equal snd H3) as eq_x; simpl in eq_x.
    assert (refine (CallBagMethod ridx midx r_o d)
                   (ret (fst x, snd x)));
      [ | rewrite eq_x in H3;
          unfold ComputationalADT.cMethods in eq_x; simpl in *; rewrite <- eq_x; eapply H0].
    intros v Comp_v; simpl in *; inversion_by computes_to_inv; subst.
    destruct x; simpl @fst in *; simpl @snd in *.
    generalize d i m H1 H2; clear.
    eapply (fun P H => Iterate_Dep_Type_BoundedIndex_equiv_1 P H midx).
    simpl; intuition.
  - unfold ComputationalADT.cMethods in H3; simpl in *; rewrite <- H3; eapply H2.
Qed.

Global Opaque CallBagMethod.
Global Opaque CallBagConstructor.

Arguments icons {A} {B} {a} {As} _ _.
Arguments CallBagConstructor {heading} name {index} cidx _.

Ltac implement_bag_constructors :=
  repeat match goal with
           | |- context[ Pick (fun r_n : @Build_IndexedQueryStructure_Impl_cRep ?qs_schema ?Index ?DelegateReps =>
                                 @Build_IndexedQueryStructure_Impl_AbsR
                                   _ _ ?DelegateReps ?DelegateImpls
                                   ?ValidImpls ?r_o r_n)] =>
             refine pick val (@Initialize_IndexedQueryStructureImpls' qs_schema Index DelegateReps DelegateImpls);
               [ higher_order_2_reflexivity'' |
                 unfold Build_IndexedQueryStructure_Impl_AbsR;
                   eapply Iterate_Dep_Type_BoundedIndex_equiv_1; simpl; intuition ]
           | |- context[CallBagConstructor ?ridx ?cidx ?d] =>
             match goal with
                 |- appcontext[@Build_IndexedQueryStructure_Impl_AbsR
                                 ?qs_schema ?Index
                                 ?DelegateReps ?DelegateImpls ?ValidImpls] =>
                 let r_o' := fresh "r_o'" in
                 let AbsR_r_o' := fresh "AbsR_r_o'" in
                 let refines_r_o' := fresh "refines_r_o'" in
                 destruct (@refine_BagImplConstructor
                             qs_schema Index DelegateReps DelegateImpls ValidImpls
                             {|bindex := ridx |} cidx d) as [r_o' [refines_r_o' AbsR_r_o']];
                   setoid_rewrite refines_r_o'; simpl in *; simplify with monad laws; simpl
             end
         end.

Ltac implement_bag_methods :=
  repeat
    match goal with
      | |- refine (ret _) (ret (?f ?a ?b)) => higher_order_2_reflexivity''
      | |- refine (ret _) (ret (?f ?a)) => higher_order_1_reflexivity''
      | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls ?r_o ?r_n
        |- context[
               { r_n' | @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                               ?ValidImpls ?r_o r_n'}
             ] => refine pick val _;
          [ simplify with monad laws |
            eapply H]

      | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls ?r_o ?r_n
        |- context[CallBagMethod (BagIndexKeys := ?Index') ?ridx ?midx ?r_o ?d] =>
        let r_o' := fresh "r_o'" in
        let AbsR_r_o' := fresh "AbsR_r_o'" in
        let refines_r_o' := fresh "refines_r_o'" in
        destruct (@refine_BagImplMethods qs_schema Index' DelegateReps DelegateImpls ValidImpls r_o r_n ridx H midx d) as [r_o' [refines_r_o' AbsR_r_o']];
          simpl in refines_r_o', AbsR_r_o';
          setoid_rewrite refines_r_o'; simpl in *; simplify with monad laws; simpl

      | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls ?r_o ?r_n
        |- context[Join_Lists (As := ?As) (f := ?f) (a := ?a) ?l ?c ] =>
        makeEvar (ilist f As -> list (f a))
                 ltac:(fun c' =>
                         let refines_c' := fresh in
                         assert (forall a', refine (c a') (ret (c' a'))) as refines_c';
                       [intros; try implement_bag_methods
                       | setoid_rewrite (Join_Lists_Impl l c c' refines_c');
                         simpl in *; setoid_rewrite (refineEquiv_bind_unit);
                         implement_bag_methods
                       ])

    end.

Ltac FullySharpenQueryStructure qs_schema Index :=
  let delegateSigs := constr:(Build_IndexedQueryStructure_Impl_Sigs Index) in
  let delegateSpecs := constr:(Build_IndexedQueryStructure_Impl_Specs Index) in
  let cRep' := constr:(Build_IndexedQueryStructure_Impl_cRep Index) in
  let cAbsR' := constr:(@Build_IndexedQueryStructure_Impl_AbsR qs_schema Index) in
  let DelegateIDs := constr:(map relName (qschemaSchemas qs_schema)) in
  match goal with
      |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
      ilist_of_dep_evar
        (@BoundedString DelegateIDs -> Type)
        (fun D =>
           forall idx,
             ComputationalADT.pcADT (delegateSigs idx) (D idx))
        (fun (DelegateReps : @BoundedString DelegateIDs -> Type)
             (DelegateImpls : forall idx,
                                ComputationalADT.pcADT (delegateSigs idx) (DelegateReps idx))
             (Sig : methSig) => ComputationalADT.cMethodType (cRep' DelegateReps)
                                                             (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths =>
                ilist_of_dep_evar
                  (@BoundedString DelegateIDs -> Type)
                  (fun D =>
                     forall idx,
                       ComputationalADT.pcADT (delegateSigs idx) (D idx))
                  (fun (DelegateReps : @BoundedString DelegateIDs -> Type)
                       (DelegateImpls : forall idx,
                                          ComputationalADT.pcADT (delegateSigs idx) (DelegateReps idx))
                       (Sig : consSig) =>
                     ComputationalADT.cConstructorType (cRep' DelegateReps) (consDom Sig))
                  consSigs
                  ltac:(fun cCons =>
                          eapply
                            (@Notation_Friendly_SharpenFully'
                               _
                               consSigs
                               methSigs
                               consDefs
                               methDefs
                               DelegateIDs
                               delegateSigs
                               cRep'
                               cCons
                               cMeths
                               delegateSpecs
                               cAbsR'
                            )));
        unfold Dep_Type_BoundedIndex_app_comm_cons
  end; simpl; intros;
  [repeat split; intros; try exact tt; implement_bag_constructors
  | repeat split; intros; try exact tt; implement_bag_methods].

Ltac FullySharpenQueryStructure' qs_schema Index :=
  let delegateSigs := constr:(Build_IndexedQueryStructure_Impl_Sigs Index) in
  let delegateSpecs := constr:(Build_IndexedQueryStructure_Impl_Specs Index) in
  let cRep' := constr:(Build_IndexedQueryStructure_Impl_cRep Index) in
  let cAbsR' := constr:(@Build_IndexedQueryStructure_Impl_AbsR qs_schema Index) in
  let DelegateIDs := constr:(map relName (qschemaSchemas qs_schema)) in
  match goal with
      |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
      ilist_of_dep_evar
        (@BoundedString DelegateIDs -> Type)
        (fun D =>
           forall idx,
             ComputationalADT.pcADT (delegateSigs idx) (D idx))
        (fun (DelegateReps : @BoundedString DelegateIDs -> Type)
             (DelegateImpls : forall idx,
                                ComputationalADT.pcADT (delegateSigs idx) (DelegateReps idx))
             (Sig : methSig) => ComputationalADT.cMethodType (cRep' DelegateReps)
                                                             (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths =>
                ilist_of_dep_evar
                  (@BoundedString DelegateIDs -> Type)
                  (fun D =>
                     forall idx,
                       ComputationalADT.pcADT (delegateSigs idx) (D idx))
                  (fun (DelegateReps : @BoundedString DelegateIDs -> Type)
                       (DelegateImpls : forall idx,
                                          ComputationalADT.pcADT (delegateSigs idx) (DelegateReps idx))
                       (Sig : consSig) =>
                     ComputationalADT.cConstructorType (cRep' DelegateReps) (consDom Sig))
                  consSigs
                  ltac:(fun cCons =>
                          eapply
                            (@Notation_Friendly_SharpenFully'
                               _
                               consSigs
                               methSigs
                               consDefs
                               methDefs
                               DelegateIDs
                               delegateSigs
                               cRep'
                               cCons
                               cMeths
                               delegateSpecs
                               cAbsR'
                            )));
        unfold Dep_Type_BoundedIndex_app_comm_cons
  end; simpl; intros;
  [repeat split; intros; try exact tt; implement_bag_constructors
  | repeat split; intros; try exact tt ].

  Ltac higher_order_4_reflexivity'' :=
  let x := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c ?d)) => constr:(x) end in
  let f := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c ?d)) => constr:(f) end in
  let a := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c ?d)) => constr:(a) end in
  let b := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c ?d)) => constr:(b) end in
  let c := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c ?d)) => constr:(c) end in
  let d := match goal with |- ?R (ret ?x) (ret (?f ?a ?b ?c ?d)) => constr:(d) end in
  let x' := (eval pattern a, b, c, d in x) in
  let f' := match x' with ?f' _ _ _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

  Ltac Implement_Insert_Checks :=
    repeat first
           [setoid_rewrite FunctionalDependency_symmetry;
             simplify with monad laws;
             setoid_rewrite if_duplicate_cond_eq
           | fundepToQuery; try simplify with monad laws
           | foreignToQuery; try simplify with monad laws
           | setoid_rewrite refine_trivial_if_then_else; simplify with monad laws
           ].

  Ltac Implement_Bound_Join_Lists :=
    match goal with
      | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls ?r_o ?r_n
        |- refine (Bind (Join_Lists (As := ?As) (f := ?f) (a := ?a) ?l ?c) _) _ =>
        makeEvar (ilist f As -> list (f a))
                 ltac:(fun c' =>
                         let refines_c' := fresh in
                         assert (forall a', refine (c a') (ret (c' a'))) as refines_c';
                       [intros
                       | etransitivity;
                         [apply refine_bind;
                           [ apply (Join_Lists_Impl l c c' refines_c')
                           | unfold pointwise_relation; intros; higher_order_1_reflexivity
                           ]
                         | etransitivity;
                           [ apply (proj1 (refineEquiv_bind_unit _ _)) | simpl]
                         ]]; cbv beta; simpl in * )
    end.

  Ltac Implement_Bound_Bag_Call :=
    match goal with
    | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                 ?ValidImpls ?r_o ?r_n
      |- refine (Bind (CallBagMethod (BagIndexKeys := ?Index') ?ridx ?midx ?r_o ?d) _) _ =>
      let r_o' := fresh "r_o'" in
      let AbsR_r_o' := fresh "AbsR_r_o'" in
      let refines_r_o' := fresh "refines_r_o'" in
      destruct (@refine_BagImplMethods qs_schema Index' DelegateReps DelegateImpls ValidImpls r_o r_n ridx H midx d) as [r_o' [refines_r_o' AbsR_r_o']];
        simpl in refines_r_o', AbsR_r_o';
        etransitivity;
        [ apply refine_bind;
          [apply refines_r_o'
          | unfold pointwise_relation; intros; higher_order_1_reflexivity
          ]
        | etransitivity;
          [ apply (proj1 (refineEquiv_bind_unit _ _)) | simpl]
        ]; cbv beta; simpl in *
    end.

  Ltac Implement_If_Then_Else :=
    match goal with
      | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls ?r_o ?r_n
        |- refine (If_Then_Else ?i (ret ?t) (ret ?e)) _ =>
        etransitivity;
          [ apply (refine_If_Then_Else_ret i t e)
          | ]
      | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls ?r_o ?r_n
        |- refine (Bind (If ?i Then ?t Else ?e) ?k) _ =>
        etransitivity;
          [ apply (refine_If_Then_Else_Bind i t e k)
          | etransitivity;
            [ apply refine_If_Then_Else;
              [ reflexivity | | ]
            | ]
          ]
    end.

  Ltac Implement_AbsR_Relation :=
    match goal with
      (* The case when a table has been updated *)
      | [H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                    ?ValidImpls ?r_o ?r_n,
             H2 : AbsR (?ValidImpls ?TableID) ?r_o' ?r_n'
         |- refine (Bind {r_n' | @Build_IndexedQueryStructure_Impl_AbsR
                                   ?qs_schema
                                   ?Index ?DelegateReps ?DelegateImpls
                                   ?ValidImpls (UpdateIndexedRelation ?r_o ?TableID ?r_o') r_n'} _) _]
        => etransitivity;
          [ apply refine_bind;
            [apply refine_pick_val;
              apply (@Update_Build_IndexedQueryStructure_Impl_AbsR
                      qs_schema Index DelegateReps DelegateImpls
                   ValidImpls r_o r_n TableID r_o' r_n' H H2)
            | unfold pointwise_relation; intros; higher_order_1_reflexivity
            ]
          | etransitivity;
            [ apply (proj1 (refineEquiv_bind_unit _ _)) | simpl]
          ]; cbv beta; simpl in *
      | [H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                    ?ValidImpls ?r_o ?r_n
         |- refine (Bind {r_n' | @Build_IndexedQueryStructure_Impl_AbsR
                                   ?qs_schema
                                   ?Index ?DelegateReps ?DelegateImpls
                                   ?ValidImpls ?r_o r_n'} _) _]
        => etransitivity;
          [ apply refine_bind;
            [apply refine_pick_val;
              apply H
            | unfold pointwise_relation; intros; higher_order_1_reflexivity
            ]
          | etransitivity;
            [ apply (proj1 (refineEquiv_bind_unit _ _)) | simpl]
          ]; cbv beta; simpl in *
    end.


Ltac implement_Delete_branches :=
    repeat setoid_rewrite refine_If_Then_Else_Bind;
    match goal with
        |- context[If _ Then ?t Else ?e] =>
        let B := type of t in
        makeEvar
          B
          ltac:(fun t' =>
                  makeEvar B
                           ltac:(fun e' =>
                                   setoidreplace (refine e e') idtac;
                                 [ setoidreplace (refine t t') idtac
                                 | ] ) )
    end;
    [
    | (* Refine the then branch *)
    implement_QSDeletedTuples find_simple_search_term;
      simplify with monad laws;
      cbv beta; simpl;
      implement_EnsembleDelete_AbsR find_simple_search_term;
      simplify with monad laws;
      reflexivity
    | (* Refine the else branch *)
    simplify with monad laws;
      simpl; commit; reflexivity
    ].

Ltac implement_Insert_branches :=
  repeat setoid_rewrite refine_If_Then_Else_Bind;
      repeat setoid_rewrite Bind_refine_If_Then_Else;
      repeat setoid_rewrite refineEquiv_bind_unit; simpl;
      match goal with
          |- context[If _ Then ?t Else ?e] =>
          let B := type of t in
          makeEvar
            B
            ltac:(fun t' =>
                    makeEvar B
                             ltac:(fun e' =>
                                     setoidreplace (refine e e') idtac;
                                   [ setoidreplace (refine t t') idtac
                                   | ] ) )
      end;
        [
        | (* Refine the then branch *)
        repeat match goal with
                 | [ H : DelegateToBag_AbsR ?r_o ?r_n
                     |- context[idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation ?r_o ?TableID) idx};
                                 {r_n' |
                                  DelegateToBag_AbsR
                                    (UpdateUnConstrRelation ?r_o ?TableID
                                                            (EnsembleInsert
                                                               {| elementIndex := idx; indexedElement := ?tup |}
                                                        (GetUnConstrRelation ?r_o ?TableID))) r_n'}]]
                   => setoid_rewrite (@refine_BagADT_QSInsert _ _ r_o r_n H TableID tup);
                     simplify with monad laws; reflexivity
                 | |- _ => setoid_rewrite <- refineEquiv_bind_bind
               end
        | (* Refine the else branch *)
        repeat match goal with
                 | [ H : DelegateToBag_AbsR ?r_o ?r_n
                     |- context[{idx | UnConstrFreshIdx (GetUnConstrRelation ?r_o ?TableID) idx};;
                                {r_n' | DelegateToBag_AbsR ?r_o r_n'}]]
                   => let H' := fresh in
                      pose proof H as H';
                        destruct H' as [_ H'];
                        let l := fresh in
                        let bnd := fresh in
                        let fresh_bnd := fresh in
                        destruct (H' TableID) as [l [[bnd fresh_bnd] _]];
                          refine pick val bnd; eauto;
                          setoid_rewrite refineEquiv_bind_unit;
                          refine pick val r_n; eauto;
                          setoid_rewrite refineEquiv_bind_unit;
                          reflexivity
                 | |- _ => setoid_rewrite <- refineEquiv_bind_bind
               end
        ].

  Ltac Focused_refine_Query' :=
          match goal with
            | |- context[ Count (@Query_For ?ResultT ?body) ] =>
              makeEvar (Comp (list ResultT))
                       ltac:(fun body' =>
                               let refine_body' := fresh in
                               assert (refine (@Query_For ResultT body) body') as refine_body';
                             [
                             | setoid_rewrite refine_Count; setoid_rewrite refine_body']
                            )
            | |- context[ @Query_For ?ResultT ?body ] =>
              makeEvar (Comp (list ResultT))
                       ltac:(fun body' =>
                               let refine_body' := fresh in
                               assert (refine (@Query_For ResultT body) body') as refine_body';
                             [
                             | setoid_rewrite refine_body']
                            )
          end.
