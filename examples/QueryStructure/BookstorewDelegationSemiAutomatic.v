Require Import Coq.Strings.String AutoDB BagADT.

(* Our bookstore has two relations (tables):
   - The [Books] relation contains the books in the
     inventory, represented as a tuple with
     [Author], [Title], and [ISBN] attributes.
     The [ISBN] attribute is a key for the relation,
     specified by the [where attributes .. depend on ..]
     constraint.
   - The [Orders] relation contains the orders that
     have been placed, represented as a tuple with the
     [ISBN] and [Date] attributes.

   The schema for the entire query structure specifies that
   the [ISBN] attribute of [Orders] is a foreign key into
   [Books], specified by the [attribute .. of .. references ..]
   constraint.
 *)

(* Let's define some synonyms for strings we'll need,
 * to save on type-checking time. *)
Definition sBOOKS := "Books".
Definition sAUTHOR := "Authors".
Definition sTITLE := "Title".
Definition sISBN := "ISBN".
Definition sORDERS := "Orders".
Definition sDATE := "Date".

(* Now here's the actual schema, in the usual sense. *)

Definition BookStoreSchema :=
  Query Structure Schema
    [ relation sBOOKS has
              schema <sAUTHOR :: string,
                      sTITLE :: string,
                      sISBN :: nat>
                      where attributes [sTITLE; sAUTHOR] depend on [sISBN];
      relation sORDERS has
              schema <sISBN :: nat,
                      sDATE :: nat> ]
    enforcing [attribute sISBN for sORDERS references sBOOKS].

(* Aliases for the tuples contained in Books and Orders, respectively. *)
Definition Book := TupleDef BookStoreSchema sBOOKS.
Definition Order := TupleDef BookStoreSchema sORDERS.

(* Our bookstore has two mutators:
   - [PlaceOrder] : Place an order into the 'Orders' table
   - [AddBook] : Add a book to the inventory

   Our bookstore has two observers:
   - [GetTitles] : The titles of books written by a given author
   - [NumOrders] : The number of orders for a given author
 *)

(* So, first let's give the type signatures of the methods. *)
Definition BookStoreSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      (* Method "PlaceOrder" : rep x Order -> rep x bool, *)
      Method "DeleteOrder" : rep x nat -> rep x list Order,
      (* Method "AddBook" : rep x Book -> rep x bool, *)
      (* Method "DeleteBook" : rep x nat -> rep x list Book, *)
      Method "GetTitles" : rep x string -> rep x list string,
      Method "NumOrders" : rep x string -> rep x nat
    }.

(* Now we write what the methods should actually do. *)

Definition BookStoreSpec : ADT BookStoreSig :=
  QueryADTRep BookStoreSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    (*update "PlaceOrder" ( o : Order ) : bool :=
        Insert o into sORDERS, *)

    update "DeleteOrder" ( oid : nat ) : list Order :=
        Delete o from sORDERS where o!sISBN = oid ,

    (*update "AddBook" ( b : Book ) : bool :=
        Insert b into sBOOKS , *)

    (* update "DeleteBook" ( id : nat ) : list Book :=
        Delete book from sBOOKS where book!sISBN = id , *)

    query "GetTitles" ( author : string ) : list string :=
      For (b in sBOOKS)
      Where (author = b!sAUTHOR)
      Return (b!sTITLE) ,

      query "NumOrders" ( author : string ) : nat :=
        Count (For (o in sORDERS) (b in sBOOKS)
               Where (author = b!sAUTHOR)
               Where (b!sISBN = o!sISBN)
               Return ())
}.

(* Aliases for internal names of the two tables *)
Definition Books := GetRelationKey BookStoreSchema sBOOKS.
Definition Orders := GetRelationKey BookStoreSchema sORDERS.

(* Aliases for internal notions of schemas for the two tables *)
Definition BookSchema := QSGetNRelSchemaHeading BookStoreSchema Books.
Definition OrderSchema := QSGetNRelSchemaHeading BookStoreSchema Orders.

(* Now we define an index structure (delegate) for each table. *)

Require Import
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        ADTSynthesis.QueryStructure.Implementation.Operations.BagADT.Refinements
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

(* Definition OrderSearchTerm := BuildIndexSearchTerm [ OrderSchema/sISBN  ].

Definition MatchOrderSearchTerm : OrderSearchTerm -> @Tuple OrderSchema -> bool.
  apply MatchIndexSearchTerm; repeat (econstructor; eauto with typeclass_instances).
Defined.

Definition BookSearchTerm := BuildIndexSearchTerm [ BookSchema/sAUTHOR; BookSchema/sISBN ].

Definition MatchBookSearchTerm : BookSearchTerm -> @Tuple BookSchema -> bool.
  apply MatchIndexSearchTerm; repeat (econstructor; eauto with typeclass_instances).
Defined.

Definition BookStorageDelegate := BagSpec MatchBookSearchTerm id.
Definition OrderStorageDelegate := BagSpec MatchOrderSearchTerm id.*)

(* In other words, index first on the author field, then the ISBN field.
 * Works especially efficiently for accesses keyed on author. *)


(*Definition BookStore_AbsR := (@DelegateToBag_AbsR _ BookStoreIndices).*)

(* Lemma BookstorewDelegates_AbsR_Pick :
  forall (qs_schema : QueryStructureSchema)
         indices
         (r_o : UnConstrQueryStructure qs_schema)
         (r_n : IndexedQueryStructure qs_schema indices),
    refineEquiv {r_n' | DelegateToBag_AbsR (r_o) r_n} (ret r_o).
Proof.
  intros r_o; split; intros v Comp_v;
  inversion_by computes_to_inv; subst; unfold BookstorewDelegates_AbsR in *.
  constructor; eauto.
  erewrite ilist_eq;
    [constructor | eauto].
Qed. *)

Opaque CallBagMethod.

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


Ltac findMatchingTerm fds s k :=
  match fds with
    | (?fd, ?X) =>
      let H := fresh in assert (H : bindex s = fd) by reflexivity; clear H;
        k X
    | (?fds1, ?fds2) => findMatchingTerm fds1 s k || findMatchingTerm fds2 s k
  end.

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

(* Get the heading of SC, then *)
Ltac makeTerm fs SC fds tail k :=
  match eval hnf in SC with
  | Build_Heading ?f =>
    createTerm f fds tail fs k
  end.

(* Given a storage schema [SC], a filter [F], and a
   tactic [k] which processes filters, convert [F] into
   a search term (a list of boolean functions over the tuples in
   [SC]. *)
Ltac findGoodTerm SC F k :=
  match F with
    | fun a => ?[@?f a] =>
      match type of f with
        | forall a, {?X = _!?fd} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
        | forall a, {_!?fd = ?X} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
        | forall a, {?X = _``?fd} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
        | forall a, {_``?fd = ?X} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
      end
    | fun a => (@?f a) && (@?g a) =>
      findGoodTerm SC f ltac:(fun fds1 tail1 =>
                                findGoodTerm SC g ltac:(fun fds2 tail2 =>
                                                          k (fds1, fds2) (fun tup : @Tuple SC => (tail1 tup) && (tail2 tup))))
    | _ => k tt F
  end.

Ltac find_simple_search_term qs_schema idx filter_dec search_term :=
  match type of search_term with
    | BuildIndexSearchTerm ?attr =>
     let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
              findGoodTerm SC filter_dec
                           ltac:(fun fds tail =>
                                   let tail := eval simpl in tail in
                                       makeTerm attr SC fds tail
                                                ltac:(fun tm => pose tm; try unify tm search_term;
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
      | |- ExtensionalEq (fun a => (@?f a)) ?b =>
        let fT := type of f in
        makeEvar
          fT
          ltac:(fun f' => k)
    end.

  (* Convert List_Query_In Where Clauses into a filter using search terms. *)
  Ltac convert_Where_to_search_term :=
    (* First replace Where clauses with test functions. *)
    simpl; repeat (setoid_rewrite refine_List_Query_In_Where;
                   instantiate (1 := _)); simpl;
    (* Combine different filters into a single function. *)
    repeat setoid_rewrite <- filter_and;
    (* Now break the functions up again and find search term replacements for each. *)
    match goal with
        |- context [List_Query_In (filter ?f _) _] =>
        let T := type of f in
        makeEvar T
                 ltac:(fun g =>
                         let eqv := fresh in
                         assert (ExtensionalEq f g) as eqv;
                       [ apply ExtensionalEq_andb_true; split_filters idtac
                       | setoid_rewrite (filter_by_equiv f g eqv)])
    end.

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

  Ltac convert_filter_to_find':=
    try match goal with
            |- context[filter (fun a => (_ && _) && true) _] =>
            setoid_rewrite <- andb_assoc; simpl
        end;
    match goal with
      | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[l <- CallBagMethod ?idx ``("Enumerate") ?r_n ();
                    List_Query_In (filter (fun a => MatchIndexSearchTerm ?st (ilist_hd a) && @?filter_rest a)
                                          (Build_single_Tuple_list (snd l))) ?resultComp] =>
        let b := fresh in
        pose proof (@refine_Query_For_In_Find_single _ _ _ r_o r_n H idx st resultComp filter_rest) as b;
          simpl in b; setoid_rewrite b; clear b

      | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[l <- CallBagMethod ?idx ``("Enumerate") ?r_n ();
                    l' <- Join_Lists (Build_single_Tuple_list (snd l)) ?cl;
                    List_Query_In (filter (fun a => MatchIndexSearchTerm ?st (ilist_hd (ilist_tl a)) && @?filter_rest a)
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
                    List_Query_In (filter (fun a => MatchIndexSearchTerm (Dep_SearchTerm_Wrapper ?st' (ilist_hd (ilist_tl a)))
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

Theorem BookStoreManual :
  Sharpened BookStoreSpec.
Proof.

  unfold BookStoreSpec.

  (* First, we unfold various definitions and drop constraints *)
  start honing QueryStructure.

  make simple indexes using [[sAUTHOR; sISBN]; [sISBN]].

  hone constructor "Init".
  {
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    finish honing.
  }

  hone method "NumOrders".
  {
    simplify with monad laws.
    implement_In.
    setoid_rewrite refine_Join_Enumerate_Swap; eauto.
    convert_Where_to_search_term.

    find_equivalent_search_term 1 find_simple_search_term.
    find_equivalent_search_term_pair 1 0 find_simple_search_term_dep.

    convert_filter_to_find.
    Implement_Aggregates.
    commit.
    finish honing.
  }

  hone method "GetTitles".
  {
    simplify with monad laws.
    implement_In.
    convert_Where_to_search_term.

    find_equivalent_search_term 0 find_simple_search_term.

    convert_filter_to_find.
    Implement_Aggregates.
    commit.
    finish honing.
}

  hone method "DeleteOrder".
  {
    implement_QSDeletedTuples find_simple_search_term.
    simplify with monad laws; cbv beta; simpl.
    implement_EnsembleDelete_AbsR find_simple_search_term.
    simplify with monad laws.
    finish honing.
  }

  (* At this point our implementation is fully computational: we're done! *)

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
    end; simpl; split.

  Fixpoint Build_IndexedQueryStructure_Impl_Sigs
    {indices : list NamedSchema}
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
    : list NamedADTSig :=
    match indices as indices return ilist _ indices -> list NamedADTSig with
      | nil => fun _ => nil
      | cons ns indices' =>
        fun Index =>
          {| ADTSigname := relName ns;
             namedADTSig := 
               BagSig (@Tuple (schemaHeading (relSchema ns))) (BagSearchTermType (ilist_hd Index)) (BagUpdateTermType (ilist_hd Index)) |}
                       :: @Build_IndexedQueryStructure_Impl_Sigs indices' (ilist_tl Index)
    end Index.

  Fixpoint Build_IndexedQueryStructure_Impl_Specs
           {indices : list NamedSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
  : ilist (fun ns => ADT (namedADTSig ns)) (@Build_IndexedQueryStructure_Impl_Sigs indices Index) :=
    match indices as indices return
          forall (Index : ilist _ indices),
            ilist (fun ns : NamedADTSig => ADT (namedADTSig ns))
                  (@Build_IndexedQueryStructure_Impl_Sigs indices Index)
    with
      | nil => fun _ => inil _
      | cons ns indices' =>
        fun Index => icons {| ADTSigname := relName ns;
                              namedADTSig := _ |}
                           (@BagSpec (@Tuple (schemaHeading (relSchema ns)))
                                     (BagSearchTermType (ilist_hd Index))
                                     (BagUpdateTermType (ilist_hd Index))
                                     (BagMatchSearchTerm (ilist_hd Index))
                                     (BagApplyUpdateTerm (ilist_hd Index)))
                           (@Build_IndexedQueryStructure_Impl_Specs indices' (ilist_tl Index))
    end Index.
  
  Definition Build_IndexedQueryStructure_Impl_cRep
           {indices : list NamedSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns)) (@Build_IndexedQueryStructure_Impl_Sigs indices Index))
  : Type
    :=
    i2list
      (fun (ns : NamedADTSig)
           (index : cADT (namedADTSig ns)) => cRep index) DelegateImpls.

  Fixpoint map_IndexedQS_idx_boundi
        {indices}
  : forall
      n
      (Index : ilist
                 (fun ns : NamedSchema =>
                    SearchUpdateTerms (schemaHeading (relSchema ns)))
                 indices)
      idx, 
      nth_error
        (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index))
        n = Some idx
      ->  nth_error (map relName indices) n = Some idx.
  Proof.
    refine (match indices with
              | nil => _
              | ns :: indices' =>
                fun n => 
                  match n return
                        forall
                          (Index : ilist
                                     (fun ns : NamedSchema =>
                                        SearchUpdateTerms (schemaHeading (relSchema ns)))
                                     (ns :: indices'))
                          idx,
                          nth_error (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)) n =
                          Some idx ->
                          nth_error (map relName (ns :: indices')) n = Some idx
                  with
                    | 0 => fun Index idx nth_n => nth_n
                    | S n' => fun Index => (map_IndexedQS_idx_boundi indices' n' (ilist_tl Index))
                  end
            end);
    simpl; intros; try discriminate; eauto.
  Defined.
  
  Definition map_IndexedQS_idx
             indices
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
             (idx : BoundedIndex
                      (map ADTSigname
                           (Build_IndexedQueryStructure_Impl_Sigs Index)))
  : BoundedIndex (map relName indices) := 
    {| bindex := bindex idx;
       indexb := {| ibound := ibound (indexb idx);
                    boundi := map_IndexedQS_idx_boundi _ Index (boundi (indexb idx))|} |}.

  Fixpoint map_IndexedQS_idx_boundi'
        {indices}
  : forall
      n
      (Index : ilist
                 (fun ns : NamedSchema =>
                    SearchUpdateTerms (schemaHeading (relSchema ns)))
                 indices)
      idx, 
      nth_error (map relName indices) n = Some idx
      -> nth_error
        (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index))
        n = Some idx.
  Proof.
    refine (match indices with
              | nil => _
              | ns :: indices' =>
                fun n => 
                  match n return
                        forall
                          (Index : ilist
                                     (fun ns : NamedSchema =>
                                        SearchUpdateTerms (schemaHeading (relSchema ns)))
                                     (ns :: indices'))
                          idx,
                          nth_error (map relName (ns :: indices')) n = Some idx
                          -> nth_error (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)) n = Some idx
                  with
                    | 0 => fun Index idx nth_n => nth_n
                    | S n' => fun Index => (map_IndexedQS_idx_boundi' indices' n' (ilist_tl Index))
                  end
            end);
    simpl; intros; try discriminate; eauto.
  Defined.
  
  Definition map_IndexedQS_idx'
             indices
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
             (idx : BoundedIndex (map relName indices))
  : BoundedIndex
                      (map ADTSigname
                           (Build_IndexedQueryStructure_Impl_Sigs Index)) := 
    {| bindex := bindex idx;
       indexb := {| ibound := ibound (indexb idx);
                    boundi := map_IndexedQS_idx_boundi' _ Index (boundi (indexb idx))|} |}.

  Lemma ith_Build_IndexedQueryStructure_Impl_Sigs_eq
        {indices}
  : forall
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
      (idx : BoundedIndex
               (map ADTSigname
                    (Build_IndexedQueryStructure_Impl_Sigs Index))),
      (BagSig (@Tuple (schemaHeading (relSchema ((nth_Bounded relName indices (map_IndexedQS_idx Index idx))))))
              (BagSearchTermType
                 (ith_Bounded relName Index (map_IndexedQS_idx Index idx)))
              (BagUpdateTermType
                 (ith_Bounded relName Index (map_IndexedQS_idx Index idx))))
      = namedADTSig
          (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index) idx).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply (IHindices (ilist_tl Index) idx n nth_n).
  Defined.

  Lemma ith_Build_IndexedQueryStructure_Impl_Specs_eq
        {indices}
  : forall
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
      (idx : BoundedIndex
               (map ADTSigname
                    (Build_IndexedQueryStructure_Impl_Sigs Index))),
      ith_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Specs Index) idx = 
  eq_rect _ ADT
          (@BagSpec (@Tuple (schemaHeading (relSchema (@nth_Bounded NamedSchema string relName
                                                                    indices (map_IndexedQS_idx Index idx)))))
                    (BagSearchTermType (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                    (BagUpdateTermType (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                    (BagMatchSearchTerm (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                    (BagApplyUpdateTerm (ith_Bounded _ Index (map_IndexedQS_idx Index idx))))
                    _ (ith_Build_IndexedQueryStructure_Impl_Sigs_eq Index idx).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply (IHindices (ilist_tl Index) idx n nth_n).
  Defined.
        
  Definition map_IndexedQS_Rep 
             {indices}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
             idx
             (rep : @IndexedEnsemble
                      (@Tuple
                         (schemaHeading
                            (relSchema
                               (@nth_Bounded NamedSchema string relName
                                             indices (map_IndexedQS_idx Index idx) )))))
  : Rep
      (ith_Bounded ADTSigname
                   (Build_IndexedQueryStructure_Impl_Specs Index) idx).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n rep.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply IHindices; eauto.
  Defined.

  Definition map_IndexedQS_Rep'
             {indices}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
             idx
             (rep : Rep
                      (ith_Bounded ADTSigname
                                   (Build_IndexedQueryStructure_Impl_Specs Index)
                                   (map_IndexedQS_idx' Index idx)))
  : @IndexedEnsemble
      (@Tuple
         (schemaHeading
            (relSchema
               (@nth_Bounded NamedSchema string relName
                             indices idx )))).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n rep.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply (IHindices (ilist_tl Index)); eauto.
  Defined.
    
  Definition Build_IndexedQueryStructure_Impl_AbsR
             {qs_schema : QueryStructureSchema}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
             (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                                     (Build_IndexedQueryStructure_Impl_Sigs Index))
             (ValidImpl :
                forall idx,
                  refineADT (ith_Bounded ADTSigname
                                         (Build_IndexedQueryStructure_Impl_Specs Index) idx)
                            (LiftcADT (ith_Bounded ADTSigname DelegateImpls idx)))
             (r_o : IndexedQueryStructure qs_schema Index)
             (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls)
  : Prop := 
    forall idx,
      AbsR (ValidImpl idx)
           (map_IndexedQS_Rep Index idx (GetIndexedRelation r_o (map_IndexedQS_idx Index idx)))
           (i2th_Bounded ADTSigname r_n idx).

  Definition map_IndexedQS_Rep''
             {indices}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
             idx
             (rep : @IndexedEnsemble
                      (@Tuple
                         (schemaHeading
                            (relSchema
                               (@nth_Bounded NamedSchema string relName
                                             indices idx)))))
  : Rep
      (ith_Bounded ADTSigname
                   (Build_IndexedQueryStructure_Impl_Specs Index) (map_IndexedQS_idx' Index idx)).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n rep.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply IHindices; eauto.
  Defined.

  Definition Build_IndexedQueryStructure_Impl_AbsR''
             {qs_schema : QueryStructureSchema}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
             (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                                     (Build_IndexedQueryStructure_Impl_Sigs Index))
             (ValidImpl :
                forall idx : BoundedIndex (map relName (qschemaSchemas qs_schema)),
                  refineADT (ith_Bounded ADTSigname
                                         (Build_IndexedQueryStructure_Impl_Specs Index) (map_IndexedQS_idx' Index idx))
                            (LiftcADT (ith_Bounded ADTSigname DelegateImpls (map_IndexedQS_idx' Index idx))))
             (r_o : IndexedQueryStructure qs_schema Index)
             (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls)
  : Prop := 
    forall idx,
      AbsR (ValidImpl idx)
           (map_IndexedQS_Rep'' Index idx (GetIndexedRelation r_o idx))
           (i2th_Bounded ADTSigname r_n (map_IndexedQS_idx' Index idx)).

  Definition CallBagImplMethod
             {qs_schema : QueryStructureSchema}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
             (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                                    (Build_IndexedQueryStructure_Impl_Sigs Index))
             idx midx
             (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls) :=
    cMethods (ith_Bounded ADTSigname DelegateImpls idx) midx (i2th_Bounded _ r_n idx).

  Definition CallBagImplConstructor
             {qs_schema : QueryStructureSchema}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
             (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                                    (Build_IndexedQueryStructure_Impl_Sigs Index))
             idx midx :=
    cConstructors (ith_Bounded ADTSigname DelegateImpls idx) midx .

  Fixpoint Build_IndexedQueryStructure_Impl_midx
           {indices}
           (P : ADTSig -> Type)
  : forall (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
             ridx
             (midx : P
                       (BagSig (@Tuple (schemaHeading
                            (relSchema
                               (@nth_Bounded NamedSchema string relName
                                             indices (map_IndexedQS_idx Index ridx ) ))))
                               (BagSearchTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                               (BagUpdateTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx))))),
      P
        (namedADTSig
           (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)
                        ridx)) := 
    match indices return
          forall (Index : ilist
                            (fun ns : NamedSchema =>
                               SearchUpdateTerms (schemaHeading (relSchema ns)))
                            indices)
                 (ridx : BoundedIndex
                           (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)))
                 (midx : P
                       (BagSig (@Tuple (schemaHeading
                            (relSchema
                               (@nth_Bounded NamedSchema string relName
                                             indices (map_IndexedQS_idx Index ridx ) ))))
                               (BagSearchTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                               (BagUpdateTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx))))),
      P
        (namedADTSig
           (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)
                        ridx))
    with
      | nil => fun _ ridx => BoundedIndex_nil _ ridx
      | ns :: indices' =>
        fun Index ridx =>  
          match ridx with
            | {| bindex := ridx;
                 indexb := {|ibound := n;
                             boundi := nth_n |}|} => 
              match n return
                    forall
                      (Index' : ilist
                                  (fun ns : NamedSchema =>
                                     SearchUpdateTerms (schemaHeading (relSchema ns))) (ns :: indices'))
                      ridx nth_n,
                      let idx := {| bindex := ridx;
                                    indexb := {|ibound := n;
                                                boundi := nth_n |}|} in 
                      P
                                (BagSig (@Tuple (schemaHeading
                                                   (relSchema
                                                      (@nth_Bounded NamedSchema string relName
                                                                    (ns :: indices') (map_IndexedQS_idx Index' idx ) ))))
                                        (BagSearchTermType
                                           (ith_Bounded relName Index' (map_IndexedQS_idx Index' idx)))
                                        (BagUpdateTermType
                                           (ith_Bounded relName Index' (map_IndexedQS_idx Index' idx)))) -> 
                      P
                        (namedADTSig
                           (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index')
                                        {| bindex := ridx;
                                           indexb := {|ibound := n;
                                                       boundi := nth_n |}|}))
              with
                | 0 => fun Index idx nth_n midx => midx
                | S n' => fun Index idx nth_n midx =>
                            (@Build_IndexedQueryStructure_Impl_midx
                               indices' P (ilist_tl Index)
                               {| bindex := idx;
                                  indexb := {|ibound := n';
                                              boundi := nth_n |}|}
                               midx)
              end Index ridx nth_n 
                            end
         end.  


(*fst
    (MethodDomCod
       (BagSig Tuple (BagSearchTermType (ith_Bounded relName Index ridx))
          (BagUpdateTermType (ith_Bounded relName Index ridx))) midx)"
 while it is expected to have type
 "fst
    (MethodDomCod
       (namedADTSig
          (nth_Bounded ADTSigname
             (Build_IndexedQueryStructure_Impl_Sigs Index) ridx')) midx')" *)
  
  Definition Build_IndexedQueryStructure_Impl_MethodDom
           {indices}
  : forall (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           ridx
           midx,
      fst (MethodDomCod
             (BagSig (@Tuple (schemaHeading (relSchema (nth_Bounded relName indices  ridx))))
                     (BagSearchTermType
                        (ith_Bounded relName Index ridx))
                     (BagUpdateTermType
                        (ith_Bounded relName Index ridx)))
             midx)
    -> fst
        (MethodDomCod
           (namedADTSig
              (nth_Bounded ADTSigname
                           (Build_IndexedQueryStructure_Impl_Sigs Index) (map_IndexedQS_idx' Index ridx)))
           (Build_IndexedQueryStructure_Impl_midx MethodIndex Index (map_IndexedQS_idx' Index ridx) midx)).
  Proof.
    destruct ridx as [idx [n nth_n]]; revert Index idx n nth_n.
    induction indices.
  - destruct n; simpl; discriminate.
  - destruct n; simpl; eauto.
    intros; eapply (IHindices (ilist_tl Index) idx n nth_n); eauto.
  Defined.

  Definition Build_IndexedQueryStructure_Impl_MethodCod
           {indices}
  : forall (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           ridx
           midx,
      snd
        (MethodDomCod
           (namedADTSig
              (nth_Bounded ADTSigname
                           (Build_IndexedQueryStructure_Impl_Sigs Index) (map_IndexedQS_idx' Index ridx)))
           (Build_IndexedQueryStructure_Impl_midx MethodIndex Index (map_IndexedQS_idx' Index ridx) midx))
  ->       snd (MethodDomCod
             (BagSig (@Tuple (schemaHeading (relSchema (nth_Bounded relName indices  ridx))))
                     (BagSearchTermType
                        (ith_Bounded relName Index ridx))
                     (BagUpdateTermType
                        (ith_Bounded relName Index ridx)))
             midx)
.
  Proof.
    destruct ridx as [idx [n nth_n]]; revert Index idx n nth_n.
    induction indices.
  - destruct n; simpl; discriminate.
  - destruct n; simpl; eauto.
    intros; eapply (IHindices (ilist_tl Index) idx n nth_n); eauto.
  Defined.

Lemma ith_Build_IndexedQueryStructure_Impl_Methods
        {indices}
  : forall
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
      (idx : BoundedIndex
               (map ADTSigname
                    (Build_IndexedQueryStructure_Impl_Sigs Index))),
      Methods (ith_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Specs Index) idx) = 
      eq_rect _ (fun r => forall idx, methodType (Rep r) _ _ )
              (Methods (eq_rect _ ADT
                                (@BagSpec (@Tuple (schemaHeading (relSchema (@nth_Bounded NamedSchema string relName
                                                                                          indices (map_IndexedQS_idx Index idx)))))
                                          (BagSearchTermType (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                                          (BagUpdateTermType (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                                          (BagMatchSearchTerm (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                                          (BagApplyUpdateTerm (ith_Bounded _ Index (map_IndexedQS_idx Index idx))))
                                _ (ith_Build_IndexedQueryStructure_Impl_Sigs_eq Index idx)))
              _ (eq_sym (ith_Build_IndexedQueryStructure_Impl_Specs_eq Index idx)).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply (IHindices (ilist_tl Index) idx n nth_n).
  Defined.
  
  Lemma refine_Mapped_Methods
        {indices}
        (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (indices) )
  :  forall
      ridx,
      forall
        (r_o : @IndexedEnsemble (@Tuple (schemaHeading (relSchema (nth_Bounded relName indices ridx)))))
      midx 
      d r s,
        let ridx' := map_IndexedQS_idx' Index ridx in 
        let midx' := Build_IndexedQueryStructure_Impl_midx MethodIndex Index ridx' midx in
        let d' := Build_IndexedQueryStructure_Impl_MethodDom Index ridx _ d in
Methods
     (ith_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Specs Index) ridx') midx'
     (map_IndexedQS_Rep'' Index ridx r_o) d'
     ↝ (r, s) ->
Methods
  (BagSpec (BagMatchSearchTerm (ith_Bounded relName Index ridx))
           (BagApplyUpdateTerm (ith_Bounded relName Index ridx))) midx r_o d
   ↝ (map_IndexedQS_Rep' Index ridx r,
     Build_IndexedQueryStructure_Impl_MethodCod Index ridx midx s).
  Proof.
    intros; pose proof (ith_Build_IndexedQueryStructure_Impl_Methods Index ridx') as H';
    rewrite H' in H; revert H; clear H'.
    unfold d', midx', ridx' in *; clear ridx' midx' d'.
    revert r_o d r s.
    intro; eapply (Iterate_Dep_Type_BoundedIndex_equiv_1) with (idx := midx);
    simpl.
    intuition;
      simpl in *;
      first [revert midx r_o d r s H
            | revert midx r_o b a r s H ];
    try (destruct ridx as [idx [n nth_n]];
      revert idx n nth_n;
      unfold IndexedQueryStructure, GetIndexedRelation in *;
      unfold list_ind, list_rect in *;
      induction indices; destruct n; simpl; try (intros; discriminate); eauto;
      eapply IHindices).
  Qed.
  
  Lemma refine_BagImplMethods
        {qs_schema : QueryStructureSchema}
        (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
        (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                               (Build_IndexedQueryStructure_Impl_Sigs Index))
        ValidImpl
  :  forall (r_o : IndexedQueryStructure qs_schema Index)
            (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls)
            ridx,
            let ridx' := map_IndexedQS_idx' Index ridx in 
            forall (midx : MethodIndex
                     (BagSig Tuple
                             (BagSearchTermType
                                (ith_Bounded relName Index (map_IndexedQS_idx Index ridx')))
                             (BagUpdateTermType
                                (ith_Bounded relName Index (map_IndexedQS_idx Index ridx')))))
                   (d : fst
                          (MethodDomCod
                             (BagSig (@Tuple (schemaHeading (relSchema (nth_Bounded relName (qschemaSchemas qs_schema) ridx))))
                                     (BagSearchTermType (ith_Bounded relName Index ridx))
                                     (BagUpdateTermType (ith_Bounded relName Index ridx))) midx)),
       let midx' := Build_IndexedQueryStructure_Impl_midx MethodIndex Index ridx' midx in
       let d' := Build_IndexedQueryStructure_Impl_MethodDom Index ridx _ d in
       Build_IndexedQueryStructure_Impl_AbsR'' ValidImpl r_o r_n ->
       exists r_o',
         AbsR (ValidImpl ridx) r_o' (fst (CallBagImplMethod ridx' midx' r_n d'))
         /\ refine (CallBagMethod ridx midx r_o d)
                   (ret (map_IndexedQS_Rep' _ _ r_o',
                         Build_IndexedQueryStructure_Impl_MethodCod Index ridx _
                                                                    (snd (CallBagImplMethod (map_IndexedQS_idx' Index ridx) midx' r_n d')))).
    intros.
    pose proof (ADTRefinementPreservesMethods (ValidImpl ridx) midx'
                                              (map_IndexedQS_Rep'' Index ridx
                                                                 (GetIndexedRelation r_o ridx))
                                              (i2th_Bounded _ r_n ridx') d' (H ridx) (ReturnComputes _)).
    Local Arguments map_IndexedQS_Rep : simpl never.
    inversion_by computes_to_inv; subst.
    exists (fst x);
      unfold CallBagImplMethod; simpl in *. 
      split; simpl.
      - pose proof (f_equal fst H3) as eq_x0; simpl in eq_x0.
        rewrite eq_x0 in H2; simpl in H2; apply H2.
    - pose proof (f_equal snd H3) as eq_x; simpl in eq_x.
      assert (refine (CallBagMethod ridx midx r_o d)
                     (ret
                        (map_IndexedQS_Rep' Index ridx (fst x),
                         Build_IndexedQueryStructure_Impl_MethodCod Index ridx midx (snd x))));
        [ | rewrite eq_x in H0;  eapply H0 ].
      intros v Comp_v; simpl in *; inversion_by computes_to_inv; subst.
      destruct x; simpl @fst in *; simpl @snd in *.
      unfold ridx' in *.
      revert H1.
      Local Transparent CallBagMethod.
      eapply refine_Mapped_Methods.
  Qed.

  (*Fixpoint Build_IndexedQueryStructure_Impl_ConstructorDom
           {indices}
           {struct indices}
  : forall (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
             ridx
             (midx : ConstructorIndex
                       (BagSig (@Tuple (schemaHeading
                            (relSchema
                               (@nth_Bounded NamedSchema string relName
                                             indices (map_IndexedQS_idx Index ridx ) ))))
                               (BagSearchTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                               (BagUpdateTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx))))),
      (ConstructorDom
             (BagSig Tuple
                     (BagSearchTermType
                        (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                     (BagUpdateTermType
                        (ith_Bounded relName Index (map_IndexedQS_idx Index ridx))))
             midx) -> 
      (ConstructorDom
             (namedADTSig
                (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)
                             ridx))
             (Build_IndexedQueryStructure_Impl_midx ConstructorIndex Index ridx midx)) := 
    match indices return
          forall (Index : ilist
                            (fun ns : NamedSchema =>
                               SearchUpdateTerms (schemaHeading (relSchema ns)))
                            indices)
                 (ridx : BoundedIndex
                           (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)))
                 (midx : ConstructorIndex
                       (BagSig (@Tuple (schemaHeading
                            (relSchema
                               (@nth_Bounded NamedSchema string relName
                                             indices (map_IndexedQS_idx Index ridx ) ))))
                               (BagSearchTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                               (BagUpdateTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx))))),
            (ConstructorDom
                   (BagSig Tuple
                           (BagSearchTermType
                              (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                     (BagUpdateTermType
                        (ith_Bounded relName Index (map_IndexedQS_idx Index ridx))))
                   midx) -> 
            (ConstructorDom
                   (namedADTSig
                      (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)
                                   ridx))
                   (Build_IndexedQueryStructure_Impl_midx ConstructorIndex Index ridx midx))
    with
      | nil => fun _ ridx => BoundedIndex_nil _ ridx
      | ns :: indices' =>
        fun Index ridx =>  
          match ridx with
            | {| bindex := ridx;
                 indexb := {|ibound := n;
                             boundi := nth_n |}|} => 
              match n return
                    forall
                      (Index' : ilist
                                  (fun ns : NamedSchema =>
                                     SearchUpdateTerms (schemaHeading (relSchema ns))) (ns :: indices'))
                      ridx nth_n,
                      let idx := {| bindex := ridx;
                                    indexb := {|ibound := n;
                                                boundi := nth_n |}|} in 
                      forall (midx : ConstructorIndex (BagSig (@Tuple (schemaHeading
                                                     (relSchema
                                                        (@nth_Bounded NamedSchema string relName
                                                                      (ns :: indices') (map_IndexedQS_idx Index' idx ) ))))
                                          (BagSearchTermType
                                             (ith_Bounded relName Index' (map_IndexedQS_idx Index' idx)))
                                          (BagUpdateTermType
                                             (ith_Bounded relName Index' (map_IndexedQS_idx Index' idx))))),
                      (ConstructorDom
                             (BagSig Tuple
                                     (BagSearchTermType
                                        (ith_Bounded relName Index' (map_IndexedQS_idx Index' idx)))
                                     (BagUpdateTermType
                                        (ith_Bounded relName Index' (map_IndexedQS_idx Index' idx))))
                             midx) -> 
                      (ConstructorDom
                             (namedADTSig
                                (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index')
                                             idx))
                             (Build_IndexedQueryStructure_Impl_midx ConstructorIndex Index' idx midx))
              with
                | 0 => fun Index idx nth_n midx d => d
                | S n' => fun Index idx nth_n midx d =>
                            (@Build_IndexedQueryStructure_Impl_ConstructorDom
                               indices' (ilist_tl Index)
                               {| bindex := idx;
                                  indexb := {|ibound := n';
                                              boundi := nth_n |}|}
                               midx d)
              end Index ridx nth_n 
                            end
         end.

  Lemma ith_Build_IndexedQueryStructure_Impl_Constructors
        {indices}
  : forall
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
      (idx : BoundedIndex
               (map ADTSigname
                    (Build_IndexedQueryStructure_Impl_Sigs Index))),
      Constructors (ith_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Specs Index) idx) = 
      eq_rect _ (fun r => forall idx, constructorType (Rep r) _ )
              (Constructors (eq_rect _ ADT
                                (@BagSpec (@Tuple (schemaHeading (relSchema (@nth_Bounded NamedSchema string relName
                                                                                          indices (map_IndexedQS_idx Index idx)))))
                                          (BagSearchTermType (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                                          (BagUpdateTermType (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                                          (BagMatchSearchTerm (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                                          (BagApplyUpdateTerm (ith_Bounded _ Index (map_IndexedQS_idx Index idx))))
                                _ (ith_Build_IndexedQueryStructure_Impl_Sigs_eq Index idx)))
              _ (eq_sym (ith_Build_IndexedQueryStructure_Impl_Specs_eq Index idx)).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply (IHindices (ilist_tl Index) idx n nth_n).
  Defined.

  Lemma refine_Mapped_Constructors
        {indices}
        (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (indices) )
  :  forall
      ridx
      (midx : ConstructorIndex
                (BagSig Tuple
                        (BagSearchTermType
                           (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                        (BagUpdateTermType
                           (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))))
      d r,
      Constructors (ith_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Specs Index) ridx) (Build_IndexedQueryStructure_Impl_midx ConstructorIndex Index ridx midx)
                   (Build_IndexedQueryStructure_Impl_ConstructorDom Index ridx midx d)
                   ↝ r ->
      Constructors
        (BagSpec (BagMatchSearchTerm (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                 (BagApplyUpdateTerm (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))) midx d
   ↝ map_IndexedQS_Rep' Index ridx r.
  Proof.
    intros; pose proof (ith_Build_IndexedQueryStructure_Impl_Constructors Index ridx) as H';
      simpl ith_Bounded in *; rewrite H' in H; revert H.
    clear H'.
    revert d r.
    eapply Iterate_Dep_Type_BoundedIndex_equiv_1 with (idx := midx).
    simpl; intuition.
    simpl in *.
    revert midx d r H.
    destruct ridx as [idx [n nth_n]];
      revert idx n nth_n;
      unfold IndexedQueryStructure, GetIndexedRelation in *;
      unfold list_ind, list_rect in *;
      induction indices; destruct n; simpl; try (intros; discriminate); eauto;
      eapply IHindices.
  Qed.

  Check refine_BagImplMethods.
  Check CallBagImplConstructor.
    
  Lemma refine_BagImplConstructors
        {qs_schema : QueryStructureSchema}
        (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
        (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                               (Build_IndexedQueryStructure_Impl_Sigs Index))
        (ValidImpl : forall
                        idx : BoundedIndex
                                (map ADTSigname
                                   (Build_IndexedQueryStructure_Impl_Sigs
                                      Index)),
                      refineADT
                        (ith_Bounded ADTSigname
                           (Build_IndexedQueryStructure_Impl_Specs Index)
                           idx)
                        (LiftcADT (ith_Bounded ADTSigname DelegateImpls idx)))
  :  forall (ridx : BoundedIndex
                   (map ADTSigname
                      (Build_IndexedQueryStructure_Impl_Sigs Index)))
            (midx : ConstructorIndex
                     (BagSig Tuple
                             (BagSearchTermType
                                (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                             (BagUpdateTermType
                                (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))))
            d,
       let midx' := Build_IndexedQueryStructure_Impl_midx ConstructorIndex Index ridx midx in
       let d' := Build_IndexedQueryStructure_Impl_ConstructorDom Index ridx midx d in
       exists r_o',
         AbsR (ValidImpl ridx) r_o' (CallBagImplConstructor _ DelegateImpls ridx midx' d')
         /\ refine (CallBagConstructor _ _ (map_IndexedQS_idx Index ridx) midx d)
                   (ret (map_IndexedQS_Rep' _ _ r_o')) .
  Proof.
    intros.
    pose proof (ADTRefinementPreservesConstructors (ValidImpl ridx) midx'
                                                   d' (ReturnComputes _)).
    inversion_by computes_to_inv; subst.
    exists x;
      unfold CallBagImplConstructor; simpl in *; split; simpl.
    - eassumption.
    - intros v Comp_v; simpl in *; inversion_by computes_to_inv; subst.
      Local Transparent CallBagConstructor.
      eapply refine_Mapped_Constructors; eauto.
  Qed.
 *)

  Definition Build_IndexedQueryStructure_Impl_AbsR'
             {qs_schema : QueryStructureSchema}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
             (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                                     (Build_IndexedQueryStructure_Impl_Sigs Index))
             (ValidImpl :
                forall idx,
                  refineADT (ith_Bounded ADTSigname
                                         (Build_IndexedQueryStructure_Impl_Specs Index) idx)
                            (LiftcADT (ith_Bounded ADTSigname DelegateImpls idx)))
             (r_o : IndexedQueryStructure qs_schema Index)
             (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls)
  : Prop := 
      @Build_IndexedQueryStructure_Impl_AbsR''
        qs_schema Index DelegateImpls
        (fun idx => ValidImpl (map_IndexedQS_idx' Index idx))
        r_o
        r_n.
  
  FullySharpenEachMethod
    (Build_IndexedQueryStructure_Impl_Sigs Index)
    (Build_IndexedQueryStructure_Impl_Specs Index)
    (Build_IndexedQueryStructure_Impl_cRep Index)
    (@Build_IndexedQueryStructure_Impl_AbsR' BookStoreSchema Index).

  Focus 3.

  intros.
  Opaque CallBagMethod.
  simplify with monad laws.
  simpl in *. unfold Build_IndexedQueryStructure_Impl_AbsR' in *.
  match goal with
      H : Build_IndexedQueryStructure_Impl_AbsR'' (qs_schema := ?qs_schema) ?ValidImpl ?r_o ?r_n
      |- context[CallBagMethod (BagIndexKeys := ?Index') ?ridx ?midx ?r_o ?d] =>
      let r_o' := fresh "r_o'" in
      let AbsR_r_o' := fresh "AbsR_r_o'" in 
      let refines_r_o := fresh "refines_r_o'" in 
      destruct (@refine_BagImplMethods qs_schema Index' _ ValidImpl r_o r_n ridx midx d H) as [r_o' [AbsR_r_o' refines_r_o']]; 
      unfold map_IndexedQS_idx' in refines_r_o', AbsR_r_o'; simpl in refines_r_o', AbsR_r_o';
      setoid_rewrite refines_r_o'; simpl in *; simplify with monad laws; simpl
  end.

  refine pick val _.

  Focus 2.
  unfold Build_IndexedQueryStructure_Impl_AbsR''.
  
  
  
  simpl.
  Set Printing Implicit.
  idtac.
  rewrite H2.
  
  pose (e q i _ r i0 b b0 b1 p).


  
  Focus 3.
  
    [BagSig Book (BuildSearchTermFromAttributes BookSearchTerm);
                           BagSig Order (BuildSearchTermFromAttributes OrderSearchTerm)]
                         (icons _ (BagSpec (SearchTermFromAttributesMatcher BookSearchTerm))
                         (icons _ (BagSpec (SearchTermFromAttributesMatcher OrderSearchTerm))
                                (inil ADT)))
                         (fun DelegateImpl : ilist cADT
                                                [BagSig Book (BuildSearchTermFromAttributes BookSearchTerm);
                                                  BagSig Order (BuildSearchTermFromAttributes OrderSearchTerm)] => prod (cRep (ilist_hd DelegateImpl)) (cRep (ilist_hd (ilist_tl DelegateImpl))))
                         (fun (DelegateImpl : ilist cADT
                                                [BagSig Book (BuildSearchTermFromAttributes BookSearchTerm);
                                                  BagSig Order (BuildSearchTermFromAttributes OrderSearchTerm)])
                              (ValidImpl :
                                 forall n, Dep_Option_elim_T2
                                             (fun Sig adt adt' => @refineADT Sig adt (LiftcADT adt'))
                                             (ith_error (icons _ (BagSpec (SearchTermFromAttributesMatcher BookSearchTerm))
                         (icons _ (BagSpec (SearchTermFromAttributesMatcher OrderSearchTerm))
                                (inil ADT))) n)
                                             (ith_error DelegateImpl n))
                        (r_o : IndexedQueryStructure BookStoreSchema BookStoreIndices)
                        r_n =>
                      AbsR (ValidImpl 0)
                           (GetIndexedRelation r_o {| bindex := sBOOKS |})
                           (fst r_n) /\
                      AbsR (ValidImpl 1)
                           (GetIndexedRelation r_o {| bindex := sORDERS |})
                           (snd r_n)).
    simpl; split;
    intros; unfold GetIndexedRelation, i2th_Bounded, ith_Bounded_rect; simpl.

  - simplify with monad laws; simpl.

  let H := fresh in
  pose proof (Iterate_Dep_Type_BoundedIndex_equiv_2 _ (ADTRefinementPreservesConstructors (ValidImpl 1))) as H; simpl in H; intuition.
  let H := fresh in
  pose proof (Iterate_Dep_Type_BoundedIndex_equiv_2 _ (ADTRefinementPreservesConstructors (ValidImpl 0))) as H; simpl in H; intuition.

  rewrite refineEquiv_pick_pair.
  assert (refine
            {r_n : cRep (ilist_hd (ilist_tl DelegateImpl)) |
             AbsR (ValidImpl 1) (Empty_set IndexedElement) r_n}
            (r_o' <- ret (Empty_set IndexedElement);
             {r_n : cRep (ilist_hd (ilist_tl DelegateImpl)) |
              AbsR (ValidImpl 1) r_o' r_n})) as H' by
      (setoid_rewrite refineEquiv_bind_unit; reflexivity);
    setoid_rewrite H'; setoid_rewrite (a d); clear H'.

  assert (refine
            {r_n : cRep (ilist_hd DelegateImpl) |
             AbsR (ValidImpl 0) (Empty_set IndexedElement) r_n}
            (r_o' <- ret (Empty_set IndexedElement);
             {r_n : cRep (ilist_hd DelegateImpl) |
              AbsR (ValidImpl 0) r_o' r_n})) as H' by
      (setoid_rewrite refineEquiv_bind_unit; reflexivity);
    setoid_rewrite H'; setoid_rewrite (a0 d); clear H'.

  simplify with monad laws.

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

  higher_order_2_reflexivity''.
  - constructor.
  - simpl; split; intros; intuition.
    let H := fresh in
    pose proof (Iterate_Dep_Type_BoundedIndex_equiv_2 _ (ADTRefinementPreservesMethods (ValidImpl 1))) as H.
    Opaque Methods.
    simpl Iterate_Dep_Type_BoundedIndex in H. intuition.
    simplify with monad laws.
    setoid_rewrite refineEquiv_pick_pair; simplify with monad laws.
    simpl.

    Lemma refineEquiv_duplicate_bind {A B : Type}
    : forall (c : Comp A) (k : A -> A -> Comp B),
        refine (a <- c; a' <- c; k a a')
               (a <- c; k a a).
    Proof.
      unfold refine; intros; inversion_by computes_to_inv;
      repeat (econstructor; eauto).
    Qed.

    rewrite refineEquiv_duplicate_bind.
    setoid_rewrite get_update_indexed_eq.
    Check get_update_indexed_neq.
    simpl in *|-*.
    match goal with
        |- context[GetIndexedRelation (UpdateIndexedRelation ?r ?idx _ ) ?idx'] =>
        assert (idx <> idx') as H' by
                                 (unfold not; intros; discriminate);
          setoid_rewrite (fun n => @get_update_indexed_neq _ _ r idx idx' n H')
    end.
    setoid_rewrite (refine_pick_val _ H0); simplify with monad laws.

    match goal with
        |- context [CallBagMethod _ _ _ ?d] => pose proof (a3 _ _ d H1)
    end.

    Eval cbv beta in (snd r_n) .
    pose (@refineCallMethod _ (BagSpec (SearchTermFromAttributesMatcher
                                          (ith_Bounded relName BookStoreIndices
                                                       (GetRelationKey BookStoreSchema sORDERS))))
                            (ilist_hd (ilist_tl DelegateImpl)) (ValidImpl 1)
                            {| bindex := "Delete" |} _ _ _ H).
    destruct_ex; intuition.
    rewrite H3.
    simplify with monad laws.
    rewrite H2.
    simplify with monad laws.
    simpl.
    destruct x.
    simpl in *.
    rewrite H4; simpl.
    higher_order_2_reflexivity''.

    Opaque Methods.

    let H := fresh in
    pose proof (Iterate_Dep_Type_BoundedIndex_equiv_2 _ (ADTRefinementPreservesMethods (ValidImpl 0))) as H.
    simpl Iterate_Dep_Type_BoundedIndex in H. intuition.
    simplify with monad laws.
    setoid_rewrite refineEquiv_pick_pair; simplify with monad laws.
    simpl.

    simpl in *|-*.

    match goal with
        |- context [CallBagMethod _ _ _ ?d] => pose proof (a0 _ _ d H0)
    end.

    pose (@refineCallMethod _ (BagSpec (SearchTermFromAttributesMatcher
                                          (ith_Bounded relName BookStoreIndices
                                                       (GetRelationKey BookStoreSchema sBOOKS))))
                            (ilist_hd DelegateImpl) (ValidImpl 0)
                            {| bindex := "Find" |} _ _ _ H).
    destruct_ex; intuition.
    rewrite H3.
    simplify with monad laws.
    refine pick val a.
    simplify with monad laws.
    refine pick val b.
    simplify with monad laws.
    destruct x.
    simpl in H4; rewrite H4.
    simpl.
    let x := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(x) end in
    let f := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(f) end in
    let a := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(a) end in
    let b := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(b) end in
    let b' := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(b') end in
    let c := match goal with |- ?R (ret ?x) (ret (?f ?a (?b, ?b') ?c)) => constr:(c) end in
    let x' := (eval pattern a, b, b', c in x) in
    let f' := match x' with ?f' _ _ _ _ => constr:(fun i a => f' i (fst a) (snd a)) end in
    unify f f';
      cbv beta;
      solve [apply reflexivity].
    eauto.
    eauto.
Defined.

(*Definition BookStoreImpl : ComputationalADT.cADT BookStoreSig.
  extract implementation of BookStoreManual using (inil _).
Defined.

Print BookStoreImpl. *)
