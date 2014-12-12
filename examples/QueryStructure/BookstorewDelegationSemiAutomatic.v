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

(* implement_In' implements [UnConstrQuery_In] in a variety of contexts. *)
Ltac implement_In' :=
  match goal with
    (* Implement a List_Query_In of a list [l] applied to a UnConstrQuery_In [idx]
        by enumerating [idx] with a method call and joining the result with [l] *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- context[fun b' : ?ElementT => List_Query_In (@?l b') (fun b => UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx (@?f b' b) )] ] =>
      let H' := eval simpl in
      (fun (b' : ElementT) => refine_Join_Query_In_Enumerate' H (idx := idx) (f b') (l b')) in
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

  Fixpoint Join_ListsT (Ts : list Type) : Type
    :=
      match Ts with
        | [] => unit
        | [A] => A
        | A :: Cs => prod A (Join_ListsT Cs)
      end.
  
  Inductive list' (A : Type) : Type :=
  | nil' : list' A | cons' : A -> list' A -> list' A.

  Fixpoint list'_to_list
           (A : Type)
           (l : list' A)
  : list A :=
    match l with
      | nil' => nil
      | cons' a As => cons a (list'_to_list As)
    end.

  Fixpoint list_to_list'
           (A : Type)
           (l : list A)
  : list' A :=
    match l with
      | nil => nil' A
      | cons a As => cons' a (list_to_list' As)
    end.

  Lemma list_to_list'_id {A : Type}
  : forall l : list' A,
      list_to_list' (list'_to_list l) = l.
  Proof.
    induction l; simpl; congruence.
  Qed.

  Lemma list'_to_list_id {A : Type}
  : forall l : list A,
      list'_to_list (list_to_list' l) = l.
  Proof.
    induction l; simpl; congruence.
  Qed.

  (* Fixpoint Join_Lists''
           {A : Type}
           (Ts : list A)
           (f : A -> Type)
           (ls : ilist (fun a => list' (f a))  Ts)
  : @list (ilist f Ts). *)

  Lemma refineEquiv_Join_bind {A B C}
  : let T := Type in
    forall (ca : Comp A)
           (cb : Comp B)
           (c : A -> B -> Comp C),
      refine (a <- ca;
              b <- cb;
              c a b)
             (ab <- (a <- ca;
                     b <- cb;
                     ret (icons (A := T) (B := id) A a (icons (A := T) (B := id) B b (inil id))));
              c (ith_default (A := T) (B := id) unit () ab 0)
                (ith_default (A := T) (B := id) unit () ab 1)).
  Proof.
    intros * v Comp_v; inversion_by computes_to_inv; subst;
    repeat econstructor; eauto.
  Qed.

  (*Lemma refineEquiv_Join_bind' {A B C} {D D'}
  : forall (ca : Comp (D * (list A)))
           (cb : Comp (D' * (list B)))
           (c : list (A * B) -> Comp C),
      refine (a <- ca;
              b <- cb;
              c (Join_Lists (snd a) (Build_single_Tuple_list (snd b))))
             (ab <- (a <- ca;
                     b <- cb;
                     ret (icons A (list_to_list' (snd a)) (icons B (list_to_list' (snd b)) (inil list'))));
              c (Join_Lists'' ab)).
  Proof.
    intros; rewrite refineEquiv_Join_bind.
    simpl; intros v Comp_v; inversion_by computes_to_inv; subst.
    repeat econstructor; eauto.
    simpl in *; repeat rewrite list'_to_list_id in H1; eauto.
  Qed. *)
  
  hone method "NumOrders".
  {
    simplify with monad laws.
    implement_In.
    simpl; repeat (setoid_rewrite refine_List_Query_In_Where;
                   instantiate (1 := _)); simpl; 
    repeat setoid_rewrite <- filter_and.
    match goal with
        |- context[filter ?f _] =>
        let T := type of f in 
        makeEvar T
                 ltac:(fun g =>
                         let eqv := fresh in 
                         assert (ExtensionalEq f g) as eqv;
                       [
                       | setoid_rewrite (filter_by_equiv f g eqv)])
    end.

    Lemma ExtensionalEq_andb {A} :
      forall (f g f' g' : A -> bool),
        ExtensionalEq f f'
        -> ExtensionalEq g g'
        -> ExtensionalEq (fun a => f a && g a) (fun a => f' a && g' a).
    Proof.
      unfold ExtensionalEq; intros; congruence.
    Qed.

    Ltac split_filters k :=
      match goal with
          |- ExtensionalEq (fun a => (@?f a) && (@?g a)) ?b =>
          let fT := type of f in
          let gT := type of g in
          makeEvar
            fT
            ltac:(fun f' =>
                    makeEvar gT ltac:(fun g' =>
                                        apply (@ExtensionalEq_andb _ f g f' g');
                                      [ first [split_filters | k ] | first [split_filters | k]] ))
    end.

    split_filters idtac.

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

    Focus 2.

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

Ltac find_simple_search_term_dep qs_schema idx dom filter_dec search_term :=
  match type of search_term with
    | ?dom -> BuildIndexSearchTerm ?attr =>
      let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
      findGoodTerm_dep SC filter_dec
                       ltac:(fun fds tail =>
                               let tail := eval simpl in tail in
                                   makeTerm_dep dom attr SC fds tail
                                                ltac:(fun tm => pose tm;
                                                      (* unification fails if I don't pose tm first... *) unify tm search_term;
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

Unset Ltac Debug.
find_equivalent_search_term_pair 0 1 find_simple_search_term_dep.

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

find_equivalent_search_term 0 find_simple_search_term.
simpl
Focus 3.
match goal with
    |- ExtensionalEq ?f ?b =>
    get_ithDefault f 0 ltac:(fun l => pose l)
end.

  hone method "DeleteOrder".
  {
    implement_QSDeletedTuples find_simple_search_term.
    simplify with monad laws; cbv beta; simpl.
    implement_EnsembleDelete_AbsR find_simple_search_term.
    simplify with monad laws.
    finish honing.
  }



    setoid_rewrite r.
    setoid_rewrite refine_Join_Query_In_Enumerate'.
    refine_List_Query_In_Where.
    implement_Enumerate_filter find_simple_search_term.
    simplify with monad laws.
    simpl; implement_Pick_DelegateToBag_AbsR_observer; simplify with monad laws.
    setoid_rewrite refine_List_Query_In_Return.
    simplify with monad laws.
    finish honing.
  }

  hone method "GetTitles".
  {
    setoid_rewrite refine_Query_In_Enumerate; eauto.
    setoid_rewrite refine_List_Query_In_Where.
    implement_Enumerate_filter find_simple_search_term.
    simplify with monad laws.
    simpl; implement_Pick_DelegateToBag_AbsR_observer; simplify with monad laws.
    setoid_rewrite refine_List_Query_In_Return.
    simplify with monad laws.
    finish honing.
  }

  hone method "NumOrders".
  {

  unfold cast, eq_rect_r, eq_rect, eq_sym; simpl.

  (* At this point our implementation is fully computational: we're done! *)

  Require Import ADTNotation.BuildComputationalADT.
  Require Import ADT.ComputationalADT.

  Ltac FullySharpenEachMethod delegateSigs delegateSpecs cRep' cAbsR' :=
    match goal with
        |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
        ilist_of_evar
          (ilist ComputationalADT.cADT delegateSigs)
          (fun DelegateImpl Sig => cMethodType (cRep' DelegateImpl) (methDom Sig) (methCod Sig))
          methSigs
          ltac:(fun cMeths => ilist_of_evar
                                (ilist ComputationalADT.cADT delegateSigs)
                                (fun DelegateImpl Sig =>
                                   cConstructorType (cRep' DelegateImpl) (consDom Sig))
                                consSigs
                                ltac:(fun cCons =>
                                        eapply Notation_Friendly_SharpenFully with
                                        (DelegateSpecs := delegateSpecs)
                                          (cConstructors := cCons)
                                          (cMethods := cMeths)
                                          (cAbsR := cAbsR')));
          unfold Dep_Type_BoundedIndex_app_comm_cons
    end.

  FullySharpenEachMethod [BagSig Book (BuildSearchTermFromAttributes BookSearchTerm);
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
