Require Import QueryStructureNotations.
Require Import ListImplementation.
Require Import KVEnsembles ADTCache CacheSpec.
Require Import AutoDB.

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

(* So, first let's give the type signatures of the methods. *)
Definition BookStoreSig : ADTSig :=
  ADTsignature {
      "Init" : unit → rep,
      "AddBook" : rep × Book → rep × bool,
      "NumTitles" : rep × string → rep × nat,
      "NumOrders" : rep × string → rep × nat
    }.

(* Now we write what the methods should actually do. *)
Definition BookStoreSpec : ADT BookStoreSig :=
  QueryADTRep BookStoreSchema {
    const "Init" (_ : unit) : rep := empty,

    update "AddBook" ( b : Book ) : bool :=
        Insert b into sBOOKS ,

    query "NumTitles" ( author : string ) : nat :=
      Count (For (b in sBOOKS)
             Where (author = b!sAUTHOR)
             Return ()),

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

(* Aliases for the two tables *)
Definition GetBooks (or : UnConstrQueryStructure BookStoreSchema)
  := GetUnConstrRelation or Books.
Definition GetOrders (or : UnConstrQueryStructure BookStoreSchema)
  := GetUnConstrRelation or Orders.

(* Now we define an index structure for each table. *)
Definition BookStorage : @BagPlusBagProof Book.
  mkIndex BookSchema [ BookSchema/sAUTHOR; BookSchema/sISBN ].
Defined.
(* In other words, index first on the author field, then the ISBN field.
 * Works especially efficiently for accesses keyed on author. *)

Definition OrderStorage : @BagPlusBagProof Order.
  mkIndex OrderSchema [ OrderSchema/sISBN ].
Defined.

(* Each index has an associate datatype.  Let's name each one. *)
Definition TBookStorage := BagType BookStorage.
Definition TOrderStorage := BagType OrderStorage.

Section CachingRefinement.

  Definition CacheSpec := @CacheSpec string nat.
  Variable LRUCache : Sharpened CacheSpec.
  Definition CacheImpl := projT1 LRUCache.
  Definition CacheAbs : Rep CacheSpec -> Rep CacheImpl -> Prop :=
    AbsR (projT2 LRUCache).

  Definition CacheInvariant
             (or : UnConstrQueryStructure BookStoreSchema)
             (cache : Rep CacheSpec) :=
    forall author count,
      cache (author,  count)
      -> refine
           (Count (For (UnConstrQuery_In or Books
                                         (fun d =>
                                            Where (author = d!sAUTHOR)
                                                  Return ()))))
           (ret count).

(* This abstraction relation connects:
 * 1. Abstract database from reference implementation, using sets
 * 2. Our fancy realization, using search trees (from Bags library)
 * 3. The invariant that the cache holds valid queries *)

Definition BookStore_AbsR
           (or : UnConstrQueryStructure BookStoreSchema)
           (nr : TBookStorage * TOrderStorage) : Prop :=
  or!sBOOKS ≃ benumerate (fst nr) /\ or!sORDERS ≃ benumerate (snd nr).

Definition CachedBookStore_AbsR
           (or :  cachedRep (UnConstrQueryStructure BookStoreSchema)
                            (Rep CacheSpec))
           (nr : (TBookStorage * TOrderStorage)
                  * (Rep CacheImpl)) : Prop :=
  BookStore_AbsR (origRep or) (fst nr) /\ CacheAbs (cachedVal or) (snd nr).


Ltac observer''' AbsR storages :=
  unfold AbsR in *; split_and; concretize;
  asPerm storages; commit.

Ltac observer'' :=
  match goal with
    | [ _ : ?AbsR _ _ |- _ ] =>
      match type of AbsR with
        | UnConstrQueryStructure _ -> ?T -> Prop =>
          let storages := storageOf T in observer''' AbsR storages;
                                        pose storages
      end
  end.

  Definition CachedBookStore :
    Sharpened BookStoreSpec.
  Proof.
    unfold BookStoreSpec.

    start honing QueryStructure.

    hone representation using (cachedRep_AbsR CacheInvariant).

    hone method "NumOrders".
    { simplify with monad laws.
      setoid_rewrite (refine_pick_val _ H0).
      simplify with monad laws.
      unfold cachedRep_AbsR in H0; intuition; subst; simpl.
      finish honing.
    }

    hone method "NumTitles".
    { simplify with monad laws.
      etransitivity.
      apply refine_Pick_Some_dec with (P := fun v => cachedVal r_n (n, v)); intros.
      { destruct H0; subst; unfold CacheInvariant in *|- .
        rewrite H2 by eassumption.
        simplify with monad laws; cbv beta; simpl.
        refine pick val _; try split; eauto.
        simplify with monad laws.
        finish honing.
      }
      {
        unfold cachedRep_AbsR in *|-; simpl; split_and; subst.
        rewrite refine_under_bind; [reflexivity | ].
        intros; rewrite refine_pick_cachedRep.
        simplify with monad laws.
        assert (refine {cv | CacheInvariant (origRep r_n) cv}
                       (c <- (callMeth CacheSpec "AddKey" (cachedVal r_n) (n, a));
                        ret (fst c))).
        repeat econstructor.
        inversion_by computes_to_inv; subst.
        unfold CacheInvariant; intros.
        unfold SubEnsembleInsert in H1.
        intros H7; destruct (H2 _ H4); injections.
        unfold refine; intros; inversion_by computes_to_inv; subst; eauto.
        apply H3; eauto.
        rewrite H2.
        simplify with monad laws.
        simpl.
        refine pick pair.
        simplify with monad laws.
        refine pick val _; eauto using SubEnsembleInsertRefl.
        simplify with monad laws.
        refine pick val true.
        simplify with monad laws.
        finish honing.
        right; intuition.
        destruct H4; eauto.
      }
      finish honing.
    }

    hone constructor "Init".
    { simplify with monad laws.
      rewrite refine_pick_cachedRep.
      refine pick val (fun _ : string * nat => False).
      simplify with monad laws; finish honing.
      unfold CacheInvariant; simpl.
      intuition.
    }

    hone method "AddBook".
    {
      simplify with monad laws; cbv beta; simpl.
      etransitivity.
      eapply refine_bind_pick; intros.
      setoid_rewrite refine_pick_cachedRep.
      simplify with monad laws.
      simpl.
      apply refine_under_bind.
      intros; apply refine_under_bind.
      intros; apply refine_under_bind.
      intros.
      etransitivity.
      apply refine_bind.
      apply refine_if with (b := a0) (ea := ret (cachedVal r_n));
        intros; subst; simpl;
        [ | refine pick val _; [ reflexivity| eapply H0]].
      apply refine_if with (b := a1) (ea := ret (cachedVal r_n));
        intros; subst; simpl;
        [ | refine pick val _; [ reflexivity| eapply H0]].
      pose (n!sAUTHOR) as author; simpl in author.
      pose (callMeth CacheSpec "UpdateKey" (cachedVal r_n)) as Update.
      simpl in Update.
      apply refine_if with (b := a2)
                           (ea := ret (cachedVal r_n))
                           (ta := (r' <- Update (author, S);
                      ret (fst r')));
        intros; subst; simpl;
        [ | refine pick val _; [ reflexivity| eapply H0]].
      repeat econstructor.
      unfold Update in *; clear Update.
      inversion_by computes_to_inv; subst.
      unfold CacheInvariant; intros.
      apply H5 in H6; unfold In in *.
      destruct H6; split_and.
      destruct_ex; split_and; subst.
      etransitivity.
      apply refine_refine_Count.
      apply refine_For_In_Insert.
      unfold In, not; intros; eapply H1;
      [ eapply H6
      | subst_body; auto ].
      rewrite refine_Count_bind_bind_app.
      unfold cachedRep_AbsR, CacheInvariant in H0; split_and; subst.
      set (n!sAUTHOR); simpl in *.
      etransitivity.
      apply refine_if with (b := if (string_dec d author)
                                 then true
                                 else false);
        find_if_inside; try discriminate; subst; intros.
      { setoid_rewrite refine_Count at 1; simplify with monad laws;
        unfold Query_Where at 1; refine pick val [()];
        [ | intuition; econstructor].
        simplify with monad laws.
        rewrite H7.
        simplify with monad laws; simpl; reflexivity.
        apply H10.
      }
      {
        setoid_rewrite refine_Count at 1; simplify with monad laws;
        unfold Query_Where; refine pick val [];
        [ | intuition; econstructor].
        simplify with monad laws.
        destruct H5; split_and; try congruence.
        setoid_rewrite H7; [reflexivity | ].
        eapply H10.
      }
      destruct (string_dec d author); subst;
      [reflexivity | unfold d, author in *; congruence].
      { destruct H6; simpl in *; etransitivity.
        eapply refine_refine_Count.
        apply refine_For_In_Insert.
        unfold In, not; intros; eapply H1;
        [ eapply H9
        | subst_body; auto ].
        rewrite refine_Count_bind_bind_app.
        unfold author in *.
        setoid_rewrite refine_Count at 1; simplify with monad laws;
        unfold Query_Where; refine pick val [];
        [ | intuition; econstructor ].
        simplify with monad laws.
        destruct H0; split_and; try congruence.
        eapply H9; eauto.
      }
      unfold pointwise_relation; intros.
      higher_order_1_reflexivity.
      higher_order_1_reflexivity.
      destruct H0; subst.
      finish honing.
    }

    hone representation using CachedBookStore_AbsR.
    hone constructor "Init".
    { simplify with monad laws.
      unfold CachedBookStore_AbsR.
      refine pick pair.
      etransitivity.
      apply refine_bind.
      unfold BookStore_AbsR.
      splitPick; reflexivity.
      intro.
      (* Rewriting with the cache implementation. *)
      assert (refine {c | CacheAbs (fun _ : string * nat => False) c}
                     (callCons CacheImpl "EmptyCache" ())).
      {
        pose (ADTRefinementPreservesConstructors (projT2 LRUCache) {| bindex := "EmptyCache" |}).
        simpl in r; rewrite <- r.
        rewrite refineEquiv_bind_unit; f_equiv.
      }
      higher_order_1_reflexivity.
      simplify with monad laws.
      finish honing.
    }

    hone method "NumOrders".
    {
      simplify with monad laws.
      unfold CachedBookStore_AbsR.
      etransitivity.
      apply refine_bind.
      destruct H0; clear H1.
      observer''; reflexivity.
      intro; destruct H0.
      refine pick pair; simplify with monad laws.
      refine pick val _ ; try eassumption.
      simplify with monad laws.
      refine pick val _ ; try eassumption.
      simplify with monad laws.
      finish honing.
      simpl.
      finish honing.
    }

    hone method "NumTitles".
    { simplify with monad laws.
      pose (callMeth CacheImpl "LookupKey" (snd r_n) n).
      assert (refine {b |
                      forall b' : nat,
                        (b = Some b' -> cachedVal or (n, b')) /\
                        (b = None -> forall b'0 : nat, ~ cachedVal or (n, b'0))}
                     (o <- callMeth CacheImpl "LookupKey" (snd r_n) n;
                      ret (snd o))).
      {
        pose (ADTRefinementPreservesMethods (projT2 LRUCache) {| bindex := "LookupKey" |}
                                            (cachedVal or) (snd r_n) n (proj2 H0)).
        simpl in r.
        pose_string_ids.
        rewrite <- r.
        unfold refine; intros; inversion_by computes_to_inv; subst.
        simpl in *.
        destruct H2; destruct x2; eauto.
      }
      rewrite H1; simplify with monad laws.
      etransitivity; [apply refine_under_bind | ]; intros.
      rewrite refine_If_Opt_Then_Else_Bind; apply refine_If_Opt_Then_Else.
      { intro.
        simplify with monad laws.
        refine pick val _; simpl; eauto.
        simplify with monad laws; higher_order_1_reflexivity.
      }
      {
        unfold CachedBookStore_AbsR in *; split_and.
        simplify with monad laws.
        etransitivity.
        apply refine_bind.
        observer''; reflexivity.
        intro.
        refine pick pair; simplify with monad laws.
        simpl.
        refine pick val _; eauto using SubEnsembleInsertRefl.
        simplify with monad laws.
        refine pick val _; eauto.
        simplify with monad laws.
        higher_order_1_reflexivity.
        simplify with monad laws.
        reflexivity.
      }
      simpl; finish honing.
    }

    hone method "AddBook".
    {
      unfold CachedBookStore_AbsR in *;
      unfold BookStore_AbsR in *; split_and.
      simpl.
      simplify with monad laws.
      pruneDuplicates.
      pickIndex.
      fundepToQuery.
      concretize.
      etransitivity.
      apply refine_bind.
      simpl in *.
      let T := storageOf (prod TBookStorage TOrderStorage) in
      asPerm T.
      commit.
      reflexivity.
      intro.
      Split Constraint Checks.
      simplify with monad laws.
      etransitivity.
      apply refine_bind.
      reflexivity.
      intro.
      refine pick pair.
      simplify with monad laws.
      etransitivity.
      refineEquiv_pick_pair_benumerate.
      repeat (rewrite refine_pick_val by (refine_list_insert_in_other_table || binsert_correct_DB); simplify with monad laws); reflexivity.
      higher_order_1_reflexivity.
      pose (callMeth CacheImpl "UpdateKey" (snd r_n)).
      assert (forall kv, refine
                           (or <- (callMeth CacheSpec "UpdateKey" (cachedVal or) kv);
                            {b | CacheAbs (fst or) b})
                           (nr <- c kv; ret (fst nr))).
      {
        intros;
        pose (ADTRefinementPreservesMethods (projT2 LRUCache) {| bindex := "UpdateKey" |}
                                            _ _ kv H2).
        unfold c; subst_strings. rewrite <- r.
        repeat rewrite refineEquiv_bind_bind.
        f_equiv; unfold pointwise_relation; intros.
        rewrite refineEquiv_bind_bind; simpl.
        setoid_rewrite refineEquiv_bind_unit; simpl.
        setoid_rewrite refineEquiv_unit_bind.
        reflexivity.
      }
      simpl in H4.
      set (n!sAUTHOR).
      specialize (H4 (d, S )).
      simpl in H4.
      subst_body.
      rewrite <- refineEquiv_bind_bind, H4.
      simplify with monad laws.
      reflexivity.
      simplify with monad laws.
      refine pick val r_n; eauto.
      simplify with monad laws; reflexivity.
      simplify with monad laws.
      finish honing.
    }

    finish sharpening.

  Defined.

End CachingRefinement.
