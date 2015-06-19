Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindSuffixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation
        Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsSchema
        Fiat.Examples.DnsServer.DnsLemmas.


Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "AddData" : rep x DNSRRecord -> rep x bool,
      Method "Process" : rep x packet -> rep x packet
    }.

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

                                               (* in start honing querystructure, it inserts constraints before every insert / decision procedure *)
                                               (* n<- count (For (r in _) where (r = tup) return True); if n > 0 then.. *)
                                               (* For refines decision procedure *)
    update "AddData" (t : DNSRRecord) : bool :=
      Insert t into sCOLLECTIONS,

    query "Process" (p : packet) : packet :=
      let t := qtype (questions p) in
      Repeat 1 initializing n with qname (questions p)
               defaulting rec with (ret (buildempty p))
         {{ rs <- For (r in sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                  Where (IsSuffix n r!sNAME) (* prefixed with [n] to [rs] *)
                  (* prefix: "com.google" is a prefix of "com.google.scholar" *)
                  Return r;
            If (negb (is_empty rs))        (* Are there any matching records? *)
            Then                    (* TODO: reverse these if/then cases *)
              bfrs <- [[r in rs | upperbound name_length rs r]]; (* Find the best match (largest prefix) in [rs] *)
              b <- { b | decides b (forall r, List.In r bfrs -> n = r!sNAME) };
              if b                (* If the record's QNAME is an exact match  *)
              then
                unique b,                         (* only one match (unique / otherwise) *)
                List.In b bfrs /\ b!sTYPE = CNAME     (* If the record is a CNAME, *)
                               /\ t <> CNAME ->>      (* and the query did not request a CNAME *)

                  p' <- rec b!sNAME;                  (* Recursively find records matching the CNAME *)
                                                    (* ?? Shouldn't this use the sDATA ?? *)
                  ret (addan p' b)
                      (* addan : packet -> DNSRRecord -> packet *)
                otherwise ->>     (* Copy the records into the answer section of an empty response *)
                (* multiple matches -- add them all as answers in the packet *)
                  ret (List.fold_left addan bfrs (buildempty p))
              else              (* prefix but record's QNAME not an exact match *)
                (* return all the prefix records that are nameserver records -- 
                 ask the authoritative servers *)
                bfrs' <- [[x in bfrs | x!sTYPE = NS]];
                ret (List.fold_left addns bfrs' (buildempty p))
            Else ret (buildempty p) (* No matching records! *)
          }}}.

(* -------------------------------------------------------------------------------------- *)

(* Refinement lemmas that depend on DnsSchema (other lemmas are in DnsLemmas) *)

(* implement the DNS record constraint check as code that counts the number of occurrences of
the constraint being broken (refines the boolean x1 in AddData) *)
Lemma refine_count_constraint_broken :
  forall (n : DNSRRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedTuple (GetHeading DnsSchema sCOLLECTIONS),
                       (r!sCOLLECTIONS)%QueryImpl tup' ->
                       n!sNAME = (indexedElement tup')!sNAME -> n!sTYPE <> CNAME)}
           (If (beq_RRecordType n!sTYPE CNAME)
               Then count <- Count
               For (UnConstrQuery_In r ``(sCOLLECTIONS)
                                     (fun tup : Tuple =>
                                        Where (n!sNAME = tup!sNAME)
                                              Return tup ));
            ret (beq_nat count 0) Else ret true).
Proof.
  intros; setoid_rewrite refine_pick_decides at 1;
  [ | apply refine_is_CNAME__forall_to_exists | apply refine_not_CNAME__independent ].
  (* refine existence check into query. *)
  match goal with
      |- context[{b | decides b
                              (exists tup : @IndexedTuple ?heading,
                                 (@GetUnConstrRelation ?qs_schema ?qs ?tbl tup /\ @?P tup))}]
      =>
      let H1 := fresh in
      let H2 := fresh in
      makeEvar (Ensemble (@Tuple heading))
               ltac:(fun P' => assert (Same_set (@IndexedTuple heading) (fun t => P' (indexedElement t)) P) as H1;
                     [unfold Same_set, Included, Ensembles.In;
                       split; [intros x H; pattern (indexedElement x);
                               match goal with
                                   |- ?P'' (indexedElement x) => unify P' P'';
                                     simpl; eauto
                               end
                              | eauto]
                     |
                     assert (DecideableEnsemble P') as H2;
                       [ simpl; eauto with typeclass_instances (* Discharge DecideableEnsemble w/ intances. *)
                       | setoid_rewrite (@refine_constraint_check_into_query' qs_schema tbl qs P P' H2 H1); clear H1 H2 ] ]) end.
  remember n!sTYPE; refine pick val (beq_RRecordType d CNAME); subst;
  [ | case_eq (beq_RRecordType n!sTYPE CNAME); intros;
      rewrite <- beq_RRecordType_dec in H; find_if_inside;
      unfold not; simpl in *; try congruence ].
  simplify with monad laws.
  autorewrite with monad laws.
  setoid_rewrite negb_involutive.
  reflexivity.
Qed.


(* uses refine_forall_to_exists; refines x2 in AddData 
very similar to refine_count_constraint_broken; comments below are relative to refine_count_constraint_broken *)
Lemma refine_count_constraint_broken' :
  forall (n : DNSRRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedTuple (GetHeading DnsSchema sCOLLECTIONS),
                       (r!sCOLLECTIONS)%QueryImpl tup' ->
                       (indexedElement tup')!sNAME = n!sNAME (* switched *)
                       -> (indexedElement tup')!sTYPE <> CNAME)} (* indexedElement tup', not n *)
           (* missing the If/Then statement *)
           (count <- Count
                  For (UnConstrQuery_In r ``(sCOLLECTIONS)
                                        (fun tup : Tuple =>
                                           Where (n!sNAME = tup!sNAME
                                                  /\ tup!sTYPE = CNAME ) (* extra /\ condition *)
                                                 Return tup ));
            ret (beq_nat count 0)).
Proof.
  intros; setoid_rewrite refine_forall_to_exists.
  (*refine existence check into query. *)
  match goal with
      |- context[{b | decides b
                              (exists tup : @IndexedTuple ?heading,
                                 (@GetUnConstrRelation ?qs_schema ?qs ?tbl tup /\ @?P tup))}]
      =>
      let H1 := fresh in
      let H2 := fresh in
      makeEvar (Ensemble (@Tuple heading))
               ltac:(fun P' => assert (Same_set (@IndexedTuple heading) (fun t => P' (indexedElement t)) P) as H1;
                     [unfold Same_set, Included, Ensembles.In;
                       split; [intros x H; pattern (indexedElement x);
                               match goal with
                                   |- ?P'' (indexedElement x) => unify P' P'';
                                     simpl; eauto
                               end
                              | eauto]
                     |
                     assert (DecideableEnsemble P') as H2;
                       [ simpl; eauto with typeclass_instances (* Discharge DecideableEnsemble w/ intances. *)
                       | setoid_rewrite (@refine_constraint_check_into_query' qs_schema tbl qs P P' H2 H1); clear H1 H2 ] ]) end.
  (* apply @DecideableEnsemble_And.  apply DecideableEnsemble_EqDec.
  apply Query_eq_list. apply DecideableEnsemble_EqDec. apply Query_eq_RRecordType.
  Print Instances DecideableEnsemble. *)
  simplify with monad laws.
  setoid_rewrite negb_involutive; f_equiv.
Qed.

(* ------------------------ *)
(* Debugging lemmas for prefix lemma *)

Check BoundedIndex.
Print BoundedIndex.

(*
Lemma minimal: 
    let heading := <sNAME :: name, sTYPE :: RRecordType, 
                   sCLASS :: RRecordClass, sTTL :: nat, 
                   sDATA :: string>%Heading : Heading in

    let BStringId0 := ``(sNAME) (* : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] *) in
    let BStringId1 := ``(sTYPE) (* : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] *) in

    let schma := {|
          schemaHeading := heading;
          attrConstraints := None;
          tupleConstraints := Some
                                (fun t t' : Tuple =>
                                   GetAttribute t BStringId0 =
                                   GetAttribute t' BStringId0 ->
                                   GetAttribute t BStringId1 <> CNAME) |}
                 : Schema in
 
    True.
(* CNAME error *)
Proof.
Admitted.

Check GetAttribute.
Print GetAttribute.
Check Attributes.
Print Attributes.
Locate GetAttribute.

Lemma minimal_annotated: 
    let heading := <sNAME :: name, sTYPE :: RRecordType, 
                   sCLASS :: RRecordClass, sTTL :: nat, 
                   sDATA :: string>%Heading : Heading in

    let BStringId0 := ``(sNAME) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in
    let BStringId1 := ``(sTYPE) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in
    (* annotated, error goes away when schma is commented out *)
    let schma := {|
          schemaHeading := heading;
          attrConstraints := None;
          tupleConstraints := Some
                                (fun t t' : Tuple =>
                                   (* typeclass magic error? *)
                                   @GetAttribute heading t BStringId0 =
                                   @GetAttribute heading t' BStringId0 ->
                                   @GetAttribute heading t BStringId1 <> CNAME) |}
                 : Schema in
 
    True.
Proof.

Admitted.
*)

Ltac inv H := inversion H; clear H; try subst.

(* TODO: move into another file if possible
TODO: clean up annotations/typeclass magic *)
Lemma found_names_are_prefixes_of_question : 
    (* large context here is pasted from the proof *)
    let StringId2 := "EqualityIndex" : string in
    let StringId3 := "Name" : string in
    let BStringId := ``(sCOLLECTIONS) : BoundedIndex [sCOLLECTIONS] in
    let BStringId2 := ``(StringId3)
                      : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in


    let heading := <sNAME :: name, sTYPE :: RRecordType, 
  sCLASS :: RRecordClass, sTTL :: nat, 
  sDATA :: string>%Heading : Heading in

    (* let SearchTerm := @BuildIndexSearchTerm heading *)
    (*                     [{| *)
    (*                         KindIndexKind := StringId2; *)
    (*                         KindIndexIndex := BStringId2 |}] :  *)
    (*                     Type in *)

    (* TODO *)
    let SearchTerm := @BuildIndexSearchTerm heading
                  (@Datatypes.cons (@KindIndex heading)
                     (@Build_KindIndex heading StringId2 BStringId2)
                     (@Datatypes.nil (@KindIndex heading)))
                  (prod (option (Domain heading BStringId2))
                     (@Tuple heading -> bool)) : Type in
    (* TODO *)
    (* let SearchUpdateTerm := {| *)
    (*       BagSearchTermType := SearchTerm; *)
    (*       BagMatchSearchTerm := MatchIndexSearchTerm; *)
    (*       BagUpdateTermType := Tuple -> Tuple; *)
    (*       BagApplyUpdateTerm := fun z : Tuple -> Tuple => z |} *)
    (*                         : SearchUpdateTerms heading in *)

let  SearchUpdateTerm := @Build_SearchUpdateTerms heading SearchTerm
                        (@MatchIndexSearchTerm heading
                           (@Datatypes.cons (@KindIndex heading)
                              (@Build_KindIndex heading StringId2 BStringId2)
                              (@Datatypes.nil (@KindIndex heading)))
                           (prod (option (Domain heading BStringId2))
                              (@Tuple heading -> bool))
                           (fun
                              (st : prod (option (Domain heading BStringId2))
                                      (@Tuple heading -> bool))
                              (tup : @Tuple heading) =>
                            andb
                              match
                                @fst (option (Domain heading BStringId2))
                                  (@Tuple heading -> bool) st 
                                return bool
                              with
                              | Some val =>
                                  match
                                    @list_eq_dec string string_dec
                                      (@GetAttribute heading tup BStringId2)
                                      val return bool
                                  with
                                  | left _ => true
                                  | right _ => false
                                  end
                              | None => true
                              end
                              (@snd (option (Domain heading BStringId2))
                                 (@Tuple heading -> bool) st tup)))
                        (@Tuple heading -> @Tuple heading)
                        (fun z : @Tuple heading -> @Tuple heading => z)
                   : SearchUpdateTerms heading in

    let BStringId0 := ``(sNAME) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in
    let BStringId1 := ``(sTYPE) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in

    let schma := {|
          schemaHeading := heading;
          attrConstraints := None;
          tupleConstraints := Some
                                (fun t t' : Tuple =>
                                   @GetAttribute heading t BStringId0 =
                                   @GetAttribute heading t' BStringId0 ->
                                   @GetAttribute heading t BStringId1 <> CNAME) |}
                 : Schema in
    let   nschma := relation sCOLLECTIONS has (schma)%NamedSchema : NamedSchema in

  (* TODO *)
    (* let Index := icons SearchUpdateTerm *)
    (*                    (inil *)
    (*                       (fun ns : NamedSchema => *)
    (*                          SearchUpdateTerms (schemaHeading (relSchema ns)))) *)
    (*               : ilist *)
    (*                  (fun ns : NamedSchema => *)
    (*                     SearchUpdateTerms (schemaHeading (relSchema ns))) *)
    (*                  [nschma] in *)

  let Index := @icons NamedSchema
             (fun ns : NamedSchema =>
              SearchUpdateTerms (schemaHeading (relSchema ns))) nschma
             (@Datatypes.nil NamedSchema) SearchUpdateTerm
             (@inil NamedSchema
                (fun ns : NamedSchema =>
                 SearchUpdateTerms (schemaHeading (relSchema ns))))
        : @ilist NamedSchema
            (fun ns : NamedSchema =>
             SearchUpdateTerms (schemaHeading (relSchema ns)))
            (@Datatypes.cons NamedSchema nschma (@Datatypes.nil NamedSchema)) in

  forall (a : IndexedEnsemble * list Tuple) (d : packet) (r_n : IndexedQueryStructure DnsSchema Index),

    (* hypothesis 1 *)
        (
    @CallBagMethod DnsSchema Index BStringId BagFind r_n
                  (None,
                   fun y : Tuple =>
                     ?[IsSuffix_dec (qname (questions d)) (@GetAttribute heading y BStringId0)])
                  ↝ a) ->

    (* hypothesis 2 *)
    forall (n' : DNSRRecord),
      List.In n' (snd a) ->

      (* conclusion *)
      IsPrefix (get_name n') (qname (questions d)).
Proof.
  intros.
  inv H.
  inv H1.
  inv H2.
  unfold BagMatchSearchTerm in H0.
  simpl in H0.
  unfold MatchIndexSearchTerm in H0.
  simpl in H0.
  
  unfold IsSuffix_dec in H0.
  unfold GetAttribute in H0.
  (* simpl in H0. *)

  apply filter_In in H0.
 (* Set Printing All. *)
  inv H0.

(* TODO fix *)
  destruct ( @IsPrefix_dec string FindSuffixSearchTerms.Astring_eq
             (@ith_Bounded Attribute string attrName attrType
                (AttrList heading) n' BStringId0) (qname (questions d))).
  apply i.
  inversion H2.
Qed.

(* -------------------------------------------------------------------------------------- *)

(* Helper lemmas for main data integrity constraint proof *)

Lemma flatmap_permutation : forall heading l1 (l2 : list (@Tuple heading)),
    In (list Tuple)
       (FlattenCompList.flatten_CompList
          (map (fun r : @Tuple heading => Return r) l2)) l1
    -> Permutation l1 l2.
Proof.
  intros. revert l1 H.
  induction l2; intros; destruct l1; intros; simpl in *; 
  try reflexivity; inv H; (inv H0; inv H1; inv H0; inv H2; inv H).
  - inv H3.
  - rewrite app_singleton. auto. 
Qed.   

Lemma flatmap_permutation' : forall heading (l : list (@Tuple heading)),
    In (list Tuple) (@FlattenCompList.flatten_CompList (@Tuple heading)
     (@map (@Tuple heading) (Comp (list (@Tuple heading)))
        (fun r : @Tuple heading => @Query_Return (@Tuple heading) r) l))
     l.
Proof.
  intros.
  induction l; simpl. Transparent ret.
  - unfold ret. apply In_singleton.
  - Transparent Bind.
    unfold Bind in *.
    unfold In in *.
    eexists.
    split.
    * unfold Query_Return in *.
      unfold ret.
      apply In_singleton.
    * exists l.
      split.
      + auto.
      + unfold ret.
        rewrite app_singleton.
        apply In_singleton.
        Opaque ret. Opaque Bind.
Qed.

Definition UnIndexedEnsembleListExists
           (ElementType : Type) (ensemble : @IndexedEnsemble ElementType) :=
  exists lIndexed : list (@IndexedElement ElementType),
    exists lElems : list ElementType,
      map indexedElement lIndexed = lElems /\
      (forall x : IndexedElement, In IndexedElement ensemble x <-> List.In x lIndexed) /\
      NoDup (map elementIndex lIndexed).

Lemma unindexed_OK_exists_index heading :
  forall S x,
    UnIndexedEnsembleListExists S ->
    (forall (l : list Tuple), (In _ (QueryResultComp (heading := heading) S (fun r => Return r)) l ->
      incl x l))
    ->
    forall t, List.In t x -> exists n, In _ S {| indexedElement := t; 
                                                elementIndex := n |}.
Proof.
  intros S x ListSetExists H t H0.
  intros.
  unfold QueryResultComp in *.

  unfold UnIndexedEnsembleListEquivalence in *.
  unfold incl in *.

  unfold UnIndexedEnsembleListExists in ListSetExists.
  inversion ListSetExists as [lIndexed]. clear ListSetExists.
  inversion H1 as [lElems]. clear H1.
  inversion H2. clear H2. inversion H3. clear H3.

  specialize (H lElems).

  assert (In (list Tuple)
        (queriedList <- {queriedList : list Tuple |
                        exists l' : list IndexedElement,
                          map indexedElement l' = queriedList /\
                          (forall x0 : IndexedElement,
                           In IndexedElement S x0 <-> List.In x0 l') /\
                          NoDup (map elementIndex l')};
         FlattenCompList.flatten_CompList
           (map (fun r : Tuple => Return r) queriedList)) lElems) as lElemsEquiv.
  {
    clear H.
    Transparent Bind. unfold Bind.
    unfold In.
    exists lElems.
    split.
    - Transparent Pick. unfold Pick.
      exists lIndexed. auto.
    - apply flatmap_permutation'.
  }

  specialize (H lElemsEquiv).
  pose proof H as x_incl_lElems. clear H.
  clear lElemsEquiv.
(* SearchAbout nth_error. *)
  (* in the context, we have
nth n x = Some t
nth n' x = Some t'

theorem about nth/map

List.In t x


 *)

  specialize (x_incl_lElems t H0). clear H0.

  pose proof in_map_iff as in_map_iff.
  subst.
  specialize (in_map_iff (@IndexedElement (@Tuple heading)) (@Tuple heading)
                         indexedElement lIndexed t).
  inversion in_map_iff as [in_exists exists_in].
  clear in_map_iff exists_in.
  specialize (in_exists x_incl_lElems).
  destruct in_exists. 
  inv H. 
  destruct x0 as [index elem].
  simpl in *.
  exists index.
  apply H2.
  auto.
Qed.

Theorem IsSuffix_string_dec : 
  forall l1 l2 : list string, IsSuffix l1 l2 \/ ~ IsSuffix l1 l2.
Proof.
  intros.
  revert l2; induction l1; intros; destruct l2.

  - left. unfold IsPrefix. exists (@nil string). reflexivity.
  - right.
    intros not.
    inversion not.
    inversion H.
  - left. unfold IsPrefix. exists (a :: l1). rewrite app_nil_l. reflexivity.
  - (* could be either *)
    (* prefix iff a0 = a and l2 is a prefix of l1 (induction hyp) *)
    pose proof (string_dec a s) as string_dec.
    (* it's a LIST OF STRINGS, not a list of characters *)
    specialize (IHl1 l2).
    destruct string_dec.
    + rewrite e.
      destruct IHl1.
      left.
      unfold IsPrefix in *.
      destruct H.
      * exists x.
        rewrite <- app_comm_cons.
        rewrite H. reflexivity.
      * unfold IsPrefix in *.
        unfold not in H.
        right.
        intros not.
        destruct not.
        inversion H0.
        apply H.
        exists x.
        auto.
    + 
      unfold not in n.
      right.
      intros not.
      unfold IsPrefix in *.
      destruct not.
      inversion H.
      apply n.
      symmetry.
      apply H1.
Qed.
 
Lemma nth_error_subset_same : forall {A : Type} (a : list A) (l : list A) t1 t2 n1 n2,
    nth_error a n1 = Some t1 ->
    nth_error a n2 = Some t2 ->
    n1 <> n2 ->
    List.incl a l ->
    (exists m1 m2,
        nth_error l m1 = Some t1 /\
        nth_error l m2 = Some t2 /\
        m1 <> m2).
Proof.
  intros.
  unfold incl in *.
  pose proof H2 as H3.
  specialize (H2 t1).
  specialize (H3 t2).

(* SearchAbout nth_error. *)
  (* TODO look at proofs of in_list_exists and exists_in_list *)

  pose proof (exists_in_list a) as exists_in_list.
  assert (List.In t1 a). { apply exists_in_list. exists n1. auto. }
  assert (List.In t2 a). { apply exists_in_list. exists n2. auto. }
  clear exists_in_list.

  pose proof (H2 H4) as t1_in_l.
  (* apply in_list_exists in t1_in_l. *)

  pose proof (H3 H5) as t2_in_l.
  (* apply in_list_exists in t2_in_l. *)

  pose proof H4 as t1_in_a. clear H4.
  pose proof H5 as t2_in_a. clear H5.

  (* t1 and t2 have to be *somewhere* in l. it's possible that, if they were the same element, that they could be both the first element, but the initial hyp says that another one has to exist somewhere...

if one is the first and the other one is elsewhere... induction? *)

  clear H2 H3.
  revert n1 n2 H H0 H1 t1_in_a t2_in_a. revert t1_in_l t2_in_l. revert a t1 t2.
  induction a as [ | a_head a_tail ]; intros.
  * inv t1_in_a.
  * simpl in *.
    destruct t1_in_a; destruct t2_in_a.
    -                           (* both are first element of a *)
      subst.
      rewrite H3 in H.

      assert (~(n1 = 0 /\ n2 = 0)) as not_both_0.
      { intros wrong.
        inv wrong. auto. }
      apply Decidable.not_and in not_both_0.
      (* Focus 2. { SearchAbout Decidable.decidable (_ = _). apply dec_eq_nat. } *)

      destruct not_both_0; destruct l; simpl in *; try omega; destruct t1_in_l; destruct t2_in_l; simpl in *; try omega.
      
      + subst.
        (* exists 0. *)
        (* simpl. unfold Specif.value. *)
        (* SearchAbout nth_error. *)
        destruct n1; try omega.
        simpl in *.
        eapply IHa_tail.
        admit.                  (* cleared *)
        admit. apply H. 
        
Admitted.        

  (*     +  *)


  (*   destruct t1_in_l; destruct t2_in_l. *)
  (*   - *)
  (*     (* both are first element of l: l_head = t1 and l_head = t2 *) *)
  (*     subst. *)
  (*     (* rewrite H3 in H. *) *)
  (*     (* pose proof H0 as H0'. *) *)
  (*     (* pose proof H as H'. *) *)
  (*     (* rewrite <- H0 in H. *) *)
  (*     (* clear H0. *) *)
  (*     (* how to do "another one has to exist"? *) *)
  (*     (*  *) *)
  (*     simpl in *. *)
  (*     + omega. *)
  (*     + simpl in *. *)
  (*       subst. *)
  (*       clear H4. *)
  (*       destruct H5. *)
  (*       { subst. *)
  (*         exists 0. *)
          
  
  

  (* revert n1 n2 H H0 H1 H2 H3. *)
  (* induction a; intros; destruct n1; destruct n2; simpl in *; try omega. *)
  (* * unfold Specif.value in *. *)
  (*   inv H. *)
  (*   admit. *)
  (* * admit. *)
  (* * admit. *)
    

  (* pose proof (H2 H4) as t1_in_l. *)
  (* apply in_list_exists in t1_in_l. *)
  (* inv t1_in_l. *)

  (* pose proof (H3 H5) as t2_in_l. *)
  (* apply in_list_exists in t2_in_l. *)
  (* inv t2_in_l. *)

  (* eexists. eexists. *)


  (* repeat split. *)
  (* - apply H6. *)
  (* - apply H7. *)
  (* - intros not. *)
  (*   (* I guess that the indices they picked for you in the new/larger list could be the same if the elements were the same. would be ok if we had a hyp that the elements weren't the same, but I don't think that's true *)
  (*    but i want that different indices *exist*. the elements might be the same, but there are at least two of them!! do I destruct list.in? *) *)
  (*   subst. *)
  (*   pose proof H as some_t1. *)
  (*   pose proof H0 as some_t2. *)
  (*   rewrite <- H7 in H0. *)
  (*   rewrite <- H6 in H. *)
  (*   rewrite <- H in H0. *)
  (*   clear H H2 H3 H4 H5 H6 H7. *)
  (*   destruct a. *)
  (*   * destruct n1; destruct n2; auto; simpl in *. *)



Lemma tuples_in_relation_satisfy_constraint_specific :
  forall (a : list Tuple) (n : packet) (r_n : QueryStructure DnsSchema),

(* TODO *)
    (* For (r in sCOLLECTIONS) *)
    (*        (Where (IsSuffix (qname (questions n)) r!sNAME) *)
    (*         Return r )  ↝ a -> *)
    let   BStringId0 := ``(sNAME) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in
@computes_to
         (list
            (@Tuple             (* heading1 *)
               (BuildHeading
                  (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                     (@Datatypes.cons Attribute
                        (Build_Attribute sTYPE RRecordType)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sCLASS RRecordClass)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTTL nat)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sDATA string)
                                 (@Datatypes.nil Attribute)))))))))
         (@Query_For
            (@Tuple
               (BuildHeading
                  (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                     (@Datatypes.cons Attribute
                        (Build_Attribute sTYPE RRecordType)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sCLASS RRecordClass)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTTL nat)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sDATA string)
                                 (@Datatypes.nil Attribute))))))))
            (@Query_In
               (@Tuple
                  (BuildHeading
                     (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sTYPE RRecordType)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sCLASS RRecordClass)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTTL nat)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sDATA string)
                                    (@Datatypes.nil Attribute))))))))
               (@Build_QueryStructureHint DnsSchema r_n)
               (@Build_BoundedIndex string
                  (@Datatypes.cons string sCOLLECTIONS
                     (@Datatypes.nil string)) sCOLLECTIONS
                  (@Build_IndexBound string sCOLLECTIONS
                     (@Datatypes.cons string sCOLLECTIONS
                        (@Datatypes.nil string)) O
                     (@eq_refl (option string) (@Some string sCOLLECTIONS))))
               (fun
                  r : @Tuple
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute))))))) =>
                @Query_Where
                  (@Tuple
                     (BuildHeading
                        (@Datatypes.cons Attribute
                           (Build_Attribute sNAME name)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTYPE RRecordType)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sCLASS RRecordClass)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sTTL nat)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sDATA string)
                                       (@Datatypes.nil Attribute))))))))
                  (@IsSuffix string (qname (questions n))
                     (@GetAttribute
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute))))))) r
                        (@Build_BoundedIndex string
                           (@Datatypes.cons string sNAME
                              (@Datatypes.cons string sTYPE
                                 (@Datatypes.cons string sCLASS
                                    (@Datatypes.cons string sTTL
                                       (@Datatypes.cons string sDATA
                                          (@Datatypes.nil string)))))) sNAME
                           (@Build_IndexBound string sNAME
                              (@Datatypes.cons string sNAME
                                 (@Datatypes.cons string sTYPE
                                    (@Datatypes.cons string sCLASS
                                       (@Datatypes.cons string sTTL
                                          (@Datatypes.cons string sDATA
                                             (@Datatypes.nil string)))))) O
                              (@eq_refl (option string) (@Some string sNAME))))))
                  (@Query_Return
                     (@Tuple
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute)))))))) r))))
         a

->
  
  forall (t t' : DNSRRecord) (n0 n' : nat),
    n0 <> n' ->
    nth_error a n0 = Some t ->
    nth_error a n' = Some t' ->
    get_name t = get_name t' ->
    t!sTYPE <> CNAME.
(* get_name vs. t!sNAME *)
Proof.
  intros.
  inversion H.
  inv H4.

assert (forall l,
In
         (list
            (@Tuple
               (BuildHeading
                  (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                     (@Datatypes.cons Attribute
                        (Build_Attribute sTYPE RRecordType)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sCLASS RRecordClass)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTTL nat)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sDATA string)
                                 (@Datatypes.nil Attribute)))))))))
         (* --- *)
         (@Query_In
            (@Tuple
               (BuildHeading
                  (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                     (@Datatypes.cons Attribute
                        (Build_Attribute sTYPE RRecordType)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sCLASS RRecordClass)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTTL nat)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sDATA string)
                                 (@Datatypes.nil Attribute))))))))
            (@Build_QueryStructureHint DnsSchema r_n)
            (@Build_BoundedIndex string
               (@Datatypes.cons string sCOLLECTIONS (@Datatypes.nil string))
               sCOLLECTIONS
               (@Build_IndexBound string sCOLLECTIONS
                  (@Datatypes.cons string sCOLLECTIONS
                     (@Datatypes.nil string)) O
                  (@eq_refl (option string) (@Some string sCOLLECTIONS))))

            (fun
               r : @Tuple
                     (* [ *) (BuildHeading
                        (@Datatypes.cons Attribute
                           (Build_Attribute sNAME name)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTYPE RRecordType)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sCLASS RRecordClass)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sTTL nat)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sDATA string)
                                       (@Datatypes.nil Attribute))))))) (* ] *) =>
               (@Query_Return
                  (@Tuple
                     (BuildHeading
                        (@Datatypes.cons Attribute
                           (Build_Attribute sNAME name)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTYPE RRecordType)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sCLASS RRecordClass)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sTTL nat)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sDATA string)
                                       (@Datatypes.nil Attribute)))))))) r)))
         l
-> List.incl x l
). {
  (* need to use the main H5 too, with the filter 
this is because x is a list of tuples that all came from r *)
  clear BStringId0.
  clear t t' n0 H0 H1 H2 H3 H n'.
  remember H5 as inFilter. clear HeqinFilter H5.
  intros l inRelation.
  inversion inFilter.
  inv H.
  (* Set Printing All. *)
  simpl in *.
  (* H0: x0 (new) is something over r_n... all queried lists (?) with the index AND the proof dropped?
         (fun queriedList => ...)
         and x0 is one of the lists in that set
     H1: x is in the set of lists from the flatmapped computation *on x0* with the filter
 *)
  Print DropQSConstraints.
  Print UnConstrQueryStructure.
  Print UnConstrRelation.       (* has indexes *)
  Check UnIndexedEnsembleListEquivalence. (* why does this return a prop *)

  inv H0.
  (* H : x0 (new) is x1 without indices, and all indices in x1 are unique, and
     forall x2 (new) : indexedelement, it's in sCOLLECTIONS if and only if it's in x1, the list of indexed elements  *)
  (* TODO *)
  Check ((DropQSConstraints r_n)!sCOLLECTIONS)%QueryImpl.
  (* complicated type with a function and functions *)

  inv H. 
  inv H2.
  remember (map elementIndex x1) as x0.
  (* introduces aux variables x1, forall x0 *)
  
  inversion inRelation.
  inversion H2. clear H2. inversion H3. clear H3.
  inversion H2. clear H2. inversion H5. clear H5.
  simpl in *.             (* TODO ltac for these inversions and reasoning about them *)
  (* introduces aux variables x2, forall x0 *)
  
  (* wait, H and H2 have List.In there (given some constraint) -- but require an indexed element *)
  Print IndexedElement.

  (* SearchAbout incl. *)
  unfold incl.
  subst. (* optional *)

  (* x3 : list IndexedElement (presumably the entries in r_n?) *)
  (* wait can i do: (modulo indices)
  (not sure what's happening in the first part here...)
List.in a0 x -> In IndexedElement a0 sCOLL -> List.In a0 x3
     /\ l is one permutation of x3 -> List.In a0 l!! *)

(* FlattenCompList.flatten_CompList *)
(*   (map (fun r : Tuple => Return r) (map indexedElement x3)) *)
(*      : Comp (list Tuple) *)
(* map *)
(*   (fun r : Tuple => Where (IsSuffix (qname (questions n)) r!sNAME) *)
(*    Return r ) *)
(*      : list Tuple -> list (Comp (list Tuple)) *)
  (* so the inner function has type Tuple -> Comp (list Tuple) *)
Check FlattenCompList.flatten_CompList.
(*      : list (Comp (list ?12195)) -> Comp (list ?12195) *)

  intros filterElem filterH.
  remember (map indexedElement x3) as x3elems.

  assert (exists feIndex,
     List.In {| elementIndex := feIndex; indexedElement := filterElem |} x1).
  { 
(* fun r : Tuple => Where (IsSuffix (qname (questions n)) r!sNAME)
Return r 
     : Tuple -> Comp (list Tuple)
     : Tuple -> Ensemble (list Tuple)  *)
    (* keep only l, x3, x1, h1, x,  *)

  remember (map indexedElement x1) as x1elems.

  (* this is the real nub of the proof *)
  assert (List.incl x x1elems).
  {
    unfold incl.
    intros xElem. intro.

    (* unfold Query_Where in H1. *)
    (* unfold Query_Return in H1. *)

    (* Transparent Pick. *)
    (* unfold Pick in H1. *)
    (* unfold FlattenCompList.flatten_CompList in H1. *)
    (* Transparent Bind. *)
    (* unfold Bind in *. *)
    (* Print Bind. *)
    (* Locate Bind. *)

    Check In_flatten_CompList.
    
    (* pose proof (In_flatten_CompList (. *)

Print FlattenCompList.boxed_option.

    (* C-c a, C-c p -- Proof General (org mode?) *)
    (* Set Printing All. auto. *)
    (* SearchAbout FlattenCompList.flatten_CompList. *)
    (* Locate computes_to. *)
    pose proof (In_flatten_CompList (fun r => IsSuffix (qname (questions n))

 (@GetAttribute
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute))))))) r
                        (@Build_BoundedIndex string
                           (@Datatypes.cons string sNAME
                              (@Datatypes.cons string sTYPE
                                 (@Datatypes.cons string sCLASS
                                    (@Datatypes.cons string sTTL
                                       (@Datatypes.cons string sDATA
                                          (@Datatypes.nil string)))))) sNAME
                           (@Build_IndexBound string sNAME
                              (@Datatypes.cons string sNAME
                                 (@Datatypes.cons string sTYPE
                                    (@Datatypes.cons string sCLASS
                                       (@Datatypes.cons string sTTL
                                          (@Datatypes.cons string sDATA
                                             (@Datatypes.nil string)))))) O
                              (@eq_refl (option string) (@Some string sNAME)))))

) ) as in_flatten.
    
    assert (forall a0 : Tuple,
                (fun r : Tuple => IsSuffix (qname (questions n))
 (@GetAttribute
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute))))))) r
                        (@Build_BoundedIndex string
                           (@Datatypes.cons string sNAME
                              (@Datatypes.cons string sTYPE
                                 (@Datatypes.cons string sCLASS
                                    (@Datatypes.cons string sTTL
                                       (@Datatypes.cons string sDATA
                                          (@Datatypes.nil string)))))) sNAME
                           (@Build_IndexBound string sNAME
                              (@Datatypes.cons string sNAME
                                 (@Datatypes.cons string sTYPE
                                    (@Datatypes.cons string sCLASS
                                       (@Datatypes.cons string sTTL
                                          (@Datatypes.cons string sDATA
                                             (@Datatypes.nil string)))))) O
                              (@eq_refl (option string) (@Some string sNAME)))))) a0 \/
                ~
                (fun r : Tuple => IsSuffix (qname (questions n))  (@GetAttribute
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute))))))) r
                        (@Build_BoundedIndex string
                           (@Datatypes.cons string sNAME
                              (@Datatypes.cons string sTYPE
                                 (@Datatypes.cons string sCLASS
                                    (@Datatypes.cons string sTTL
                                       (@Datatypes.cons string sDATA
                                          (@Datatypes.nil string)))))) sNAME
                           (@Build_IndexBound string sNAME
                              (@Datatypes.cons string sNAME
                                 (@Datatypes.cons string sTYPE
                                    (@Datatypes.cons string sCLASS
                                       (@Datatypes.cons string sTTL
                                          (@Datatypes.cons string sDATA
                                             (@Datatypes.nil string)))))) O
                            (@eq_refl (option string) (@Some string sNAME)))))) a0) as dec.
    { intros. apply IsSuffix_string_dec. }

    specialize (in_flatten dec). clear dec.
    specialize (in_flatten x1 x xElem H3).
    Transparent computes_to.
    unfold computes_to in *.
    (* tuple vs. indexedelement?? *)

    assert ((exists a' : IndexedElement,
                 List.In a' x1 /\ indexedElement a' = xElem) -> List.In xElem x1elems).
    {
    intros.

    inversion H5. clear H5.
    inversion H8. clear H8.
    rewrite <- H9.
    rewrite Heqx1elems.
    apply in_map_iff.
    eexists.
    split.
    reflexivity.
    auto. }

    apply H5. clear H5.

    (* maybe lift the list to have indices first?? *)
    (* or look at how In_flatten_CompList was proved *)
    (* it's saying, if it computes to l, any element in l is in il *)
    (* Locate In_flatten_CompList. *)
    
    (* Locate FlattenCompList.flatten_CompList. *)

    apply in_flatten.
    (* now need to manipulate H1, function on Tuple inplies function on IndexedElement *)

    rewrite Heqx1elems in H1.
    rewrite List.map_map in H1.
    unfold In in H1.
    apply H1.
  }

  unfold incl in H3.
  specialize (H3 filterElem).

  (* alternate version *)
  assert (List.In filterElem x1elems ->
          exists index, List.In {| elementIndex := index; indexedElement := filterElem |} x1). 
  {
  intros.
  rewrite Heqx1elems in H5.
  apply in_map_iff in H5.
  destruct H5.
  destruct H5.

  destruct x0.
  simpl in *.
  rewrite H5 in H8.
  exists elementIndex.
  apply H8. }

  specialize (H3 filterH).
  specialize (H5 H3).
  destruct H5 as [index].
  exists index.
  apply H5.
  }

(* note [ ret [r] ] and [ l0 = [] ]. it seems that it really is "filtering" x1elems *)

(* Print Build_BoundedIndex. *)
(* Print Build_IndexBound. *)

(* now, given List.In filterElem x and the In (filter  x1elems ...) x, 
show List.In indexedFilterElem x1.

filteredElem \in x \subset x1elems *)

(* l is a permutation of x3
x3 is sCOLLECTIONS

x1 is sCOLLECTIONS
H1: x is a subset of x1elems
x: ??? *)
    
  (* ------------------------ *)

  destruct H3 as [feIndex].                  (* new *)

  remember (Build_IndexedElement feIndex filterElem) as indexedFilterElem.
  specialize (H2 indexedFilterElem).
  specialize (H indexedFilterElem).

  inversion H. clear H.
  inversion H2. clear H2.

  specialize (H8 H3).
  specialize (H H8).

  clear H5 H8 H9.

  eapply Permutation_in.
  apply Permutation_sym.
  apply flatmap_permutation.
  apply H4.

  (* there's probably something I can do with indices to remove this step *)
  assert (List.In indexedFilterElem x3 -> List.In filterElem (map indexedElement x3)) as H5.
  { intros. 
    apply in_map_iff.
    exists indexedFilterElem.
    split.
    - rewrite HeqindexedFilterElem. reflexivity.
    - auto. }

  rewrite Heqx3elems.
  apply H5. apply H.
 }                              (* ends List.incl x l *)
(* ------------------------------------------------------------------------------------------ *)
  (* TODO: now try to use this lemma *)

(* prove that everything in x is in a and vice versa *)
(* use H6 *)
  assert (Permutation a x).
  {
    unfold In in H6.
    Transparent Pick.
    unfold Pick in *.
    Opaque Pick.
    apply Permutation_sym in H6.
    auto.
  }

(* prove that everything in a is in sCOLLECTIONS *)
  (* assert (In (list Tuple) ((r in sCOLLECTIONS) (Return r)) a). *)
  (* same problem -- subset, not exact match *)
assert (forall l,
In
         (list
            (@Tuple
               (BuildHeading
                  (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                     (@Datatypes.cons Attribute
                        (Build_Attribute sTYPE RRecordType)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sCLASS RRecordClass)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTTL nat)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sDATA string)
                                 (@Datatypes.nil Attribute)))))))))
         (* --- *)
         (@Query_In
            (@Tuple
               (BuildHeading
                  (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                     (@Datatypes.cons Attribute
                        (Build_Attribute sTYPE RRecordType)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sCLASS RRecordClass)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTTL nat)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sDATA string)
                                 (@Datatypes.nil Attribute))))))))
            (@Build_QueryStructureHint DnsSchema r_n)
            (@Build_BoundedIndex string
               (@Datatypes.cons string sCOLLECTIONS (@Datatypes.nil string))
               sCOLLECTIONS
               (@Build_IndexBound string sCOLLECTIONS
                  (@Datatypes.cons string sCOLLECTIONS
                     (@Datatypes.nil string)) O
                  (@eq_refl (option string) (@Some string sCOLLECTIONS))))

            (fun
               r : @Tuple
                     (* [ *) (BuildHeading
                        (@Datatypes.cons Attribute
                           (Build_Attribute sNAME name)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTYPE RRecordType)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sCLASS RRecordClass)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sTTL nat)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sDATA string)
                                       (@Datatypes.nil Attribute))))))) (* ] *) =>
               (@Query_Return
                  (@Tuple
                     (BuildHeading
                        (@Datatypes.cons Attribute
                           (Build_Attribute sNAME name)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTYPE RRecordType)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sCLASS RRecordClass)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sTTL nat)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sDATA string)
                                       (@Datatypes.nil Attribute)))))))) r)))
         l 
-> List.incl a l). 
  {
    (* x \subset sCOLLECTIONS, and Permutation a x *)
    intros allTuplesInRelation inRelation.

    unfold incl.
    intros aTuple inA.
    unfold incl in H4.

    clear BStringId0 H H5. clear t t' n0 n' H0 H1 H2 H3.

    specialize (H4 allTuplesInRelation inRelation aTuple).
    apply H4.
    eapply Permutation_in.
    apply H7. auto.
  } 

(* use the proof that the constraints hold on everything in sC, therefore on a *)
(* t and t' are in a, therefore the constraint must hold on them *)
  (* this is the top-level goal  *)

  assert (List.In t a).
  { apply exists_in_list. exists n0. auto. }
  assert (List.In t' a).
  { apply exists_in_list. exists n'. auto. }

  assert (List.In t x).
  { eapply Permutation_in. apply H7. auto. }
  assert (List.In t' x).
  { eapply Permutation_in. apply H7. auto. }

  clear BStringId0.
  pose proof unindexed_OK_exists_index as existsIndex.
  specialize (existsIndex (BuildHeading
                          (@Datatypes.cons Attribute
                             (Build_Attribute sNAME name)
                             (@Datatypes.cons Attribute
                                (Build_Attribute sTYPE RRecordType)
                                (@Datatypes.cons Attribute
                                   (Build_Attribute sCLASS RRecordClass)
                                   (@Datatypes.cons Attribute
                                      (Build_Attribute sTTL nat)
                                      (@Datatypes.cons Attribute
                                         (Build_Attribute sDATA string)
                                         (@Datatypes.nil Attribute)))))))).

  
  (* difference between r_n and sCOLLECTIONS?? *)
  pose ((DropQSConstraints r_n)!sCOLLECTIONS)%QueryImpl as relationSet. simpl in relationSet.
  unfold UnConstrRelation in *.
  specialize (existsIndex relationSet x). (* or a *)

  assert (UnIndexedEnsembleListExists relationSet) as relationSetListExists.
  {
    unfold UnIndexedEnsembleListExists.
    inversion H5. inv H13. inv H14. inv H13. inv H16. 
    simpl in *. pose proof H13 as iff. clear H13. (* TODO factor out *)
    exists x1 (map indexedElement x1). auto.
  }

  assert ((forall l : list Tuple,
                 In (list Tuple)
                   (QueryResultComp relationSet (fun r : Tuple => Return r))
                   l -> incl x l)) as list_subset.
  { apply H4. }                 (* :o *)
  pose proof (existsIndex relationSetListExists list_subset t) as tIndexed.
  pose proof (existsIndex relationSetListExists list_subset t') as t'Indexed.
  Check existsIndex.            (* not powerful enough? *)
  (* TODO: make existsIndex more powerful, use nth_error

   *)
  Print UnIndexedEnsembleListExists.
  specialize (tIndexed H11). specialize (t'Indexed H12).
  destruct tIndexed as [tIndex tIn].
  destruct t'Indexed as [t'Index t'In].
  clear existsIndex list_subset relationSetListExists.
  unfold DNSRRecord in *.
  remember {| elementIndex := tIndex; indexedElement := t |} as tIndexed.
  remember  {| elementIndex := t'Index; indexedElement := t' |} as t'Indexed.

  SearchAbout Relation. (* rel tup : tuple is in the relation -> pairwise constr. apply *)
  (* SearchAbout RelationSchema. *)
  (* QueryStructure DnsSchema vs. QueryStrucureSchema vs. Schema? *)
  (* QueryStructure is a data type -- multiple tables

relation is a table with tuples that obey

QSS is a type of the set of tables, or the DB type

name age (name + age) <-- schema
t    10   t10     <-- data = relation
 *)
  Print DnsSchema.
  Locate Schema.
  (* SearchAbout QueryStructureSchema. *)
  Check QSGetNRelSchema.
  Print BoundedString.
  Print BoundedIndex.

  (*   BStringId := ``(sCOLLECTIONS) : BoundedIndex [sCOLLECTIONS]
  BStringId0 := ``(sNAME) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA]
  BStringId1 := ``(sTYPE) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA]
  heading := <sNAME :: name, sTYPE :: RRecordType, 
                sCLASS :: RRecordClass, sTTL :: nat, 
                sDATA :: string>%Heading : Heading
  StringId2 := "EqualityIndex" : string
  StringId3 := "Name" : string
  BStringId2 := ``(StringId3)
             : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] *)
  
  Print QueryStructure.        (*  rels pulls out the list of tables. *)
  Locate "_ ! _".
Print GetRelation.
(* but a relation isn't a set *)
(* TODO review these poses *)
pose proof (ith_Bounded relName (rels r_n) {| bindex := sCOLLECTIONS |}) as relationthing. simpl in *.
Check ({| bindex := sCOLLECTIONS |}).
Print relName.
Check (ith_Bounded relName).
Check rels.
Check (rels r_n).

pose proof (tupleconstr (ith_Bounded relName (rels r_n) {| bindex := sCOLLECTIONS |})) as 
  constraint_in_relation_OK.
unfold indexedTuple in *. 
simpl in *.

(* TODO: missing condition that tIndexed is in the relation; that's the more general lemma *)
specialize (constraint_in_relation_OK tIndexed t'Indexed).
unfold indexedElement in *. rewrite Heqt'Indexed in *. rewrite HeqtIndexed in *. simpl in *.
apply constraint_in_relation_OK. clear constraint_in_relation_OK.

-
  unfold relationSet in tIn, t'In.
  unfold get_name in *. Print DNSRRecord. Print nth_error.

  Print UnIndexedEnsembleListEquivalence.

  (* this part of the proof is duplicated; TODO split it out *)
  inversion H5. inv H13. inv H14. inv H13. inv H16. 
  simpl in *. pose proof H13 as iff. clear H13.
  (* x1 appears here *)
  Print NoDup.
  unfold DNSRRecord in *.
  remember {| elementIndex := tIndex; indexedElement := t |} as tIndexed.
  remember  {| elementIndex := t'Index; indexedElement := t' |} as t'Indexed.
  pose proof (iff tIndexed) as iff_indexed.
  inversion iff_indexed as [iff_indexed1 iff_indexed2]. clear iff_indexed.

  pose proof (iff t'Indexed) as iff_indexed'.
  inversion iff_indexed' as [iff_indexed1' iff_indexed2']. clear iff_indexed'.

  (* which direction should I use? *)
  specialize (iff_indexed1 tIn).
  specialize (iff_indexed1' t'In).
  clear iff_indexed2 iff_indexed2' relationthing.

pose proof H8 as a_incl_relation. clear H8.
specialize (a_incl_relation (map indexedElement x1)).
(* assert (In (list Tuple) (r in sCOLLECTIONS) (Return r)  (map indexedElement x1)). *)
assert (In
                      (list
                         (@Tuple
                            (BuildHeading
                               (@Datatypes.cons Attribute
                                  (Build_Attribute sNAME name)
                                  (@Datatypes.cons Attribute
                                     (Build_Attribute sTYPE RRecordType)
                                     (@Datatypes.cons Attribute
                                        (Build_Attribute sCLASS RRecordClass)
                                        (@Datatypes.cons Attribute
                                           (Build_Attribute sTTL nat)
                                           (@Datatypes.cons Attribute
                                              (Build_Attribute sDATA string)
                                              (@Datatypes.nil Attribute)))))))))
                      (@Query_In
                         (@Tuple
                            (BuildHeading
                               (@Datatypes.cons Attribute
                                  (Build_Attribute sNAME name)
                                  (@Datatypes.cons Attribute
                                     (Build_Attribute sTYPE RRecordType)
                                     (@Datatypes.cons Attribute
                                        (Build_Attribute sCLASS RRecordClass)
                                        (@Datatypes.cons Attribute
                                           (Build_Attribute sTTL nat)
                                           (@Datatypes.cons Attribute
                                              (Build_Attribute sDATA string)
                                              (@Datatypes.nil Attribute))))))))
                         (@Build_QueryStructureHint DnsSchema r_n)
                         (@Build_BoundedIndex string
                            (@Datatypes.cons string sCOLLECTIONS
                               (@Datatypes.nil string)) sCOLLECTIONS
                            (@Build_IndexBound string sCOLLECTIONS
                               (@Datatypes.cons string sCOLLECTIONS
                                  (@Datatypes.nil string)) O
                               (@eq_refl (option string)
                                  (@Some string sCOLLECTIONS))))
                         (fun
                            r : @Tuple
                                  (BuildHeading
                                     (@Datatypes.cons Attribute
                                        (Build_Attribute sNAME name)
                                        (@Datatypes.cons Attribute
                                           (Build_Attribute sTYPE RRecordType)
                                           (@Datatypes.cons Attribute
                                              (Build_Attribute sCLASS
                                                 RRecordClass)
                                              (@Datatypes.cons Attribute
                                                 (Build_Attribute sTTL nat)
                                                 (@Datatypes.cons Attribute
                                                  (Build_Attribute sDATA
                                                  string)
                                                  (@Datatypes.nil Attribute))))))) =>
                          @Query_Return
                            (@Tuple
                               (BuildHeading
                                  (@Datatypes.cons Attribute
                                     (Build_Attribute sNAME name)
                                     (@Datatypes.cons Attribute
                                        (Build_Attribute sTYPE RRecordType)
                                        (@Datatypes.cons Attribute
                                           (Build_Attribute sCLASS
                                              RRecordClass)
                                           (@Datatypes.cons Attribute
                                              (Build_Attribute sTTL nat)
                                              (@Datatypes.cons Attribute
                                                 (Build_Attribute sDATA
                                                  string)
                                                 (@Datatypes.nil Attribute))))))))
                            r))
                      (@map
                         (@IndexedElement
                            (@Tuple
                               (BuildHeading
                                  (@Datatypes.cons Attribute
                                     (Build_Attribute sNAME name)
                                     (@Datatypes.cons Attribute
                                        (Build_Attribute sTYPE RRecordType)
                                        (@Datatypes.cons Attribute
                                           (Build_Attribute sCLASS
                                              RRecordClass)
                                           (@Datatypes.cons Attribute
                                              (Build_Attribute sTTL nat)
                                              (@Datatypes.cons Attribute
                                                 (Build_Attribute sDATA
                                                  string)
                                                 (@Datatypes.nil Attribute)))))))))
                         (@Tuple
                            (BuildHeading
                               (@Datatypes.cons Attribute
                                  (Build_Attribute sNAME name)
                                  (@Datatypes.cons Attribute
                                     (Build_Attribute sTYPE RRecordType)
                                     (@Datatypes.cons Attribute
                                        (Build_Attribute sCLASS RRecordClass)
                                        (@Datatypes.cons Attribute
                                           (Build_Attribute sTTL nat)
                                           (@Datatypes.cons Attribute
                                              (Build_Attribute sDATA string)
                                              (@Datatypes.nil Attribute))))))))
                         (@indexedElement
                            (@Tuple
                               (BuildHeading
                                  (@Datatypes.cons Attribute
                                     (Build_Attribute sNAME name)
                                     (@Datatypes.cons Attribute
                                        (Build_Attribute sTYPE RRecordType)
                                        (@Datatypes.cons Attribute
                                           (Build_Attribute sCLASS
                                              RRecordClass)
                                           (@Datatypes.cons Attribute
                                              (Build_Attribute sTTL nat)
                                              (@Datatypes.cons Attribute
                                                 (Build_Attribute sDATA
                                                  string)
                                                 (@Datatypes.nil Attribute)))))))))
                         x1)) as a_incl_relation'.
{ admit. }

specialize (a_incl_relation a_incl_relation').

  (* to satisfy constraint_in_relation OK:

Given:

indices  i   j  k  l  m...
elements ti tj tk tl tm...

NoDup (map elementIndex x1)
List.In tIndex (map elementIndex x1)
 List.In t'Index (map elementIndex x1)

  /\
List.In tIndexed x1
List.In t'Indexed x1 (x1 ~ relation's list)

  /\ (it would help if we had tIndexed <> t'Indexed or t <> t'?)
(nth_error a n0 = Some t
nth_error a n' = Some t'
n0 <> n'
[a] \subset (map indexedElement x1)) --> would like to use to prove that
  (problem: map elementIndex vs indexedElement)
  exists m' m0,
  nth_error x1 m0 = Some tIndexed
  nth_error x1 m' = Some t'Indexed 
  m0 <> m' -->
  nth_error (map elementIndex x1) m0 = Some tIndex
  nth_error (map elementIndex x1) m' = Some t'Index
  m0 <> m' -->
  + NoDup map (elementIndex x1) -->
  tIndex <> t'Index

not sure if strong enough; still possible that
tIndexed = t'Indexed, even with the [a] hypothesis
maybe I cleared a hypothesis that I shouldn't have?

---

pick two elements of x1
(if they're not the same element, indices are different)

say worst case they are the same element:
(i, ti) and (i, ti)

can that be possible?
a could contain two instances of ti and ti
so... yes?

-----



-----


Want to prove: tIndex <> t'Index 

Proof:

(It's not sufficient to have 
List.In tIndex x1indices
List.In t'Index x1indices
because they might be at the same position.)
(Should I backtrack? maybe I can prove that their indices aren't equal in the earlier proof?) *)

(* no duplicates in x1 *)

(* TODO: clean this up so I don't do it twice *)
  pose proof (in_map_iff  (@elementIndex
                (@Tuple
                   (BuildHeading
                      (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                         (@Datatypes.cons Attribute
                            (Build_Attribute sTYPE RRecordType)
                            (@Datatypes.cons Attribute
                               (Build_Attribute sCLASS RRecordClass)
                               (@Datatypes.cons Attribute
                                  (Build_Attribute sTTL nat)
                                  (@Datatypes.cons Attribute
                                     (Build_Attribute sDATA string)
                                     (@Datatypes.nil Attribute)))))))))) x1 as in_map_iff.

  pose proof (in_map_iff tIndex) as in_map_tIndex.
  pose proof (in_map_iff t'Index) as in_map_t'Index.
  clear in_map_iff.
  inversion in_map_tIndex as [in_t1 in_t2]. inversion in_map_t'Index as [in_t'1 in_t'2].
  clear in_t1 in_t'1 in_map_tIndex in_map_t'Index.
  
  assert (exists x0 : IndexedElement,
             elementIndex x0 = tIndex /\ List.In x0 x1) as prem1.
  { exists tIndexed. rewrite HeqtIndexed at 1. simpl. auto. }

  assert (exists x0 : IndexedElement,
             elementIndex x0 = t'Index /\ List.In x0 x1) as prem2.
  { exists t'Indexed. rewrite Heqt'Indexed at 1. simpl. auto. }
  
  specialize (in_t2 prem1). specialize (in_t'2 prem2). clear prem1 prem2.

  Check nth_error_subset_same.
  
  clear H H5 H6 H4 iff_indexed1 iff_indexed1' a_incl_relation a_incl_relation'.

  remember (map elementIndex x1) as x1indices. 
  induction H14.                (* NoDup -- TODO should I revert? *)
  * inversion in_t2.
  *
    Print NoDup.
    simpl in *.
    destruct in_t2; destruct in_t'2.
    + admit.                    (* indices are same element (head) *)
    +                           (* ind hyp not right *)
      admit.
    +
      admit.
    +
      admit.
      


(* this is really one big admit *)
  (* admit. *)

-
  (* I also cleared the results of the inversions... getting them back here *)
  clear relationthing constraint_in_relation_OK.
  inversion H5. inv H13. inv H14. inv H13. inv H16. 
  simpl in *.

  pose proof H13 as iff. clear H13.
  (* unfold DropQSConstraints in *. *)
  (* show that t is in the relation *)
SearchAbout rel.
Check GetRelDropConstraints.
  pose proof GetRelDropConstraints as getRelDrop.
  Print BoundedString.
  Print BoundedIndex.
  specialize (getRelDrop DnsSchema r_n {| bindex := sCOLLECTIONS |}).
  simpl in *.
  
  unfold DNSRRecord in *.
  remember {| elementIndex := tIndex; indexedElement := t |} as tIndexed.
  remember  {| elementIndex := t'Index; indexedElement := t' |} as t'Indexed.

  Check (rel (ilist_hd (rels r_n)) tIndexed). (* Prop *)
  Check (GetRelation r_n ``(sCOLLECTIONS)).   (* IndexedEnsemble *)
  Check rel.
  Check (rel (ilist_hd (rels r_n))). (* IndexedEnsemble*)
  Check (rel (ilist_hd (rels r_n)) tIndexed).

  unfold GetRelation in *.
  simpl in *.
  rewrite <- getRelDrop. 
  pose proof (iff tIndexed) as iff_indexed.
  inversion iff_indexed as [iff_indexed1 iff_indexed2]. clear iff_indexed.
  unfold In in iff_indexed2.
  (* apply iff_indexed2. *)
  (* Thus, since t is in a, then it is in x, so it's in x1, so there's an index such that tIndexed in x2. *)
  (* TODO clear some stuff, also I may have inverted the wrong one? *)

  clear iff_indexed1 iff_indexed2. 

  (* now, show that t is (in?) x1 *)
  (* how to use H4 + H17? *)
  remember (map indexedElement x1) as x1elems.
  unfold relationSet in *.
  unfold In in tIn.
  auto.

  (* t'Index can be any index, so I don't think this is true. unless I use the indexed lemma again? doesn't it give me this in the form of tIn, t'In? *)

  (* pose proof (H4 x1elems). *)

  (* unfold incl in *. *)
  (* should i be using inrel_listin? did I just use that? *)
  (* rewrite Heqx1elems in H15. *)
  
  (* is the premise of H15 even true? might need to un-specialize inrel_listin and listin_inrel *)
  (* how do i prove that x1 is a permutation of scollections. should be able to use that <->, but it applies to indiv elements *)
  (* extend H15: -> exists index, List.in tIndexed x1 *)
  (* apply in_map_iff in H15. *)
   
  
  (* note that r := ilist_hd (rels r_n) : Relation {| schemaHeading... constraints... |} *)
  (* how is that done? with the fact thtat nth_error a n0 = Some t, and a <-> x \subset sCOLLECTIONS?
   sounds convoluted *)

-
  (* same as above -- split above thing into lemma and use it *)
  
  admit.

-
  unfold get_name in H3.
  unfold DNSRRecord in *.
  auto.
Qed.

(* -------------------------------------------------------------------------------------- *)

(* TODO: more general lemmas (hard to state w/ implicits; do later) *)
(*
  [for?] ((x in R) return x ~> l) ->
  forall n0 n1, nth n0 l = tup0 -> nth n0 l = tup1 ->
  tuple_constr tup0 tup1 *)

Lemma tuples_in_relation_satisfy_constraint :
    True.
Proof.

Admitted.

(* general lemma to prove, #2: deal with [where]
  (since [where] is just filtering/taking a subset, it should
  preserve the constraint/relation stuff)
  ([for?] (x in R)
      [WHERE (P x)]
  return x ~> l) ->
  forall n0 n1, nth n0 l = tup0 -> nth n0 l = tup1 ->
  tuple_constr tup0 tup1 *)

Lemma tuples_in_relation_filtered_satisfy_constraint :
  True.
Proof.

Admitted.

(* -------------------------------------------------------------------------------------- *)

(* TODO: working on this code; please excuse the comments *)

Print MostlySharpened.

Theorem DnsManual :
  MostlySharpened DnsSpec.
Proof.

  (* the two components here (start honing + GenerateIndexesForAll) are manual versions of
     partial_master_plan' in AutoDB *)

  unfold DnsSpec.

start sharpening ADT. {
  hone method "Process". {
    simplify with monad laws.
    (* Find the upperbound of the results. *)
    etransitivity.
    apply refine_under_bind; intros. (* rewrite? *)
    (* rewrite map_app, map_map, app_nil_r, map_id; simpl. *)
    etransitivity.
    apply refine_bind.
    match goal with
      |- refine _ (?H) => let id := fresh in set (id := H) in *
    end. (* rename ?whatever to H(number) *)
    (* Should honing if branches also be their own tactic? *)
    etransitivity.
    apply refine_If_Then_Else.
    match goal with
      |- context [ [[r in ?A | upperbound ?f ?l r]] ] =>
      pose (@refine_find_upperbound _ f A)
    end.
    etransitivity.
    { apply refine_bind; eauto.
      intro; higher_order_reflexivity. }

    setoid_rewrite (@refine_decides_forall_In' _ _ _ _).
    simplify with monad laws.
    etransitivity.
    Check refine_bind.
    (* implement decision procedure *)
    { 
      apply refine_bind;
      [ apply refine_check_one_longest_prefix_s
      | intro; higher_order_reflexivity ].
      intros. clear H. clear H1. unfold get_name. 
      eapply For_computes_to_In in H0.
      inv H0.
      - apply H.
      - pose proof IsSuffix_string_dec. intros. auto.
      - auto.
    }
    simplify with monad laws.
    setoid_rewrite refine_if_If.
    apply refine_If_Then_Else.
    etransitivity.
    { (* Locate "unique". *)
      
      (* setoid_rewrite refine_check_one_longest_prefix_CNAME. *)
      (* simplify with monad laws. *)
      (* reflexivity. *)
      
      apply refine_bind;        (* rewrite instead of apply *)
      [ eapply refine_check_one_longest_prefix_CNAME | intro; higher_order_reflexivity ].

      inversion H0.
      inversion H2. clear H2.
      - eapply tuples_in_relation_satisfy_constraint_specific.
        Check refine_check_one_longest_prefix_CNAME. apply H0.
      (* exciting! *)
      -                        
        clear H.
        intros.
        instantiate (1 := (qname (questions n))). 
        eapply For_computes_to_In in H0.
        inv H0. unfold IsSuffix in *. unfold get_name.
      + apply H2.
      + pose proof IsSuffix_string_dec. intros. auto.
      + auto.
    }
    simplify with monad laws.
    reflexivity. reflexivity.
    
    reflexivity. subst H1; reflexivity.
    unfold pointwise_relation; intros; higher_order_reflexivity.
    finish honing. finish honing.
}

  start_honing_QueryStructure'.

  hone method "AddData".
  {
    (* AddData has been expanded in method StringId0 *)
    (* refine (AddData body) (H r_n n) <-- what is that? *)
    (* H := existential variable of the correct (?) type,
       r_n : UnConstrQueryStructure DnsSchema, n : DNSRRecord*)
    (* x1 = check constraint between n (the record) and every other tuple  *)
    (* x2 = check constraint between every other tuple and n (the record) *)
    (* doesn't know that the constraint is symmetric? *)

    (* one-liner with rewrites? *)
    subst_all.
    match goal with
      |- refine _ (?H _ _) => let id := fresh in set (id := H) in *
    end.                        (* replace ex var with name H again *)
    setoid_rewrite refine_count_constraint_broken.        (* refine x1 *)
    setoid_rewrite refine_count_constraint_broken'.        (* refine x2 *)
    Check refine_If_Then_Else_Bind.
    Check Bind_refine_If_Then_Else.
    setoid_rewrite refine_If_Then_Else_Bind.
    setoid_rewrite Bind_refine_If_Then_Else.
    etransitivity.
    Check refine_If_Then_Else.
    apply refine_If_Then_Else.
    - simplify with monad laws.
      apply refine_under_bind; intros. (* x0 disappears? *)
      Check refine_Count.
      setoid_rewrite refine_Count; simplify with monad laws.
      apply refine_under_bind; intros.
      (* remove duplicate check *)
      (* (simplifies x1) *)
      setoid_rewrite refine_subcheck_to_filter; eauto.
      simplify with monad laws.
      rewrite clear_nested_if by apply filter_nil_is_nil.
      (* removes one of the repeated rets, and the filter dec -- how? *)
      higher_order_1_reflexivity. (* ? where did the next goal come from? *)
      eauto with typeclass_instances.
    - simplify with monad laws.
      reflexivity.              (* refine (code) (existential variable) is cleared by reflexivity *)
    - finish honing.            (* can finish honing anywhere? *)
  }
  (* higher level of reasoning *)

  GenerateIndexesForAll         (* ? in IndexSelection, see GenerateIndexesFor *)
  (* specifies that you want to use the suffix index structure TODO *)
  ltac:(CombineCase2 matchFindSuffixIndex matchEqIndex)
         ltac:(fun attrlist => make simple indexes using attrlist).
  (* SearchTerm and SearchUpdateTerm: efficiently do quality test on the name columns *)
  (* it figures out what data structure to use *)
  (* BagMatchSearchTerm *)
  (* implement query as calls to abstract bag find function *)
  (* then plug in data structures that impl bag find (chooses b/t them?) *)

  (* hone constructor "Init". *)
  { 
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    finish honing.
   }

    (* hone method "AddData". *) {
    etransitivity.
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    - apply refine_If_Then_Else.
      + simplify with monad laws.
        implement_Query
          ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
                 ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                        ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                               ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                        ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                        ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep).
        simplify with monad laws.
        rewrite (@refineEquiv_swap_bind nat).
        setoid_rewrite refine_if_If.
        implement_Insert_branches.
        reflexivity.
      + simplify with monad laws.
        implement_Query
          ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
                 ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                        ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                               ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                                      ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                                             ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep).
        simplify with monad laws.
        rewrite (@refineEquiv_swap_bind nat).
        setoid_rewrite refine_if_If.
        implement_Insert_branches.
        reflexivity.
    - reflexivity.
    - finish honing.
    }

  (* hone method "Process". *) {
    simplify with monad laws.
    implement_Query             (* in AutoDB, implement_Query' has steps *)
      ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                    ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                           ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                                  ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                                         ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep).
    simplify with monad laws.
    simpl.
    setoid_rewrite (refine_pick_val _ H).
    simplify with monad laws.
    setoid_rewrite (@refine_filtered_list _ _ _ _).
    finish honing.
  }
  
  FullySharpenQueryStructure' DnsSchema Index.
  (* implement_bag_methods needs to be patched for this goal. *)

  - implement_bag_methods.
  - implement_bag_methods.
Time Defined.

    Definition DnsDelegateReps
    : ilist (fun ns => Type) (qschemaSchemas DnsSchema).
      simpl; econstructor; [ | econstructor ].
      exact (list (@Tuple
           <sNAME :: name, sTYPE :: RRecordType, sCLASS :: RRecordClass,
              sTTL :: nat, sDATA :: string>%Heading)).
    Defined.

    Definition DnsDelegateSearchUpdateTerms
    : ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
             (qschemaSchemas DnsSchema).
      simpl; econstructor; [ | econstructor ].
      exact  DnsSearchUpdateTerm.
    Defined.



    Definition DnsDelegateImpls
    : i2list2 (fun ns (SearchTerm : SearchUpdateTerms (schemaHeading (relSchema ns)))
                   (Rep : Type) =>
                 ComputationalADT.pcADT
                   (BagSig (@Tuple (schemaHeading (relSchema ns)))
                           (BagSearchTermType SearchTerm)
                           (BagUpdateTermType SearchTerm))
                   Rep)
              DnsDelegateSearchUpdateTerms
              DnsDelegateReps.
      simpl; econstructor; [ | econstructor ].
      let p := eval simpl in (projT2 (BagADTImpl (fun _ => true)
                         (@ListAsBag
                            _
                            (BagSearchTermType DnsSearchUpdateTerm)
                            (BagUpdateTermType DnsSearchUpdateTerm)
                            {| pst_name := nil;
                               pst_filter := fun _ => true |}
                            (BagMatchSearchTerm DnsSearchUpdateTerm)
                            (BagApplyUpdateTerm DnsSearchUpdateTerm) ))) in
          exact p.
    Defined.

    Definition DnsImpl : SharpenedUnderDelegates DnsSig.
      Time let
          Impl := eval simpl in (projT1 DnsManual) in exact Impl.
    Defined.

    Print DnsImpl.
    Definition ExtractWorthyDNSImpl : ComputationalADT.cADT DnsSig.
      let s := eval unfold DnsImpl in DnsImpl in
          let Impl := eval simpl in
          (Sharpened_Implementation s
                                    (LookupQSDelegateReps DnsDelegateReps)
                                    (LookupQSDelegateImpls DnsDelegateImpls)) in exact Impl.
    Defined.

    Print ExtractWorthyDNSImpl.

    Extraction "bar.ml" ExtractWorthyDNSImpl.
