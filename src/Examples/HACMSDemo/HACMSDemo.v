Require Import Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Structures.OrderedType.

Require Import
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.StringOpt
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt.

Require Import
        Fiat.Common.SumType
        Fiat.Examples.Tutorial.Tutorial
        Fiat.Examples.DnsServer.DecomposeEnumField
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.Examples.HACMSDemo.DuplicateFree
        Fiat.QueryStructure.Automation.MasterPlan.

Require Import
        Bedrock.Word
        Bedrock.Memory.

Lemma exists_CompletelyUnConstrFreshIdx:
  forall (qs_schema : RawQueryStructureSchema)
    (BagIndexKeys : ilist3 (qschemaSchemas qs_schema))
    (r_o : UnConstrQueryStructure qs_schema)
    (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
  DelegateToBag_AbsR r_o r_n ->
  exists bnd : nat,
  forall idx : Fin.t (numRawQSschemaSchemas qs_schema),
    UnConstrFreshIdx (GetUnConstrRelation r_o idx) bnd.
Proof.
  intros.
  generalize (exists_UnConstrFreshIdx H); clear H.
  remember (GetUnConstrRelation r_o); clear.
  destruct qs_schema; simpl in *.
  clear qschemaConstraints.
  induction numRawQSschemaSchemas; simpl in *; intros.
  - exists 0; intros; inversion idx.
  - revert i IHnumRawQSschemaSchemas H.
    pattern numRawQSschemaSchemas, qschemaSchemas;
      apply Vector.caseS; simpl; intros.
    destruct (IHnumRawQSschemaSchemas
                t
                (fun idx => i (Fin.FS idx))
                (fun idx => H (Fin.FS idx))
             ).
    destruct (H Fin.F1).
    exists (max x x0).
    unfold UnConstrFreshIdx in *; simpl in *; intros.
    pose proof (Max.le_max_l x x0);
      pose proof (Max.le_max_r x x0).
    generalize dependent idx; intro; generalize t i x x0 H0 H1 H3 H4;
      clear; pattern n, idx; apply Fin.caseS; simpl; intros.
    apply H1 in H2; omega.
    apply H0 in H2; omega.
Qed.

Lemma refine_Pick_CompletelyUnConstrFreshIdx
  : forall (qs_schema : RawQueryStructureSchema)
    (BagIndexKeys : ilist3 (qschemaSchemas qs_schema))
    (r_o : UnConstrQueryStructure qs_schema)
    (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
    DelegateToBag_AbsR r_o r_n ->
    forall (bnd : nat),
      (forall (idx : Fin.t (numRawQSschemaSchemas qs_schema)),
          UnConstrFreshIdx (GetUnConstrRelation r_o idx) bnd) ->
      refine {bnd0 : nat | forall idx, UnConstrFreshIdx (GetUnConstrRelation r_o idx) bnd0} (ret bnd).
Proof.
  intros; refine pick val _; eauto.
  reflexivity.
Qed.

Instance Query_eq_word32 : Query_eq (word 32) :=
  {| A_eq_dec := @weq 32 |}.

Global Instance GetAttributeRawTermCounter' {A : Type} {qsSchema}
         {Ridx : Fin.t _}
         {tup : @RawTuple (Vector.nth _ Ridx)}
         {BAidx : _ }
         a
    : (TermAttributeCounter qsSchema (@GetAttributeRaw {| NumAttr := S _;
                                                          AttrList := Vector.cons _ A _ _ |} {|prim_fst := a; prim_snd := tup |} (Fin.FS BAidx)) Ridx BAidx) | 0 := Build_TermAttributeCounter qsSchema _ Ridx BAidx.

Ltac GetAttributeRawTermCounterTac t ::=
     lazymatch goal with
       _ =>
       match goal with
         |- TermAttributeCounter
              ?qs_schema
              (GetAttributeRaw {| prim_fst := ?a;
                             prim_snd := ?tup |} (Fin.FS ?BAidx))
         _ _ =>
    match type of tup with
    | @RawTuple (@GetNRelSchemaHeading _ _ ?Ridx) =>
      apply (@GetAttributeRawTermCounter' _ qs_schema Ridx tup _ a)
    end
    end
  end.

Lemma refineEquiv_Query_Where_And
      {ResultT}
  : forall P P' bod,
    (P \/ ~ P)
    -> refineEquiv (@Query_Where ResultT (P /\ P') bod)
                (Query_Where P (Query_Where P' bod)).
Proof.
  split; unfold refine, Query_Where; intros;
    computes_to_inv; computes_to_econstructor;
      intuition.
  - computes_to_inv; intuition.
  - computes_to_inv; intuition.
  - computes_to_econstructor; intuition.
Qed.

Corollary refineEquiv_For_Query_Where_And
          {ResultT}
          {qs_schema}
  : forall (r : UnConstrQueryStructure qs_schema) idx P P' bod,
    (forall tup, P tup \/ ~ P tup)
    -> refine (For (UnConstrQuery_In
                      r idx
                      (fun tup => @Query_Where ResultT (P tup /\ P' tup) (bod tup))))
              (For (UnConstrQuery_In
                      r idx
                      (fun tup => Where (P tup) (Where (P' tup) (bod tup))))).
Proof.
  intros; apply refine_refine_For_Proper.
  apply refine_UnConstrQuery_In_Proper.
  intro; apply refineEquiv_Query_Where_And; eauto.
Qed.

Lemma refine_If_IfOpt {A B}
  : forall (a_opt : option A) (t e : Comp B),
    refine (If_Then_Else (If_Opt_Then_Else a_opt (fun _ => false) true)
                         t e)
           (If_Opt_Then_Else a_opt (fun _ => e) t).
Proof.
  destruct a_opt; simpl; intros; reflexivity.
Qed.

Global Arguments icons2 _ _ _ _ _ _ _ / .
Global Arguments GetAttributeRaw {heading} !tup !attr .
Global Arguments ilist2_tl _ _ _ _ !il / .
Global Arguments ilist2_hd _ _ _ _ !il / .

Global Opaque If_Opt_Then_Else.
Ltac implement_DecomposeRawQueryStructure :=
  first [ simplify with monad laws; simpl
        | rewrite refine_If_IfOpt
        | match goal with
            |- refine (b <- If_Opt_Then_Else _ _ _; _) _ =>
            etransitivity;
            [ apply refine_If_Opt_Then_Else_Bind
            | simpl; eapply refine_If_Opt_Then_Else_trans;
              intros; set_refine_evar ]
          end
        | match goal with
            H0 : DecomposeRawQueryStructureSchema_AbsR' _ _ _ _ ?r_o ?r_n |- refine _ ?H => unfold H;
                                                                                            apply (refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv H0 Fin.F1)
          end
        | match goal with
            H0 : DecomposeRawQueryStructureSchema_AbsR' (qs_schema := ?qs_schema) _ _ _ _ ?r_o ?r_n |- refine (Query_For _ ) _ =>
            rewrite (refineEquiv_For_Query_Where_And r_o Fin.F1); eauto
          end
        |
        match goal with
          H0 : DecomposeRawQueryStructureSchema_AbsR' (qs_schema := ?qs_schema) _ _ _ _ ?r_o ?r_n |- refine (Query_For _ ) _ =>
          rewrite (@refine_QueryIn_Where _ qs_schema Fin.F1 _ _ _ _ _ H0 _ _ _ );
          unfold Tuple_DecomposeRawQueryStructure_inj; simpl
        end
        | match goal with
            H0 : DecomposeRawQueryStructureSchema_AbsR' _ _ _ _ ?r_o ?r_n
            |- refine { r_n | DecomposeRawQueryStructureSchema_AbsR' _ _ _ _ _ r_n} _ =>
            first [refine pick val _; [ | eassumption ]
                  | refine pick val _;
                    [ | apply (DecomposeRawQueryStructureSchema_Insert_AbsR_eq H0) ] ]
          end
        ].

Ltac implement_DecomposeRawQueryStructure' H :=
  first [
      simplify with monad laws; simpl
    | rewrite H
    | apply refine_pick_eq'
    | etransitivity;
      [ apply refine_If_Opt_Then_Else_Bind
      | simpl; eapply refine_If_Opt_Then_Else_trans;
        intros; set_refine_evar ] ].

  Lemma GetAttributeRaw_FS
    : forall {A} {heading} (a : A) (tup : @RawTuple heading) n,
      @GetAttributeRaw {| AttrList := Vector.cons _ A _ (AttrList heading) |}
                       {| prim_fst := a; prim_snd := tup |} (Fin.FS n)
    = GetAttributeRaw tup n.
  Proof.
    unfold GetAttributeRaw; simpl; reflexivity.
  Qed.

    Lemma GetAttributeRaw_F1
    : forall {A} {heading} (a : A) (tup : @RawTuple heading),
      @GetAttributeRaw {| AttrList := Vector.cons _ A _ (AttrList heading) |}
                       {| prim_fst := a; prim_snd := tup |} Fin.F1
    = a.
  Proof.
    unfold GetAttributeRaw; simpl; reflexivity.
  Qed.

  Module word_as_OT <: OrderedType.
    Definition t := word 32.
    Definition eq (c1 c2 : t) := c1 = c2.
    Definition lt (c1 c2 : t) := wlt c1 c2.

    Definition eq_dec : forall l l', {eq l l'} + {~eq l l'} := @weq 32 .

    Lemma eq_refl : forall x, eq x x.
    Proof. reflexivity. Qed.

    Lemma eq_sym : forall x y, eq x y -> eq y x.
    Proof. intros. symmetry. eauto. Qed.

    Lemma eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
    Proof. intros. unfold eq in *. rewrite H. rewrite H0. eauto. Qed.

    Lemma lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
    Proof. intros. unfold lt in *. eapply N.lt_trans; eauto. Qed.

    Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
    Proof.
      intros. unfold eq, lt, wlt in *. intro.
      rewrite <- N.compare_lt_iff in H.
      subst; rewrite N.compare_refl in H; discriminate.
    Qed.

    Lemma compare : forall x y, Compare lt eq x y.
    Proof.
      intros. unfold lt, eq, wlt.
      destruct (N.compare (wordToN x) (wordToN y)) eqn: eq.
      - eapply EQ. apply N.compare_eq_iff in eq; apply wordToN_inj; eauto.
      - eapply LT. abstract (rewrite <- N.compare_lt_iff; eauto).
      - eapply GT. abstract (rewrite <- N.compare_gt_iff; eauto).
    Defined.
End word_as_OT.

Module wordIndexedMap := FMapAVL.Make word_as_OT.

Module wordTreeBag := TreeBag wordIndexedMap.

Ltac BuildQSIndexedBag heading AttrList BuildEarlyBag BuildLastBag k ::=
  lazymatch AttrList with
  | (?Attr :: [ ])%list =>
    let AttrKind := eval simpl in (KindIndexKind Attr) in
        let AttrIndex := eval simpl in (KindIndexIndex Attr) in
            let is_equality := eval compute in (string_dec AttrKind "EqualityIndex") in

                lazymatch is_equality with
                | left _ =>
                  let AttrType := eval compute in (Domain heading AttrIndex) in
                      lazymatch AttrType with
                      | BinNums.N =>
                        k (@NTreeBag.IndexedBagAsCorrectBag
                             _ _ _ _ _ _ _
                             (@CountingListAsCorrectBag
                                (@RawTuple heading)
                                (IndexedTreeUpdateTermType heading)
                                (IndexedTreebupdate_transform heading))
                             (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                          )
                      | word 32 =>
                        k (@wordTreeBag.IndexedBagAsCorrectBag
                             _ _ _ _ _ _ _
                             (@CountingListAsCorrectBag
                                (@RawTuple heading)
                                (IndexedTreeUpdateTermType heading)
                                (IndexedTreebupdate_transform heading))
                             (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                          )

                      | BinNums.Z =>
                        k (@ZTreeBag.IndexedBagAsCorrectBag
                             _ _ _ _ _ _ _
                             (@CountingListAsCorrectBag
                                (@RawTuple heading)
                                (IndexedTreeUpdateTermType heading)
                                (IndexedTreebupdate_transform heading))
                             (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                          )
                      | nat =>
                        k (@NatTreeBag.IndexedBagAsCorrectBag
                             _ _ _ _ _ _ _
                             (@CountingListAsCorrectBag
                                (@RawTuple heading)
                                (IndexedTreeUpdateTermType heading)
                                (IndexedTreebupdate_transform heading))
                             (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                          )
                      | string =>
                        k (@StringTreeBag.IndexedBagAsCorrectBag
                             _ _ _ _ _ _ _
                             (@CountingListAsCorrectBag
                                (@RawTuple heading)
                                (IndexedTreeUpdateTermType heading)
                                (IndexedTreebupdate_transform heading))
                             (fun x => GetAttributeRaw (heading := heading) x AttrIndex)
                          )
                      end
                | right _ =>
                  BuildLastBag heading AttrList AttrKind AttrIndex k
                end
  | (?Attr :: ?AttrList')%list =>
    let AttrKind := eval simpl in (KindIndexKind Attr) in
        let AttrIndex := eval simpl in (KindIndexIndex Attr) in
            let is_equality := eval compute in (string_dec AttrKind "EqualityIndex") in
                lazymatch is_equality with
                | left _ =>
                  let AttrType := eval compute in (Domain heading AttrIndex) in
                      lazymatch AttrType with
                      | BinNums.N =>
                        BuildQSIndexedBag
                          heading AttrList'
                          BuildEarlyBag BuildLastBag
                          ltac:(fun subtree =>
                                  k (@NTreeBag.IndexedBagAsCorrectBag
                                       _ _ _ _ _ _ _ subtree
                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)))
                      | BinNums.Z =>
                        BuildQSIndexedBag
                          heading AttrList'
                          BuildEarlyBag BuildLastBag
                          (fun x => GetAttributeRaw x AttrIndex)
                          ltac:(fun subtree =>
                                  k (@ZTreeBag.IndexedBagAsCorrectBag
                                       _ _ _ _ _ _ _ subtree
                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)))
                      | nat =>
                        BuildQSIndexedBag
                          heading AttrList'
                          BuildEarlyBag BuildLastBag
                          ltac:(fun subtree =>
                                  k (@NatTreeBag.IndexedBagAsCorrectBag
                                       _ _ _ _ _ _ _ subtree
                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)))
                      | string =>
                        BuildQSIndexedBag
                          heading AttrList'
                          BuildEarlyBag BuildLastBag
                          ltac:(fun subtree =>
                                  k (@StringTreeBag.IndexedBagAsCorrectBag
                                       _ _ _ _ _ _ _ subtree
                                       (fun x => GetAttributeRaw (heading := heading) x AttrIndex)))
                      end
                | right _ =>
                  BuildQSIndexedBag
                    heading AttrList'
                    BuildEarlyBag BuildLastBag
                    ltac:(fun subtree =>
                            BuildEarlyBag
                                 heading AttrList AttrKind AttrIndex subtree k)
                end
  | ([ ])%list =>
    k (@CountingListAsCorrectBag
         (@RawTuple heading)
         (IndexedTreeUpdateTermType heading)
         (IndexedTreebupdate_transform heading))
  end.

  Ltac rewrite_drill ::=
       subst_refine_evar; (first
                             [
                               match goal with
                                 |- refine (b <- If_Opt_Then_Else _ _ _; _) _ =>
                                 etransitivity;
                                 [ apply refine_If_Opt_Then_Else_Bind
                                 | simpl; eapply refine_If_Opt_Then_Else_trans;
                                   intros; set_refine_evar ]
                               end
                             | eapply refine_under_bind_both; [ set_refine_evar | intros; set_refine_evar ]
                             | eapply refine_If_Then_Else; [ set_refine_evar | set_refine_evar ] ] ).


  Ltac implement_insert CreateTerm EarlyIndex LastIndex
       makeClause_dep EarlyIndex_dep LastIndex_dep ::=
    repeat first
           [simplify with monad laws; simpl
           | match goal with
               |- context [(@GetAttributeRaw ?heading {| prim_fst := ?a;
                                                         prim_snd := ?tup |} (Fin.FS ?BAidx)) ] =>
               setoid_rewrite (@GetAttributeRaw_FS
                                 (Vector.hd (AttrList heading))
                                 {| AttrList := Vector.tl (AttrList heading)|} a _ BAidx)
             end
           | match goal with
             | |- context [(@GetAttributeRaw ?heading {| prim_fst := ?a;
                                                         prim_snd := ?tup |} Fin.F1) ] =>
               rewrite (@GetAttributeRaw_F1
                          (Vector.hd (AttrList heading))
                          {| AttrList := Vector.tl (AttrList heading) |} a)
             end
           | setoid_rewrite refine_If_Then_Else_Bind
           | match goal with
               H : DelegateToBag_AbsR ?r_o ?r_n
               |- context[Pick (fun idx => forall Ridx, UnConstrFreshIdx (GetUnConstrRelation ?r_o Ridx) idx)] =>
               let freshIdx := fresh in
               destruct (exists_CompletelyUnConstrFreshIdx _ _ _ _ H) as [? freshIdx];
               rewrite (refine_Pick_CompletelyUnConstrFreshIdx _ _ _ _ H _ freshIdx)
             end
           | implement_Query CreateTerm EarlyIndex LastIndex
                             makeClause_dep EarlyIndex_dep LastIndex_dep
           | progress (rewrite ?refine_BagADT_QSInsert; try setoid_rewrite refine_BagADT_QSInsert); [ | solve [ eauto ] .. ]
           | progress (rewrite ?refine_Pick_DelegateToBag_AbsR; try setoid_rewrite refine_Pick_DelegateToBag_AbsR); [ | solve [ eauto ] .. ] ].

  Ltac choose_data_structures :=
    simpl; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;
    match goal with
      |- context [ @Build_IndexedQueryStructure_Impl_Sigs _ ?indices ?SearchTerms _ ] => try unfold SearchTerms
    end; BuildQSIndexedBags' BuildEarlyBag BuildLastBag.

  Ltac insertOne :=
    insertion CreateTerm EarlyIndex LastIndex
              makeClause_dep EarlyIndex_dep LastIndex_dep.

Global Instance cache : Cache :=
  {| CacheEncode := unit;
     CacheDecode := unit;
     Equiv ce cd := True |}.
Global Instance cacheAddNat : CacheAdd cache nat :=
  {| addE ce n := tt;
     addD cd n := tt;
     add_correct ce cd t m := I |}.

Definition transformer : Transformer bin := btransformer.
Global Instance transformerUnit : TransformerUnitOpt transformer bool :=
  {| T_measure t := 1;
     transform_push_opt b t := (b :: t)%list;
     transform_pop_opt t :=
       match t with
       | b :: t' => Some (b, t')
       | _ => None
       end%list
  |}.
abstract (simpl; intros; omega).
abstract (simpl; intros; omega).
abstract (destruct b;
          [ simpl; discriminate
          | intros; injections; simpl; omega ] ).
reflexivity.
reflexivity.
abstract (destruct b; destruct b'; simpl; intros; congruence).
Defined.
Definition Empty : CacheEncode := tt.

  Ltac decompose_EnumField Ridx Fidx :=
    match goal with
      |- appcontext[ @BuildADT (UnConstrQueryStructure (QueryStructureSchemaRaw ?qs_schema)) ]
      =>
      let n := eval compute in (NumAttr (GetHeading qs_schema Ridx)) in
    let AbsR' := constr:(@DecomposeRawQueryStructureSchema_AbsR' n qs_schema ``Ridx ``Fidx id (fun i => ibound (indexb i))
                                                (fun val =>
                                                   {| bindex := _;
                                                      indexb := {| ibound := val;
                                                                   boundi := @eq_refl _ _ |} |})) in hone representation using AbsR'
    end;
      try first [ solve [simplify with monad laws;
                         apply refine_pick_val;
                         apply DecomposeRawQueryStructureSchema_empty_AbsR ]
                | doAny ltac:(implement_DecomposeRawQueryStructure)
                               rewrite_drill ltac:(cbv beta; simpl; finish honing) ];
  simpl; hone representation using (fun r_o r_n => snd r_o = r_n);
    try first [
        solve [simplify with monad laws; apply refine_pick_val; reflexivity ]
      |
      match goal with
        H : snd ?r_o = ?r_n |- _
        => doAny ltac:(implement_DecomposeRawQueryStructure' H)
                        ltac:(rewrite_drill; simpl)
                               ltac:(finish honing)
      end
        ];
    cbv beta; unfold DecomposeRawQueryStructureSchema, DecomposeSchema; simpl.


  Ltac makeEvar T k :=
    let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

  Ltac shelve_inv :=
    let H' := fresh in
    let data := fresh in
    intros data H';
    repeat destruct H';
    match goal with
    | H : ?P data |- ?P_inv' =>
      is_evar P;
      let P_inv' := (eval pattern data in P_inv') in
      let P_inv := match P_inv' with ?P_inv data => P_inv end in
      let new_P_T := type of P in
      makeEvar new_P_T
               ltac:(fun new_P =>
                       unify P (fun data => new_P data /\ P_inv data)); apply (Logic.proj2 H)
    end.

  Ltac solve_data_inv :=
    first [ intros; exact I
          | solve
              [ let data := fresh in
                let H' := fresh in
                let H'' := fresh in
                intros data H' *;
                match goal with
                  proj : BoundedIndex _ |- _ =>
                  instantiate (1 := ibound (indexb proj));
                  destruct H' as [? H'']; intuition;
                  try (rewrite <- H''; reflexivity);
                  destruct data; simpl; eauto
                end ]
          | shelve_inv ].

  Ltac apply_compose :=
    intros;
    match goal with
      H : cache_inv_Property ?P ?P_inv |- _ =>
      first [eapply (compose_encode_correct_no_dep H); clear H
            | eapply (compose_encode_correct H); clear H
            ]
    end.

  Ltac build_decoder :=
    first [ solve [eapply Enum_decode_correct; [   repeat econstructor; simpl; intuition;
    repeat match goal with
            H : @Vector.In _ _ _ _ |- _ =>
            inversion H;
              apply_in_hyp Eqdep.EqdepTheory.inj_pair2; subst
          end
 | .. ]; eauto  ]
          | solve [eapply Word_decode_correct ]
          | solve [eapply Nat_decode_correct ]
          | solve [eapply String_decode_correct ]
          | eapply (SumType_decode_correct
            [ _ ]%vector
            (icons _ inil)
            (icons _ inil)
            (@Iterate_Dep_Type_equiv' 1 _ (icons _ inil))
            (@Iterate_Dep_Type_equiv' 1 _ (icons _ inil)));
            [let idx' := fresh in
             intro idx'; pattern idx';
             eapply Iterate_Ensemble_equiv' with (idx := idx'); simpl;
             repeat (match goal with |- prim_and _ _ => apply Build_prim_and; try exact I end)
            | .. ]
          | eapply (SumType_decode_correct
            [ _; _]%vector
            (icons _ (icons _ inil))
            (icons _ (icons _ inil))
            (@Iterate_Dep_Type_equiv' 2 _ (icons _ (icons _ inil)))
            (@Iterate_Dep_Type_equiv' 2 _ (icons _ (icons _ inil))));
            [let idx' := fresh in
             intro idx'; pattern idx';
             eapply Iterate_Ensemble_equiv' with (idx := idx'); simpl;
             repeat (match goal with |- prim_and _ _ => apply Build_prim_and; try exact I end)
                     | .. ]
          | eapply (SumType_decode_correct
            [ _; _; _ ]%vector
            (icons _ (icons _ (icons _ inil)))
            (icons _ (icons _ (icons _ inil)))
            (@Iterate_Dep_Type_equiv' 3 _ (icons _ (icons _ (icons _ inil))))
            (@Iterate_Dep_Type_equiv' 3 _ (icons (icons _ (icons _ inil)))));
            [let idx' := fresh in
             intro idx'; pattern idx';
             eapply Iterate_Ensemble_equiv' with (idx := idx'); simpl;
             repeat (match goal with |- prim_and _ _ => apply Build_prim_and; try exact I  end)
            | .. ]
          | intros;
            match goal with
              |- encode_decode_correct_f
                   _ _ _
                   (encode_list_Spec _) _ _ =>
              eapply FixList_decode_correct end
          | apply_compose ].

  Lemma Fin_inv :
    forall n (idx : Fin.t (S n)),
      idx = Fin.F1 \/ exists n', idx = Fin.FS n'.
  Proof. apply Fin.caseS; eauto. Qed.

  Ltac solve_cache_inv :=
    repeat instantiate (1 := fun _ => True);
    unfold cache_inv_Property; intuition;
    repeat match goal with
           | idx : Fin.t (S _) |- _ =>
             destruct (Fin_inv _ idx) as [? | [? ?] ]; subst; simpl; eauto
           | idx : Fin.t 0 |- _ =>  inversion idx
           end.

  Ltac finalize_decoder P_inv :=
  (unfold encode_decode_correct_f; intuition eauto);
    [ computes_to_inv; injections; subst; simpl;
      match goal with
        H : Equiv _ ?env |- _ =>
        eexists env; intuition eauto;
        simpl;
        match goal with
          |- ?f ?a ?b ?c = ?P =>
          let P' := (eval pattern a, b, c in P) in
          let f' := match P' with ?f a b c => f end in
          unify f f'; reflexivity
        end
      end
    | injections; eauto
    | eexists _; eexists _;
      intuition eauto; injections; eauto using idx_ibound_eq;
      try match goal with
        |- P_inv ?data => destruct data;
                                 simpl in *; eauto
      end
    ].

  Ltac build_decoder_component :=
    (build_decoder || solve_data_inv).
