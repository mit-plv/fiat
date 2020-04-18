Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.MakeWrapper Bedrock.Platform.Cito.examples.ExampleADT Bedrock.Platform.Cito.examples.ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Bedrock.Platform.Cito.examples.ExampleImpl.

Require Import Bedrock.Platform.Cito.Notations4.

Require Import Coq.Arith.Arith.
Open Scope nat.

Require Import Bedrock.Platform.Cito.examples.FiniteSet.
Require Import Bedrock.Platform.Cito.WordMap.
Import WordMap.

Infix "==" := Equal.
Infix "=s=" := WordSet.Equal (at level 60).

Definition singleton_map elt k v := @add elt k v (empty _).

Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Infix "-->" := (@singleton_map _).

Require Import Bedrock.Platform.Cito.WordMapFacts.

Definition AllDisjoint elt := ForallOrdPairs (@Disjoint elt).

Definition equal_disj_update_all elt h' hs := (h' == @update_all elt hs) /\ AllDisjoint hs.

Notation "h === x ** .. ** y" := (equal_disj_update_all h (cons x .. (cons y nil) ..)) (at level 60).

Require Coq.MSets.MSetProperties.
Module WordSetFacts := MSetProperties.Properties WordSet.

Notation to_set := WordSetFacts.of_list.

Definition wnat (w : W) := wordToNat w.
Coercion wnat : W >-> nat.

Notation " [[ ]] " := nil.
Notation " [[ x , .. , y ]] " := (cons x .. (cons y nil) ..).

Notation empty_set := WordSet.empty.

Definition unique_count ls := WordSet.cardinal (to_set ls).

Definition count_body := (
    "set" <-- DCall "ADT"!"ListSet_new"();;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      find (V "arr") h = Some (Arr arr) /\
      V' "len" = length arr /\
      (h' === h ** (V' "set" --> FSet empty_set)) /\
      V' "arr" = V "arr" /\
      goodSize (length arr)
    ];;
    "i" <- 0;;
    [BEFORE (V, h) AFTER (V', h') exists arr fset,
       find (V "arr") h = Some (Arr arr) /\
       V' "len" = length arr /\
       (h' === h ** (V' "set" --> FSet fset)) /\
       fset =s= to_set (firstn (V' "i") arr) /\
       V' "arr" = V "arr" /\
       goodSize (length arr)
    ]
    While ("i" < "len") {
      "e" <-- DCall "ADT"!"ArraySeq_read" ("arr", "i");;
      Assert [BEFORE (V, h) AFTER (V', h') exists arr fset,
         find (V "arr") h = Some (Arr arr) /\
         V' "len" = length arr /\
         (h' === h ** (V' "set" --> FSet fset)) /\
         fset =s= to_set (firstn (V' "i") arr) /\
         V' "i" < V' "len" /\
         V' "e" = Array.sel arr (V' "i") /\
         V' "arr" = V "arr" /\
         goodSize (length arr)
      ];;
      DCall "ADT"!"ListSet_add"("set", "e");;
      Assert [BEFORE (V, h) AFTER (V', h') exists arr fset,
         find (V "arr") h = Some (Arr arr) /\
         V' "len" = length arr /\
         (h' === h ** (V' "set" --> FSet fset)) /\
         fset =s= to_set (firstn (1 + V' "i") arr) /\
         V' "i" < V' "len" /\
         V' "arr" = V "arr" /\
         goodSize (length arr)
      ];;
      "i" <- "i" + 1
    };;
    "ret" <-- DCall "ADT"!"ListSet_size"("set");;
    Assert [BEFORE (V, h) AFTER (V', h') exists arr fset,
       find (V "arr") h = Some (Arr arr) /\
       (h' === h ** (V' "set" --> FSet fset)) /\
       V' "ret" = unique_count arr
    ];;
    DCall "ADT"!"ListSet_delete"("set");;
    Assert [BEFORE (V, h) AFTER (V', h') exists arr,
       find (V "arr") h = Some (Arr arr) /\
       h' == h /\
       V' "ret" = unique_count arr
    ]
)%stmtex.

Definition main_body := (
    "arr" <-- DCall "ADT"!"ArraySeq_new"(3);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ length arr = 3 ];;
    DCall "ADT"!"ArraySeq_write"("arr", 0, 10);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ length arr = 3 /\ Array.sel arr 0 = 10 ];;
    DCall "ADT"!"ArraySeq_write"("arr", 1, 20);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ exists w, arr = [[$10, $20, w]] ];;
    DCall "ADT"!"ArraySeq_write"("arr", 2, 10);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ arr = [[$10, $20, $10]] ];;
    "ret" <-- DCall "count"!"count" ("arr", 3);;
    Assert [ BEFORE(V, h) AFTER(V', h') exists arr,
      (h' === h ** (V' "arr" --> Arr arr)) /\ V' "ret" = 2 ];;
    DCall "ADT"!"ArraySeq_delete"("arr");;
    Assert [ BEFORE(V, h) AFTER(V', h')
      h' == h /\ V' "ret" = 2 ]
)%stmtex.

Require Import Bedrock.Platform.Cito.ProgramLogic2.

Definition m := cmodule "count" {{
  cfunction "count"("arr", "len")
    count_body
  end with
  cfunction "main"()
    main_body
  end
}}.

Require Import Bedrock.Platform.Cito.GoodModuleDec.
Require Import Bedrock.Platform.Cito.GoodModuleDecFacts.

Lemma good : IsGoodModule m.
  eapply is_good_module_sound.
  reflexivity.
Qed.

Definition gm := to_good_module good.

Import LinkSpecMake2.

Notation "name @ [ p ]" := (name%stmtex, p) (only parsing).

Definition modules := [[ gm ]].

Require Import Bedrock.Platform.Cito.GLabelMapFacts.

Definition imports :=
  of_list
    [[
        "ADT"!"ArraySeq_new" @ [ArraySeq_newSpec],
        "ADT"!"ArraySeq_write" @ [ArraySeq_writeSpec],
        "ADT"!"ArraySeq_read" @ [ArraySeq_readSpec],
        "ADT"!"ArraySeq_delete" @ [ArraySeq_deleteSpec],
        "ADT"!"ListSet_new" @ [ListSet_newSpec],
        "ADT"!"ListSet_add" @ [ListSet_addSpec],
        "ADT"!"ListSet_size" @ [ListSet_sizeSpec],
        "ADT"!"ListSet_delete" @ [ListSet_deleteSpec]
    ]].

Definition dummy_gf : GoodFunction.
  refine (to_good_function (cfunction "dummy"() "ret" <- 0 end)%Citofuncs _).
  eapply is_good_func_sound.
  reflexivity.
Defined.

Definition count := nth 0 (Functions gm) dummy_gf.
Definition main := nth 1 (Functions gm) dummy_gf.

Definition main_spec_Bedrock := func_spec modules imports ("count"!"main")%stmtex main.

Notation extra_stack := 40.

Definition topS := SPEC reserving (4 + extra_stack)
  PREonly[_] mallocHeap 0.

Definition top := bimport [[ ("count"!"main", main_spec_Bedrock), "sys"!"printInt" @ [printIntS],
                             "sys"!"abort" @ [abortS] ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "count"!"main"(extra_stack)
      [PREonly[_, R] [| R = 2 |] ];;

      Call "sys"!"printInt"("R")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Import Semantics.
Require Import Bedrock.Platform.Cito.GLabelMap.
Import GLabelMap.GLabelMap.
Require Import Bedrock.Platform.Cito.ChangeSpec.

Require Bedrock.Platform.Cito.AxSpec.
Import AxSpec.ConformTactic.

Definition count_spec : ForeignFuncSpec.
  refine
    {|
      PreCond := fun args => exists arr len, args = ADT (Arr arr) :: SCA len :: nil /\ len = length arr /\ goodSize (length arr);
      PostCond := fun args ret => exists arr len, args = (ADT (Arr arr), Some (Arr arr)) :: (SCA len, None) :: nil /\ ret = SCA (unique_count arr : W)
    |}.
  conform.
Defined.

Definition main_spec : ForeignFuncSpec.
  refine
    {|
      PreCond := fun args => args = nil;
      PostCond := fun _ ret => ret = SCA $2
    |}.
  conform.
Defined.

Import GLabelMap.GLabelMap.

Definition specs_change_table :=
  of_list
    [[
        "count"!"count" @ [count_spec],
        "count"!"main" @ [main_spec]
    ]]%stmtex.

Arguments Internal {ADTValue} _.
Arguments Foreign {ADTValue} _.

Definition make_specs modules imports := fold_right (fun m acc => fold_right (fun (f : GoodFunction) acc => add (GName m, FName f) (@Internal ADTValue f) acc) acc (Functions m)) (map Foreign imports) modules.

(*
    Notation fst2 := (fun x => @fst _ _ (@fst _ _ x)).

    Lemma make_specs_equal :
      forall modules imports,
        List.NoDup (List.map GName modules) ->
        ListFacts1.Disjoint (List.map GName modules) (List.map fst2 (elements imports)) ->
        specs_equal (make_specs modules imports) modules imports.
    Proof.
      unfold specs_equal.
      induction modules0; simpl; split; intros.
      eapply find_mapsto_iff in H1.
      eapply map_mapsto_iff in H1; openhyp.
      subst; simpl in *.
      right; descend; eauto.
      eapply find_mapsto_iff; eauto.
      unfold label_mapsto in *.
      openhyp.
      intuition.
      subst; simpl in *.
      unfold ForeignFuncSpec in *.
      rewrite map_o; rewrite H2; eauto.

      simpl in *.
    Qed.
 *)

Definition specs_op := make_specs modules imports.
Definition specs := apply_specs_diff specs_op specs_change_table.

Definition empty_precond : assert ADTValue := fun _ v0 v => v0 = v.

Require Import Bedrock.Platform.Cito.WordFacts2 Bedrock.Platform.Cito.WordFacts5.
Require Import Bedrock.Platform.Cito.WordMapFacts.
Import WordMap.
Require Import Bedrock.Platform.Cito.GeneralTactics2.

Lemma empty_mapsto_elim : forall P elt k v, MapsTo k v (empty elt) -> P.
  intros.
  eapply empty_mapsto_iff in H; intuition.
Qed.
Hint Extern 0 => (eapply empty_mapsto_elim; eassumption).
Lemma empty_in_elim : forall P elt k, In k (empty elt) -> P.
  intros.
  eapply empty_in_iff in H; intuition.
Qed.
Hint Extern 0 => (eapply empty_in_elim; eassumption).
Lemma singleton_mapsto_iff : forall elt k v k' v', @MapsTo elt k' v' (k --> v) <-> k' = k /\ v' = v.
  split; intros.
  eapply add_mapsto_iff in H; openhyp; eauto.
  openhyp; eapply add_mapsto_iff; eauto.
Qed.
Lemma singleton_in_iff : forall elt k k' v, @In elt k' (k --> v) <-> k' = k.
  split; intros.
  eapply add_in_iff in H; openhyp; eauto.
  openhyp; eapply add_in_iff; eauto.
Qed.
Lemma update_add : forall elt k v h, @update elt h (k --> v) == add k v h.
  intros.
  unfold Equal; intros.
  eapply option_univalence.
  split; intros.

  eapply find_mapsto_iff in H.
  eapply find_mapsto_iff.
  eapply update_mapsto_iff in H.
  openhyp.
  eapply singleton_mapsto_iff in H.
  openhyp; subst.
  eapply add_mapsto_iff; eauto.
  eapply add_mapsto_iff.
  right.
  split.
  not_not.
  subst.
  eapply singleton_in_iff; eauto.
  eauto.

  eapply find_mapsto_iff in H.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff in H.
  openhyp.
  subst.
  eapply update_mapsto_iff.
  left.
  eapply singleton_mapsto_iff; eauto.
  eapply update_mapsto_iff.
  right.
  split.
  eauto.
  not_not.
  eapply singleton_in_iff in H1; eauto.
Qed.
Lemma singleton_disj : forall elt k v h, ~ @In elt k h <-> Disjoint h (k --> v).
  unfold Disjoint; split; intros.
  not_not; openhyp.
  eapply singleton_in_iff in H0; subst; eauto.
  nintro.
  specialize (H k).
  contradict H.
  split.
  eauto.
  eapply singleton_in_iff; eauto.
Qed.
Lemma separated_star : forall elt h k (v : elt), separated h k (Some v) -> add k v h === h ** k --> v.
  intros.
  unfold separated, Semantics.separated in *.
  openhyp.
  intuition.
  split.
  unfold update_all.
  simpl.
  rewrite update_add.
  rewrite update_empty_1.
  reflexivity.
  repeat econstructor.
  eapply singleton_disj; eauto.
Qed.

Require Import Bedrock.Platform.Cito.BedrockTactics.
Lemma map_fst_combine : forall A B (a : list A) (b : list B), length a = length b -> a = List.map fst (List.combine a b).
  induction a; destruct b; simpl; intuition.
  f_equal; eauto.
Qed.

Ltac eapply_in_any t :=
  match goal with
      H : _ |- _ => eapply t in H
  end.

Lemma map_add_same_key : forall elt m k v1 v2, @add elt k v2 (add k v1 m) == add k v2 m.
  unfold WordMap.Equal; intros.
  repeat rewrite add_o.
  destruct (UWFacts.WFacts.P.F.eq_dec k y); intuition.
Qed.

Lemma not_in_add_remove : forall elt m k v, ~ @In elt k m -> WordMap.remove k (add k v m) == m.
  unfold WordMap.Equal; intros.
  rewrite remove_o.
  rewrite add_o.
  destruct (UWFacts.WFacts.P.F.eq_dec k y); intuition.
  subst.
  symmetry; eapply not_find_in_iff; eauto.
Qed.

Fixpoint same_keys_ls elt (hs1 hs2 : list (t elt)) :=
  match hs1, hs2 with
    | h1 :: hs1', h2 :: hs2' => keys h1 = keys h2 /\ same_keys_ls hs1' hs2'
    | nil, nil => True
    | _ , _ => False
  end.
Require Import Bedrock.Platform.Cito.GeneralTactics3.
Lemma same_keys_in_iff : forall elt (m1 m2 : t elt), keys m1 = keys m2 -> forall k, In k m1 <-> In k m2.
  split; intros.
  eapply In_In_keys; rewrite <- H; eapply In_In_keys; eauto.
  eapply In_In_keys; rewrite H; eapply In_In_keys; eauto.
Qed.
Lemma same_keys_disj : forall elt (a b a' b' : t elt), Disjoint a b -> keys a = keys a' -> keys b = keys b' -> Disjoint a' b'.
  unfold Disjoint; intros.
  specialize (same_keys_in_iff _ _ H0); intros.
  specialize (same_keys_in_iff _ _ H1); intros.
  intuition.
  eapply H; split.
  eapply H2; eauto.
  eapply H3; eauto.
Qed.
Lemma same_keys_forall_disj : forall elt hs1 hs2 h1 h2, List.Forall (@Disjoint elt h1) hs1 -> same_keys_ls hs1 hs2 -> keys h1 = keys h2 -> List.Forall (Disjoint h2) hs2.
  induction hs1; destruct hs2; simpl; intuition.
  inv_clear H.
  econstructor; eauto.
  eapply same_keys_disj; eauto.
Qed.

Lemma same_keys_all_disj : forall elt hs1 hs2, @AllDisjoint elt hs1 -> same_keys_ls hs1 hs2 -> AllDisjoint hs2.
  unfold AllDisjoint; induction hs1; destruct hs2; simpl; intuition.
  inv_clear H.
  econstructor; eauto.
  eapply same_keys_forall_disj; eauto.
Qed.

Lemma add_o_eq : forall elt k v v' m, @find elt k (add k v m) = Some v' -> v = v'.
  intros.
  rewrite add_o in H.
  destruct (eq_dec _ _); [ | intuition].
  injection H; intros; subst; eauto.
Qed.

Ltac split_all :=
  repeat match goal with
           | |- _ /\ _ => split
         end.

Definition count_pre : assert ADTValue :=
  fun _ v0 v =>
    v0 = v /\
    let vs := fst v in
    let h := snd v in
    exists arr,
      find (vs "arr") h = Some (Arr arr) /\
      vs "len" = length arr /\
      goodSize (length arr).
Ltac destruct_state :=
  repeat match goal with
           | [ x : State _ |- _ ] => destruct x; simpl in *
         end.
Require Import Bedrock.Platform.Cito.GeneralTactics4.
Global Add Parametric Morphism elt : (@equal_disj_update_all elt)
    with signature @Equal elt ==> Logic.eq ==> iff as equal_disj_update_all_m.
Proof.
  unfold equal_disj_update_all.
  split; intros; openhyp; split.
  rewrite <- H; eauto.
  eauto.
  rewrite H; eauto.
  eauto.
Qed.
Require Import Bedrock.Platform.Cito.WordFacts Bedrock.Platform.Cito.WordFacts2 Bedrock.Platform.Cito.WordFacts3 Bedrock.Platform.Cito.WordFacts4 Bedrock.Platform.Cito.WordFacts5.
Import Transit.
Lemma in_alldisj_neq : forall elt k1 k2 v2 h, @In elt k1 h -> AllDisjoint [[h, k2 --> v2]] -> k2 <> k1.
  intuition; subst.
  inv_clear H0.
  inversion_Forall.
  eapply H2.
  split; eauto.
  eapply singleton_in_iff; eauto.
Qed.
Theorem lt_true : forall (a b : string) env vs h vs' h',
                    @is_true ADTValue (a < b)%expr env (vs, h) (vs', h')
                    -> (sel vs' a < sel vs' b)%word.
  intros.
  hnf in H.
  simpl in H.
  unfold wltb in H.
  destruct (wlt_dec (vs' a) (vs' b)); try tauto; auto.
Qed.

Theorem lt_false : forall (a b : string) env vs h vs' h',
                     @is_false ADTValue (a < b)%expr env (vs, h) (vs', h')
                     -> (sel vs' a >= sel vs' b)%word.
  intros.
  hnf in H.
  simpl in H.
  unfold wltb in H.
  destruct (wlt_dec (vs' a) (vs' b)); try tauto; auto.
  discriminate.
Qed.

Hint Resolve lt_false lt_true.
Lemma add_swap : forall elt k1 v1 k2 v2 h, @find elt k1 h = Some v1 -> k2 <> k1 -> add k1 v1 (add k2 v2 h) == add k2 v2 h.
  intros; unfold Equal; intros.
  repeat rewrite add_o.
  destruct (eq_dec k1 y); destruct (eq_dec k2 y); subst; intuition eauto.
Qed.
Lemma firstn_plus_1 : forall ls n, n < length ls -> firstn (1 + n) ls = firstn n ls ++ selN ls n :: nil.
  induction ls; destruct n; simpl; intuition.
  f_equal.
  eapply IHls.
  eauto.
Qed.
Lemma fold_firstn :
  forall A (ls : list A) n,
    match ls with
      | [[]] => [[]]
      | a :: l => a :: firstn n l
    end = firstn (1 + n) ls.
  eauto.
Qed.
Import WordSet.
Import WordSetFacts.
Import FM.
Lemma union_empty_right : forall s, union s empty =s= s.
  intros.
  rewrite empty_union_2; eauto.
  reflexivity.
Qed.
Lemma of_list_union : forall ls1 ls2, to_set (ls1 ++ ls2) =s= union (to_set ls1) (to_set ls2).
  induction ls1; destruct ls2; simpl; intuition.
  rewrite IHls1.
  simpl.
  repeat rewrite union_empty_right.
  reflexivity.
  rewrite IHls1.
  simpl.
  rewrite union_add.
  reflexivity.
Qed.
Lemma firstn_whole : forall A (ls : list A) n, length ls <= n -> firstn n ls = ls.
  induction ls; destruct n; simpl; intuition.
  f_equal; eauto.
Qed.

Lemma count_vcs_good : and_all (vc count_body count_pre) specs.
  unfold count_pre, count_body; simpl; unfold imply_close, and_lift; simpl; split_all.
  {
    (* vc1 *)
    intros.
    subst.
    unfold SafeDCall.
    simpl.
    intros.
    openhyp.
    descend.
    instantiate (1 := [[ ]]).
    eauto.
    repeat econstructor.
  }
  {
    (* vc2 *)
    intros.

    destruct_state.
    openhyp.
    subst.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold Transit.TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x1; simpl in *; try discriminate.
    destruct x3; simpl in *; try discriminate.
    inject H10.
    descend; eauto.

    rewrite H9.
    eapply separated_star; eauto.
  }
  {
    (* vc3 *)
    intros.
    openhyp.
    destruct_state.
    simpl in *.
    injection H0; intros; subst.
    sel_upd_simpl.
    descend.
    eauto.
    eauto.
    eauto.
    reflexivity.
    eauto.
  }
  {
    (* vc4 *)
    intros.
    openhyp.
    destruct_state.
    simpl in *.
    injection H0; intros; subst.
    sel_upd_simpl.
    descend.
    eauto.
    eauto.
    eauto.
    rewrite H3.
    unfold wnat.
    erewrite <- next; eauto.
    rewrite plus_comm.
    reflexivity.
    eauto.
  }
  {
    (* vc5 *)
    intros.
    openhyp.
    destruct_state.
    simpl in *.
    unfold SafeDCall.
    simpl.
    intros.
    destruct H2; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; repeat rewrite update_add in *.
    unfold TransitSafe.
    sel_upd_simpl.
    descend.
    {
      instantiate (1 := [[ _, _ ]]); eauto.
    }
    {
      split.
      {
        unfold Semantics.word_adt_match.
        repeat econstructor; simpl.
        {
          instantiate (1 := ADT (Arr x)); simpl in *.
          rewrite H2; eapply find_mapsto_iff; eapply add_mapsto_iff.
          right.
          rewrite H4 in *; clear H4.
          split.
          {
            eapply in_alldisj_neq; eauto.
            eapply MapsTo_In; eapply find_mapsto_iff; eauto.
          }
          eapply find_mapsto_iff; eauto.
        }
        instantiate (1 := SCA (sel v0 "i")); simpl in *.
        eauto.
      }
      simpl.
      unfold Semantics.disjoint_ptrs.
      NoDup.
    }
    descend; eauto.

    rewrite <- H1; eauto.
  }
  {
    (* vc6 *)
    intros.
    openhyp.
    destruct_state.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x2; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    inject H14.
    destruct x4; simpl in *; try discriminate.
    inject H11.
    unfold store_out, Semantics.store_out in *; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst; simpl in *.
    sel_upd_simpl.
    destruct H3; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; repeat rewrite update_add in *.
    rewrite H3 in H14.
    rewrite H5 in *.
    assert (sel v0 "set" <> sel v "arr").
    {
      eapply in_alldisj_neq; eauto.
      eapply MapsTo_In; eapply find_mapsto_iff; eauto.
    }
    rewrite add_neq_o in H14 by eauto.
    change M.find with find in *.
    rewrite H14 in H; injection H; intros; subst.
    descend.
    {
      eauto.
    }
    {
      eauto.
    }
    {
      split.
      {
        rewrite H13.
        rewrite H3; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
        eapply add_swap; eauto.
      }
      eauto.
    }
    {
      eauto.
    }
    {
      eauto.
    }
    eauto.
  }
  {
    (* vc7 *)
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct_state.
    openhyp.
    unfold TransitSafe.
    sel_upd_simpl.
    destruct H1; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; repeat rewrite update_add in *.
    descend.
    instantiate (1 := [[ _, _ ]]); eauto.
    split.
    {
      unfold Semantics.word_adt_match.
      repeat econstructor; simpl.
      {
        instantiate (1 := ADT (FSet x0)); simpl in *.
        rewrite H1; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      }
      instantiate (1 := SCA (sel v0 "e")); simpl in *.
      eauto.
    }
    {
      simpl.
      unfold Semantics.disjoint_ptrs.
      NoDup.
    }
    simpl; eauto.
  }
  (* vc8 *)
  {
    intros.
    openhyp.
    destruct_state.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x2; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    inject H12.
    destruct x4; simpl in *; try discriminate.
    inject H15.
    unfold store_out, Semantics.store_out in *; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst; simpl in *.
    sel_upd_simpl.
    destruct H2; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; repeat rewrite update_add in *.
    rewrite H2 in H15; eapply_in_any add_o_eq; subst; injection H15; intros; subst.
    descend.
    {
      eauto.
    }
    {
      eauto.
    }
    {
      split.
      {
        rewrite H14.
        rewrite H2; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
        eapply map_add_same_key.
      }
      eapply same_keys_all_disj; eauto.
      simpl; eauto.
    }
    {
      rewrite H3.
      rewrite H5.
      rewrite H1 in *.
      Open Scope nat.
      rewrite fold_firstn.
      rewrite firstn_plus_1.
      {
        rewrite of_list_union.
        rewrite union_sym.
        rewrite add_union_singleton.
        simpl.
        rewrite singleton_equal_add.
        reflexivity.
      }
      unfold wnat.
      nomega.
    }
    eauto.
  }
  {
    (* vc9 *)
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct_state.
    openhyp.
    unfold TransitSafe.
    sel_upd_simpl.
    destruct H2; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; repeat rewrite update_add in *.
    descend.
    {
      instantiate (1 := [[ _ ]]); eauto.
    }
    {
      split.
      {
        unfold Semantics.word_adt_match.
        repeat econstructor; simpl.
        instantiate (1 := ADT (FSet x0)); simpl in *.
        rewrite H2; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      }
      simpl.
      unfold Semantics.disjoint_ptrs.
      NoDup.
    }
    simpl; eauto.
  }
  (* vc10 *)
  {
    intros.
    openhyp.
    destruct_state.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x2; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    inject H14.
    destruct x4; simpl in *; try discriminate.
    inject H11.
    unfold store_out, Semantics.store_out in *; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst; simpl in *.
    sel_upd_simpl.
    destruct H3; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; repeat rewrite update_add in *.
    rewrite H3 in H14; eapply_in_any add_o_eq; subst; injection H14; intros; subst.
    descend.
    {
      eauto.
    }
    {
      split.
      {
        rewrite H13.
        rewrite H3; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
        eapply map_add_same_key.
      }
      eapply same_keys_all_disj; eauto.
      simpl; eauto.
    }
    unfold unique_count.
    rewrite H4.
    repeat f_equal.
    eapply firstn_whole.
    eapply lt_false in H1.
    rewrite H2 in *.
    unfold wnat in *.
    nomega.
  }
  {
    (* vc11 *)
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct_state.
    openhyp.
    destruct H0; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; repeat rewrite update_add in *.
    unfold TransitSafe.
    sel_upd_simpl.
    descend.
    {
      instantiate (1 := [[ _ ]]); eauto.
    }
    {
      split.
      {
        unfold Semantics.word_adt_match.
        repeat econstructor; simpl.
        instantiate (1 := ADT (FSet x0)); simpl in *.
        rewrite H0; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      }
      simpl.
      unfold Semantics.disjoint_ptrs.
      NoDup.
    }
    descend; eauto.
  }
  {
    (* vc12 *)
    intros.
    openhyp.
    destruct_state.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x2; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    inject H7.
    destruct x4; simpl in *; try discriminate.
    inject H10.
    unfold store_out, Semantics.store_out in *; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst; simpl in *.
    sel_upd_simpl.
    destruct H1; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; repeat rewrite update_add in *.
    rewrite H1 in H10; eapply_in_any add_o_eq; subst; injection H10; intros; subst.
    descend.
    {
      eauto.
    }
    {
      rewrite H9.
      rewrite H1.
      eapply not_in_add_remove.
      eapply singleton_disj.
      inv_clear H3.
      inversion_Forall.
      eauto.
    }
    eauto.
  }
  eauto.
Qed.

Local Hint Immediate count_vcs_good.

Require Import SemanticsFacts4.
Definition output_gen (h : Heap ADTValue) w (i : Value ADTValue) :=
  match w, i with
    | _, SCA _ => None
    | w, ADT _ => WordMap.find w h
  end.
Require Import ListFacts4.
Import Transit.
Lemma combine_fst_snd : forall A B (ls : list (A * B)), List.combine (List.map fst ls) (List.map snd ls) = ls.
  induction ls; simpl; intuition.
  simpl; f_equal; eauto.
Qed.
Lemma combine_fst_snd' : forall A B (ls : list (A * B)) a b, a = List.map fst ls -> List.map snd ls = b -> ls = List.combine a b.
  intros.
  specialize (combine_fst_snd ls); intros.
  rewrite H0 in H1.
  rewrite <- H in H1.
  eauto.
Qed.
Arguments uncurry {_ _ _} _ _ / .
Import WordMap.
Lemma add_no_effect : forall elt k v h, @find elt k h = Some v -> add k v h == h.
  unfold Equal; intros.
  repeat rewrite add_o.
  destruct (eq_dec k y); subst; intuition.
Qed.
Arguments uncurry {_ _ _} _ _ / .
Arguments uncurry {_ _ _} _ _ / .
Arguments uncurry {_ _ _} _ _ / .

Lemma count_strengthen : forall env_ax, specs_env_agree specs env_ax -> strengthen_op_ax count count_spec env_ax.
  intros.
  unfold strengthen_op_ax, strengthen_op_ax'.

  exists (fun words inputs h => List.map (uncurry (output_gen h)) (List.combine words inputs)).
  exists (fun _ _ => None).
  split_all.
  {
    unfold outputs_gen_ok.
    intros words inputs h Hpre Hlen.
    rewrite map_length.
    rewrite combine_length_eq by eauto.
    eauto.
  }
  {
    intros.
    simpl in *.
    openhyp.
    rewrite H0; simpl; eauto.
  }
  {
    intros.
    cito_safe count count_pre count_vcs_good.
    split.
    {
      eauto.
    }
    unfold TransitSafe in *.
    openhyp.
    simpl in *.
    openhyp.
    subst; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    descend; eauto.
  }
  {
    cito_runsto count count_pre count_vcs_good.
    {
      unfold TransitSafe in *.
      openhyp.
      simpl in *.
      openhyp.
      subst; simpl in *.
      unfold good_inputs, Semantics.good_inputs in *.
      openhyp.
      unfold Semantics.word_adt_match in *.
      inversion_Forall; simpl in *.
      unfold ExampleADT.ADTValue in *.
      erewrite H0 in H9.
      inject H9.
      unfold TransitTo.
      descend.
      {
        split.
        {
          unfold Semantics.word_adt_match in *.
          simpl.
          repeat econstructor.
          {
            simpl; eauto.
          }
          unfold Semantics.disjoint_ptrs.
          NoDup.
        }
        simpl.
        descend.
      }
      {
        eauto.
      }
      {
        simpl.
        descend; eauto.
        {
          Arguments uncurry {_ _ _} _ _ / .
          simpl.
          unfold store_out, Semantics.store_out in *; simpl in *.
          repeat f_equal.
          rewrite H2.
          eauto.
        }
          Arguments uncurry {_ _ _} _ _ / .
        f_equal.
        eauto.
      }
      {
        repeat econstructor.
      }
      simpl.
      unfold store_out, Semantics.store_out in *; simpl in *.
      rewrite H2.
      rewrite H0.
      rewrite add_no_effect; eauto; reflexivity.
    }
    split.
    { eauto. }
    unfold TransitSafe in *.
    openhyp.
    simpl in *.
    openhyp.
    subst; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    descend; eauto.
  }
Qed.
Import Transit.
Opaque natToWord.

Lemma main_vcs_good : and_all (vc main_body empty_precond) specs.
  unfold empty_precond, main_body; simpl; unfold imply_close, and_lift; simpl; split_all.
  {
    (* vc1 *)
    intros.
    subst.
    unfold SafeDCall.
    simpl.
    intros.
    unfold TransitSafe.
    descend.
    instantiate (1 := [[ _ ]]).
    eauto.
    repeat econstructor.
    instantiate (1 := SCA $3).
    repeat econstructor.
    repeat econstructor.
    descend; eauto.
  }
  {
    (* vc2 *)
    intros.
    destruct_state.
    openhyp.
    subst.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x0; simpl in *; try discriminate.
    destruct x0; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    inject H7.
    inject H4.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst.
    unfold store_out, Semantics.store_out in *; simpl in *.
    descend; eauto.
    rewrite H6.
    eapply separated_star; eauto.
  }
  {
    (* vc3 *)
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct_state.
    openhyp.
    destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in *; rewrite update_add in *.
    unfold TransitSafe.
    descend.
    {
      sel_upd_simpl.
      instantiate (1 := [[ ADT _, SCA _, SCA _ ]]); eauto.
    }
    {
      split.
      {
        unfold Semantics.word_adt_match.
        repeat econstructor; simpl; eauto.
        sel_upd_simpl.
        instantiate (1 := Arr x); simpl in *.
        rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      }
      unfold Semantics.disjoint_ptrs.
      NoDup.
    }
    descend; eauto.
    rewrite H0.
    eauto.
  }
  {
    (* vc4 *)
    intros.
    openhyp.
    destruct_state.
    destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x1; simpl in *; try discriminate.
    destruct x1; simpl in *; try discriminate.
    destruct x1; simpl in *; try discriminate.
    destruct x3; simpl in *; try discriminate.
    inject H7.
    inject H10.
    unfold store_out, Semantics.store_out in *; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst; simpl in *.
    sel_upd_simpl.
    rewrite H in H10.
    eapply_in_any add_o_eq; subst.
    injection H10; intros; subst.
    descend.
    {
      split.
      {
        rewrite H9.
        rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
        eapply map_add_same_key.
      }
      eapply same_keys_all_disj; eauto.
      simpl; eauto.
    }
    {
      rewrite upd_length; eauto.
    }
    eapply CompileExpr.sel_upd_eq; eauto.
    rewrite H1; eauto.
  }
  {
    (* vc5 *)
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct_state.
    openhyp.
    destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
    unfold TransitSafe.
    sel_upd_simpl.
    descend.
    {
      instantiate (1 := [[ ADT _, SCA _, SCA _ ]]); eauto.
    }
    {
      split.
      {
        unfold Semantics.word_adt_match.
        repeat econstructor; simpl; eauto.
        instantiate (1 := Arr x); simpl in *.
        rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      }
      unfold Semantics.disjoint_ptrs.
      NoDup.
    }
    descend; eauto.
    rewrite H0; eauto.
  }
  {
    (* vc6 *)
    intros.
    openhyp.
    destruct_state.
    destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x1; simpl in *; try discriminate.
    destruct x1; simpl in *; try discriminate.
    destruct x1; simpl in *; try discriminate.
    destruct x3; simpl in *; try discriminate.
    inject H8.
    inject H11.
    unfold store_out, Semantics.store_out in *; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst; simpl in *.
    sel_upd_simpl.
    rewrite H in H11; eapply_in_any add_o_eq; subst; injection H11; intros; subst.
    destruct x5; simpl in *; try discriminate.
    destruct x5; simpl in *; try discriminate.
    destruct x5; simpl in *; try discriminate.
    destruct x5; simpl in *; try discriminate.
    descend.
    {
      split.
      {
        rewrite H10.
        rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
        eapply map_add_same_key.
      }
      eapply same_keys_all_disj; eauto.
      simpl; eauto.
    }
    Transparent natToWord.
    unfold Array.upd; simpl.
    unfold Array.sel in H2; simpl in H2; subst.
    repeat f_equal.
  }
  {
    (* vc7 *)
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct_state.
    openhyp.
    destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
    unfold TransitSafe.
    sel_upd_simpl.
    descend.
    {
      instantiate (1 := [[ ADT _, SCA _, SCA _ ]]); eauto.
    }
    {
      split.
      {
        unfold Semantics.word_adt_match.
        repeat econstructor; simpl; eauto.
        instantiate (1 := Arr x); simpl in *.
        rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      }
      unfold Semantics.disjoint_ptrs.
      NoDup.
    }
    descend; eauto.
    rewrite H0; eauto.
  }
  {
    (* vc8 *)
    intros.
    openhyp.
    destruct_state.
    destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x2; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    destruct x4; simpl in *; try discriminate.
    inject H7.
    inject H10.
    unfold store_out, Semantics.store_out in *; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst; simpl in *.
    sel_upd_simpl.
    rewrite H in H7; eapply_in_any add_o_eq; subst; inject H7.
    descend.
    {
      split.
      {
        rewrite H9.
        rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
        eapply map_add_same_key.
      }
      eapply same_keys_all_disj; eauto.
      simpl; eauto.
    }
    Transparent natToWord.
    reflexivity.
    Opaque natToWord.
  }
  {
    (* vc9 *)
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct_state.
    openhyp.
    destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
    unfold TransitSafe.
    sel_upd_simpl.
    descend.
    {
      instantiate (1 := [[ ADT _, SCA _ ]]); eauto.
    }
    {
      split.
      {
        unfold Semantics.word_adt_match.
        repeat econstructor; simpl; eauto.
        instantiate (1 := Arr x); simpl in *.
        rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      }
      unfold Semantics.disjoint_ptrs.
      NoDup.
    }
    descend.
    { eauto. }
    { rewrite H0; eauto. }
    rewrite H0; simpl.
    eauto.
  }
  {
    (* vc10 *)
    intros.
    openhyp.
    destruct_state.
    destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x1; simpl in *; try discriminate.
    destruct x1; simpl in *; try discriminate.
    destruct x1; simpl in *; try discriminate.
    destruct x3; simpl in *; try discriminate.
    inject H7.
    inject H10.
    unfold store_out, Semantics.store_out in *; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst; simpl in *.
    sel_upd_simpl.
    rewrite H in H7; eapply_in_any add_o_eq; subst; inject H7.
    descend.
    {
      split.
      {
        rewrite H9.
        rewrite H; unfold update_all; simpl; rewrite update_empty_1; rewrite update_add.
        eapply map_add_same_key.
      }
      eapply same_keys_all_disj; eauto.
      simpl; eauto.
    }
    reflexivity.
  }
  {
    (* vc11 *)
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct_state.
    openhyp.
    destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
    unfold TransitSafe.
    sel_upd_simpl.
    descend.
    {
      instantiate (1 := [[ _ ]]); eauto.
    }
    {
      split.
      {
        unfold Semantics.word_adt_match.
        repeat econstructor; simpl.
        instantiate (1 := ADT (Arr x)); simpl in *.
        rewrite H; eapply find_mapsto_iff; eapply add_mapsto_iff; eauto.
      }
      unfold Semantics.disjoint_ptrs.
      NoDup.
    }
    descend.
    eauto.
  }
  {
    (* vc12 *)
    intros.
    openhyp.
    destruct_state.
    destruct H; unfold update_all in *; simpl in *; rewrite update_empty_1 in H; repeat rewrite update_add in H.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x1; simpl in *; try discriminate.
    destruct x1; simpl in *; try discriminate.
    destruct x3; simpl in *; try discriminate.
    inject H7.
    inject H10.
    unfold store_out, Semantics.store_out in *; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst; simpl in *.
    sel_upd_simpl.
    rewrite H in H10; eapply_in_any add_o_eq; subst; injection H10; intros; subst.
    descend.
    rewrite H9.
    rewrite H.
    eapply not_in_add_remove.
    eapply singleton_disj.
    inv_clear H2.
    inversion_Forall.
    eauto.
  }
  eauto.
Qed.

Local Hint Immediate main_vcs_good.
Import Transit.

Lemma main_strengthen : forall env_ax, specs_env_agree specs env_ax -> strengthen_op_ax main main_spec env_ax.
  intros.
  unfold strengthen_op_ax, strengthen_op_ax'.
  exists (fun words inputs h => List.map (uncurry (output_gen h)) (List.combine words inputs)).
  exists (fun _ _ => None).
  split_all.
  {
    unfold outputs_gen_ok.
    intros words inputs h Hpre Hlen.
    rewrite map_length.
    rewrite combine_length_eq by eauto.
    eauto.
  }
  {
    intros.
    simpl in *.
    rewrite H0; simpl; eauto.
  }
  {
    intros.
    cito_safe main empty_precond main_vcs_good.
  }
  {
    cito_runsto main empty_precond main_vcs_good.
    2 : eauto.
    unfold TransitTo.
    unfold TransitSafe in *; simpl in *.
    openhyp.
    descend.
    { f_equal; eauto. }
    {
      repeat econstructor.
    }
    eauto.
  }
Qed.

Lemma specs_strengthen_diff : forall env_ax, specs_env_agree specs env_ax -> strengthen_diff specs_op specs_change_table env_ax.
  intros.
  unfold strengthen_diff.
  rewrite GLabelMap.fold_1.
  Opaque specs specs_op.
  simpl.
  Transparent specs specs_op.
  unfold strengthen_diff_f.
  split_all.
  eauto.
  right.
  eexists.
  split.
  reflexivity.
  eapply count_strengthen; eauto.
  right.
  eexists.
  split.
  reflexivity.
  eapply main_strengthen; eauto.
Qed.

Import LinkSpecMake.
Require Import Bedrock.Platform.Cito.LinkSpecFacts.

Import GLabelMap.GLabelMap.
Import GLabelMapFacts.
Import LinkSpecMake.

Lemma specs_op_equal : specs_equal specs_op modules imports.
  split; intros.
  unfold specs_equal, specs_op in *; simpl in *.
  eapply find_mapsto_iff in H; eapply add_mapsto_iff in H; openhyp.
  subst; simpl in *.
  left; descend; eauto.
  unfold gm, to_good_module; simpl; eauto.
  eapply add_mapsto_iff in H0; openhyp.
  subst; simpl in *.
  left; descend; eauto.
  unfold gm, to_good_module; simpl; eauto.
  eapply map_mapsto_iff in H1; openhyp.
  subst; simpl in *.
  eapply find_mapsto_iff in H2.
  right; descend; eauto.

  unfold label_mapsto in *.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  reflexivity.
  subst; simpl in *.
  reflexivity.
  intuition.
  intuition.
  subst; simpl in *.
  assert (lbl <> ("count", "count") /\ lbl <> ("count", "main")).
  split.
  nintro.
  subst; simpl in *.
  compute in H0; intuition.
  nintro.
  subst; simpl in *.
  compute in H0; intuition.
  openhyp.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  right.
  split.
  eauto.
  eapply add_mapsto_iff.
  right.
  split.
  eauto.
  eapply find_mapsto_iff in H0.
  eapply map_mapsto_iff.
  descend; eauto.
Qed.

Lemma specs_equal_domain : equal_domain specs specs_op.
  eapply equal_domain_dec_sound; reflexivity.
Qed.

Hint Resolve specs_op_equal specs_equal_domain.

Lemma new_env_strengthen : forall stn fs, env_good_to_use modules imports stn fs -> strengthen (from_bedrock_label_map (Labels stn), fs stn) (change_env specs (from_bedrock_label_map (Labels stn), fs stn)).
  intros.
  eapply strengthen_diff_strenghthen.
  Focus 2.
  eapply specs_equal_agree; eauto.
  Focus 2.
  eapply change_env_agree; eauto; eapply specs_equal_agree; eauto.
  eapply specs_strengthen_diff; eauto.
  eapply change_env_agree; eauto; eapply specs_equal_agree; eauto.
  intros; simpl; eauto.
Qed.

Lemma main_safe' : forall stn fs v, env_good_to_use modules imports stn fs -> Safe (change_env specs (from_bedrock_label_map (Labels stn), fs stn)) (Body main) v.
  cito_safe main empty_precond main_vcs_good.
  eapply change_env_agree; eauto; eapply specs_equal_agree; eauto.
Qed.

Lemma main_safe : forall stn fs v, env_good_to_use modules imports stn fs -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body main) v.
  intros.
  eapply strengthen_safe with (env_ax := change_env specs (from_bedrock_label_map (Labels stn), fs stn)).
  eapply main_safe'; eauto.
  eapply new_env_strengthen; eauto.
Qed.

Lemma main_runsto : forall stn fs v v', env_good_to_use modules imports stn fs -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body main) v v' -> sel (fst v') (RetVar f) = 2 /\ snd v' == snd v.
  intros.
  eapply strengthen_runsto with (env_ax := change_env specs (from_bedrock_label_map (Labels stn), fs stn)) in H0.
  cito_runsto main empty_precond main_vcs_good.
  split; eauto.
  2 : eauto.
  eapply change_env_agree; eauto; eapply specs_equal_agree; eauto.
  eapply new_env_strengthen; eauto.
  eapply main_safe'; eauto.
Qed.

Require Import Bedrock.Platform.Cito.Inv.
Module Import InvMake := Make ExampleADT.
Module Import InvMake2 := Make ExampleRepInv.
Import Made.
Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.

Theorem top_ok : moduleOk top.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.

  post.
  call_cito 40 (@nil string).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  eapply CompileExprs.change_hyp.
  Focus 2.
  apply (@is_state_in''' (upd x2 "extra_stack" 40)).
  autorewrite with sepFormula.
  clear H7.
  hiding ltac:(step auto_ext).
  apply main_safe; eauto.
  hiding ltac:(step auto_ext).
  repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
  apply swap; apply injL; intro.
  openhyp.
  match goal with
    | [ x : State |- _ ] => destruct x; simpl in *
  end.
  eapply_in_any main_runsto; simpl in *; intuition subst.
  eapply replace_imp.
  change 40 with (wordToNat (sel (upd x2 "extra_stack" 40) "extra_stack")).
  apply is_state_out'''''.
  NoDup.
  NoDup.
  NoDup.
  eauto.

  clear H7.
  hiding ltac:(step auto_ext).
  hiding ltac:(step auto_ext).

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
Qed.

Definition all := link top (compile_to_bedrock modules imports).

Theorem all_ok : moduleOk all.
  link0 top_ok.
Qed.
