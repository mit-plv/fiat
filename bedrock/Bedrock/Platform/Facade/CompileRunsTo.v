Set Implicit Arguments.

Require Import Bedrock.Memory Bedrock.IL.
Require Import Bedrock.Platform.Cito.GLabel.
Require Import Bedrock.Platform.Facade.Facade.

Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Bedrock.Platform.Cito.Syntax.
Require Import Bedrock.Platform.Cito.SyntaxExpr.
Require Import Bedrock.Platform.Cito.StringMap.
Import StringMap.
Require Import Bedrock.Platform.Cito.StringMapFacts.
Import FMapNotations.
Local Open Scope fmap_scope.

Require Import Bedrock.Platform.Facade.Compile.

Coercion Var : string >-> Expr.

Section ADTValue.

  Variable ADTValue : Type.

  Require Bedrock.Platform.Cito.Semantics.

  Notation RunsTo := (@RunsTo ADTValue).
  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).
  Notation Value := (@Value ADTValue).
  Notation Sca := (@SCA ADTValue).
  Notation Adt := (@ADT ADTValue).

  Definition represent p (o : option ADTValue) v :=
    match v with
      | SCA w => p = w
      | ADT a => o = Some a
    end.

  Require Import Bedrock.Platform.Cito.WordMap.

  Notation CitoState := (@Semantics.State ADTValue).
  Notation CitoCallee := (@Semantics.Callee ADTValue).
  Notation CitoInternal := (@Semantics.Internal ADTValue).
  Notation CitoRunsTo := (@Semantics.RunsTo ADTValue).

  Definition related (s_st : State) (t_st : CitoState) :=
    (forall x v,
       find x s_st = Some v -> let p := Locals.sel (fst t_st) x in represent p (WordMap.find p (snd t_st)) v) /\
    (forall p a,
       WordMap.find p (snd t_st) = Some a ->
       exists! x,
         Locals.sel (fst t_st)  x = p /\
         find x s_st = Some (ADT a)).

  Definition CitoEnv := ((glabel -> option W) * (W -> option CitoCallee))%type.

  Require Import Bedrock.Platform.Cito.ListFacts1 Bedrock.Platform.Cito.ListFacts2 Bedrock.Platform.Cito.ListFacts3 Bedrock.Platform.Cito.ListFacts5.

  Definition FuncSpec := @FuncSpec ADTValue.

  Definition compile_spec (spec : FuncSpec) : CitoCallee :=
    match spec with
      | Axiomatic s => Semantics.Foreign s
      | Operational s => CitoInternal (compile_op s)
    end.

  Definition cenv_impls_env (cenv : CitoEnv) (env : Env) :=
    (forall lbl w,
       Label2Word env lbl = Some w ->
       fst cenv lbl = Some w) /\
    (forall w spec,
       Word2Spec env w = Some spec ->
       snd cenv w = Some (compile_spec spec)).

  Require Import Bedrock.Platform.Cito.GeneralTactics.
  Require Import Bedrock.Platform.Cito.GeneralTactics3.
  Require Import Bedrock.Platform.Cito.GeneralTactics4.
  Require Import Bedrock.Platform.Facade.FacadeFacts.

  Notation ceval := SemanticsExpr.eval.
  Notation cRunsTo := Semantics.RunsTo.
  Lemma eval_ceval : forall s_st vs h e w, eval s_st e = Some (SCA _ w) -> related s_st (vs, h) -> ceval vs e = w.
  Proof.
    induction e; simpl in *; intuition.
    unfold related in *.
    openhyp.
    eapply H0 in H.
    simpl in *.
    eauto.

    inject H.
    eauto.

    unfold eval_binop_m in *.
    destruct (option_value_dec (eval s_st e1)).
    destruct s.
    destruct s.
    rewrite e in *.
    destruct (option_value_dec (eval s_st e2)).
    destruct s.
    destruct s.
    rewrite e0 in *.
    inject H.
    erewrite IHe1; [ | eauto .. ].
    erewrite IHe2; [ | eauto .. ].
    eauto.
    destruct s.
    rewrite e0 in *; discriminate.
    rewrite e0 in *; discriminate.
    destruct s.
    rewrite e in *; discriminate.
    rewrite e in *; discriminate.

    unfold eval_binop_m in *.
    destruct (option_value_dec (eval s_st e1)).
    destruct s.
    destruct s.
    rewrite e in *.
    destruct (option_value_dec (eval s_st e2)).
    destruct s.
    destruct s.
    rewrite e0 in *.
    inject H.
    erewrite IHe1; [ | eauto .. ].
    erewrite IHe2; [ | eauto .. ].
    eauto.
    destruct s.
    rewrite e0 in *; discriminate.
    rewrite e0 in *; discriminate.
    destruct s.
    rewrite e in *; discriminate.
    rewrite e in *; discriminate.
  Qed.

  Lemma eval_bool_wneb : forall (s_st : State) vs h e b, eval_bool s_st e = Some b -> related s_st (vs, h) -> wneb (ceval vs e) $0 = b.
  Proof.
    intros.
    unfold eval_bool in *.
    destruct (option_value_dec (eval s_st e)).
    destruct s.
    destruct s.
    rewrite e0 in *.
    inject H.
    eapply eval_ceval in e0; [ | eauto].
    rewrite e0 in *; eauto.
    destruct s.
    rewrite e0 in *; discriminate.
    rewrite e0 in *; discriminate.
  Qed.

  Notation boolcase := Sumbool.sumbool_of_bool.

  Lemma wneb_is_true : forall s_st vs h e, wneb (ceval vs e) $0 = true -> related s_st (vs, h) -> is_bool s_st e -> is_true s_st e.
  Proof.
    intros.
    unfold is_true.
    unfold is_bool in *.
    eapply ex_up in H1.
    openhyp.
    destruct (boolcase x); subst.
    eauto.
    eapply eval_bool_wneb in H1; eauto.
    set (ceval _ _) in *.
    rewrite H in *; discriminate.
  Qed.

  Lemma wneb_is_false : forall s_st vs h e, wneb (ceval vs e) $0 = false -> related s_st (vs, h) -> is_bool s_st e -> is_false s_st e.
  Proof.
    intros.
    unfold is_false.
    unfold is_bool in *.
    eapply ex_up in H1.
    openhyp.
    destruct (boolcase x); subst.
    eapply eval_bool_wneb in H1; eauto.
    set (ceval _ _) in *.
    rewrite H in *; discriminate.
    eauto.
  Qed.

  Require Import Bedrock.StringSet.

  Require Import Bedrock.Platform.Cito.WordMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.
  Require Import Bedrock.Platform.Cito.WordMap.
  Import WordMap.

  Require Import Bedrock.Platform.Cito.GeneralTactics2.
  Hint Extern 0 (_ == _) => reflexivity.

  Ltac subst' H := rewrite H in *; clear H.

  Ltac openhyp' :=
    repeat match goal with
             | H : _ /\ _ |- _  => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H : exists x, _ |- _ => destruct H
             | H : exists ! x, _ |- _ => destruct H
             | H : unique _ _ |- _ => destruct H
           end.

  Ltac unfold_related H := copy H; unfold related in H; simpl in H; openhyp.

  Lemma related_no_alias : forall vs h st x1 a1 x2 a2, related st (vs, h) -> StringMap.find x1 st = Some (ADT a1) -> StringMap.find x2 st = Some (ADT a2) -> vs x1 = vs x2 -> x1 = x2.
  Proof.
    intros.
    unfold_related H.
    copy H0; eapply H in H0; simpl in *.
    copy H1; eapply H in H1; simpl in *.
    unfold Locals.sel in *.
    rewrite H2 in *.
    rewrite H0 in H1; inject H1.
    eapply H4 in H0; openhyp'.
    assert (x = x1) by (eapply H1; eauto).
    assert (x = x2) by (eapply H1; eauto).
    eauto.
  Qed.

  Arguments related_no_alias [_ _] _ _ _ _ _ _ _ _ _.

  Require Import Bedrock.Platform.Cito.Option.

(*

  s_st ------- s_env, s --------> exists s_st'
 (Safe)
   ||             |                  ||
   ||          compile               ||
   ||             |                  ||
   ||             v                  ||

  t_st ------ t_env, t -------->    t_st'

*)

  Require Import Coq.Lists.List.
  Require Import Bedrock.Platform.Cito.ListFacts4.
  Import WordMap.

  Require Import Bedrock.Platform.Cito.SemanticsFacts8.

  Lemma related_no_aliasM st args input vs h :
    mapM (sel st) args = Some input ->
    related st (vs, h) ->
    NoDup args ->
    no_aliasM vs args input.
  Proof.
    intros Hmm Hr Hnd.
    unfold no_aliasM, no_dupM, only_adt.
    intros i j p ai aj Hki Hvi Hkj Hvj.
    eapply nth_error_map_elim in Hki.
    destruct Hki as [ki [Hki Hvs]].
    subst.
    eapply nth_error_map_elim in Hvi.
    destruct Hvi as [vi [Hvi Hai]].
    destruct vi as [wi | ai'].
    discriminate.
    inject Hai.
    copy_as Hmm Hmm'; eapply mapM_nth_error_1 in Hmm'; eauto.
    destruct Hmm' as [v' [? Hfki]].
    unif v'.
    eapply nth_error_map_elim in Hkj.
    destruct Hkj as [kj [Hkj Hvs]].
    eapply nth_error_map_elim in Hvj.
    destruct Hvj as [vj [Hvj Haj]].
    destruct vj as [wj | aj'].
    discriminate.
    inject Haj.
    copy_as Hmm Hmm'; eapply mapM_nth_error_1 in Hmm'; eauto.
    destruct Hmm' as [v' [? Hfkj]].
    unif v'.
    assert (ki = kj).
    eapply related_no_alias; eauto.
    subst.
    eapply NoDup_nth_error; eauto.
  Qed.

  Ltac split' name :=
    match goal with
      | |- ?T /\ _ => assert (name: T); [ | split; [ auto | ] ]
    end.

  Lemma change_var_names vs1 vs2 h vars1 vars2 input :
    related (StringMapFacts.make_map vars1 input) (vs1, h) ->
    List.map (fun x => vs2 x) vars2 = List.map (fun x => vs1 x) vars1 ->
    NoDup vars1 ->
    NoDup vars2 ->
    length vars1 = length input ->
    related (StringMapFacts.make_map vars2 input) (vs2, h).
  Proof.
    intros Hr Hm Hnd1 Hnd2 Hl.
    copy_as Hr Hr'.
    destruct Hr' as [Hr1 Hr2]; unfold related; simpl in *.
    unfold Locals.sel in *.
    split.

    intros x2 v Hf.
    eapply find_Some_make_map_iff in Hf; eauto.
    destruct Hf as [i [Hx2 Hv]].
    eapply map_eq_nth_error_1 in Hm; eauto.
    destruct Hm as [x1 [Hx1 Hvs]].
    subst' Hvs.
    eapply Hr1.
    solve [eapply find_Some_make_map_iff; eauto].
    rewrite <- Hl; solve [eapply map_eq_length_eq; eauto].

    intros p a Hfp.
    eapply Hr2 in Hfp.
    destruct Hfp as [x1 [[Hp Hfx1] Hu]].
    subst.
    eapply find_Some_make_map_iff in Hfx1; eauto.
    destruct Hfx1 as [i [Hx1 Hi]].
    copy_as Hm Hm'; symmetry in Hm'; eapply map_eq_nth_error_1 in Hm'; eauto.
    destruct Hm' as [x2 [Hx2 Hvs]].
    subst' Hvs.
    exists x2.
    split.
    split.
    eauto.
    eapply find_Some_make_map_iff; eauto.
    rewrite <- Hl; solve [eapply map_eq_length_eq; eauto].
    intros x2' [Hvs Hfx2'].
    eapply find_Some_make_map_iff in Hfx2'; eauto.
    destruct Hfx2' as [i' [Hx'2 Hi']].
    assert (Heqi : i = i').
    eapply map_eq_nth_error_1 in Hm; eauto.
    destruct Hm as [x1' [Hx1' Hvs']].
    subst' Hvs'.
    assert (Hex1 : x1 = x1').
    eapply Hu.
    split.
    eauto.
    eapply find_Some_make_map_iff; eauto.
    subst.
    solve [eapply (NoDup_nth_error Hnd1); eauto].
    subst.
    unif x2'.
    eauto.
    rewrite <- Hl; solve [eapply map_eq_length_eq; eauto].
  Qed.

  Lemma reachable_submap_related st args input vs h :
    mapM (sel st) args = Some input ->
    related st (vs, h) ->
    NoDup args ->
    reachable_heap vs args input <= h /\
    related (StringMapFacts.make_map args input) (vs, reachable_heap vs args input).
  Proof.
    intros Hmm Hr Hdn.
    split.
    unfold Submap.
    intros p a Hf.
    eapply find_Some_reachable_heap_iff in Hf.
    destruct Hf as [i [k [Hk [Hin Hvs]]]].
    subst.
    eapply mapM_nth_error_1 in Hmm; eauto.
    destruct Hmm as [v [Hin' Hfk]].
    unif v.
    eapply Hr in Hfk; simpl in *.
    solve [eauto].
    solve [eapply mapM_length; eauto].
    solve [eapply related_no_aliasM; eauto].

    split; simpl.
    intros k v Hfk.
    eapply find_Some_make_map_iff in Hfk; eauto.
    destruct Hfk as [i [Hk Hin]].
    copy_as Hmm Hmm'; eapply mapM_nth_error_1 in Hmm'; eauto.
    destruct Hmm' as [v' [? Hfk]].
    unif v'.
    eapply Hr in Hfk; simpl in *.
    destruct v as [w | a]; simpl in *.
    eauto.
    eapply find_Some_reachable_heap_iff; eauto.
    solve [eapply mapM_length; eauto].
    solve [eapply related_no_aliasM; eauto].
    solve [eapply mapM_length; eauto].

    intros p a Hfp.
    eapply find_Some_reachable_heap_iff in Hfp; eauto.
    destruct Hfp as [i [k [Hk [Hin Hvs]]]].
    subst.
    copy_as Hmm Hmm'; eapply mapM_nth_error_1 in Hmm'; eauto.
    destruct Hmm' as [v' [? Hfk]].
    unif v'.
    exists k.
    split.
    split.
    eauto.
    eapply find_Some_make_map_iff; eauto.
    solve [eapply mapM_length; eauto].
    intros k' [Hvs Hfk'].
    eapply find_Some_make_map_iff in Hfk'; eauto.
    destruct Hfk' as [i' [Hk' Hin']].
    copy_as Hmm Hmm'; eapply mapM_nth_error_1 in Hmm'; eauto.
    destruct Hmm' as [v' [? Hfk']].
    unif v'.
    solve [eapply related_no_alias; eauto].
    solve [eapply mapM_length; eauto].
    solve [eapply mapM_length; eauto].
    solve [eapply related_no_aliasM; eauto].
  Qed.

  Import WordMap.
  Import WordMapFacts.
  Require Import Bedrock.Platform.Facade.Facade.
  Lemma submap_represent p h1 h2 v : represent p (WordMap.find p h1) v -> h1 <= h2 -> represent p (WordMap.find p h2) v.
  Proof.
    intros Hpr Hsm.
    destruct v as [w | a]; simpl in *.
    eauto.
    eapply submap_find; eauto.
  Qed.
  Lemma not_reachable_iff ks st vs h input k a : related st (vs, h) -> mapM (sel st) ks = Some input -> StringMap.find k st = Some (ADT a) -> (not_reachable k ks input <-> ~ WordMap.In (vs k) (reachable_heap vs ks input)).
  Proof.
    intros Hr Hmm Hf.
    unfold not_reachable.
    split.
    intros Hnr.
    nintro.
    eapply in_reachable_heap_iff in H.
    2 : solve [eapply mapM_length; eauto].
    destruct H as [i [k' [a' [Hk' [Hi Hp]]]]].
    eapply mapM_nth_error_1 in Hmm; eauto.
    destruct Hmm as [v [Hi' Hf']].
    unif v.
    assert (k = k').
    eapply related_no_alias; eauto.
    subst.
    eapply Hnr in Hk'.
    destruct Hk' as [w Hi'].
    rewrite Hi in Hi'; discriminate.

    intros Hni i Hk.
    contradict Hni.
    eapply in_reachable_heap_iff.
    solve [eapply mapM_length; eauto].
    eapply mapM_nth_error_1 in Hmm; eauto.
    destruct Hmm as [v [Hi' Hf']].
    unfold sel in *.
    unif v.
    exists i, k, a; eauto.
  Qed.
  Arguments direct_sum_submap [_] _ _ _ _.
  Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
  Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.
  Lemma not_reachable_add_remove_many k ks ins outs h :
    NoDup ks ->
    length ks = length ins ->
    length ks = length outs ->
    not_reachable (ADTValue := ADTValue) k ks ins ->
    StringMap.find k (add_remove_many ks ins outs h) = StringMap.find k h.
  Proof.
    intros Hnd Hlki Hlko Hnr.
    eapply option_univalence.
    intros v; split; intros Hf.
    eapply find_Some_add_remove_many in Hf; eauto.
    destruct Hf as [[Hnr' Hf] | [i [a [Hk [Hi Ho]]]]].
    eauto.
    unfold not_reachable in *.
    eapply Hnr in Hk.
    destruct Hk as [w Hw].
    rewrite Hi in Hw; discriminate.
    eapply find_Some_add_remove_many; eauto.
  Qed.

  Import Semantics.

  Arguments store_out {_} _ _.
  Arguments ADTOut {_} _.
  Lemma good_input_mapM args :
    forall words cinput input h h2 st vs,
      Forall (word_adt_match h) (combine words cinput) ->
      length words = length cinput ->
      h2 <= h ->
      related st (vs, h2) ->
      List.map (fun x => vs x) args = words ->
      mapM (sel st) args = Some input ->
            let input' := cinput in
            same_types input input' ->
            input = input'.
  Proof.
    simpl; induction args; destruct words; destruct cinput; destruct input; try solve [simpl in *; intros; eauto; try discriminate].
    intros until 5; intros Hmm; intros; eapply mapM_length in Hmm; simpl in *; discriminate.
    rename a into x.
    rename v0 into v'.
    intros h h2 st vs Hfa Hl Hsm Hr Hm Hmm Hte.
    simpl in *.
    destruct (option_dec (sel st x)) as [[y Hy] | Hn].
    2 : rewrite Hn in *; discriminate.
    rewrite Hy in *.
    destruct (option_dec (mapM (sel st) args)) as [[ys Hys] | Hn].
    2 : rewrite Hn in *; discriminate.
    rewrite Hys in *.
    inject Hmm.
    inject Hm.
    inject Hl.
    inversion Hfa; subst.
    inversion Hte; subst.
    f_equal.
    2 : solve [eapply IHargs; eauto].
    eapply Hr in Hy; simpl in *.
    unfold word_adt_match in H2.
    destruct v' as [w | a]; simpl in *.
    subst.
    destruct v as [w' | a']; simpl in *.
    subst; eauto.
    intuition.
    destruct v as [w' | a']; simpl in *.
    intuition.
    eapply submap_find in Hy; eauto.
    unfold Locals.sel in *.
    unif a'.
    eauto.
  Qed.
  Lemma NoDup_no_alias st vs h args words cinput input words_cinput :
    related st (vs, h) ->
    NoDup args ->
    List.map (fun x => vs x) args = words ->
    input = cinput ->
    mapM (sel st) args = Some input ->
    words_cinput = combine words cinput ->
    no_alias words_cinput.
  Proof.
    intros Hr Hnd Hm Hid Hmm Hwid.
    subst.
    unfold no_alias.
    intros i j p ai aj Hi Hj.
    eapply nth_error_combine_elim in Hi; eauto.
    destruct Hi as [Hai Hii].
    eapply nth_error_combine_elim in Hj; eauto.
    destruct Hj as [Haj Hij].
    eapply nth_error_map_elim in Hai; eauto.
    destruct Hai as [xi [Hai ?]]; subst.
    eapply nth_error_map_elim in Haj; eauto.
    destruct Haj as [xj [Haj ?]]; subst.
    copy_as Hai Hai'; eapply mapM_nth_error_1 in Hai'; eauto.
    destruct Hai' as [vi [Hii' Hvi]].
    unif vi; simpl in *.
    copy_as Haj Haj'; eapply mapM_nth_error_1 in Haj'; eauto.
    destruct Haj' as [vj [Hij' Hvj]].
    unif vj; simpl in *.
    assert (xi = xj) by (eapply related_no_alias; eauto).
    subst; eapply NoDup_nth_error in Hnd; eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.SemanticsFacts7.
  Lemma not_in_not_reachable_p st vs h args words cinput p :
    related st (vs, h) ->
    List.map (fun x => vs x) args = words ->
    mapM (sel st) args = Some cinput ->
    ~ In p h ->
    not_reachable_p p (combine words cinput).
  Proof.
    intros Hr Hm Hmm Hni.
    unfold not_reachable_p.
    intros i v Hi.
    eapply nth_error_combine_elim in Hi.
    destruct Hi as [Hw Hi].
    eapply map_nth_error_2 in Hm; eauto.
    destruct Hm as [a [Ha Hp]].
    subst.
    eapply mapM_nth_error_1 in Hmm; eauto.
    destruct Hmm as [b [Hi' Hs]].
    unif b.
    destruct v; simpl in *.
    eexists; eauto.
    eapply Hr in Hs; simpl in *.
    contradict Hni.
    eapply find_Some_in; eauto.
  Qed.

  Lemma not_reachable_p_not_reachable (st : Facade.State ADTValue) vs args words cinput x :
    List.map (fun x => vs x) args = words ->
    mapM (sel st) args = Some cinput ->
    not_reachable_p (vs x) (combine words cinput) ->
    not_reachable x args cinput.
  Proof.
    intros Hm Hmm.
    intros Hnr; unfold not_reachable_p, not_reachable in *.
    intros i Hi.
    eapply map_nth_error_1 in Hm; eauto.
    eapply mapM_nth_error_1 in Hmm; eauto.
    openhyp; rename x0 into v.
    set (p := vs x) in *.
    edestruct Hnr.
    eapply nth_error_combine; eauto.
    subst; rename x0 into w.
    exists w.
    eauto.
  Qed.

  Lemma not_reachable_not_reachable_p st vs h args words cinput x a :
    related st (vs, h) ->
    NoDup args ->
    List.map (fun x => vs x) args = words ->
    mapM (sel st) args = Some cinput ->
    StringMap.find x st = Some (ADT a) ->
    not_reachable x args cinput ->
    not_reachable_p (vs x) (combine words cinput).
  Proof.
    intros Hr Hnd Hm Hmm Hf.
    intros Hnr; unfold not_reachable_p, not_reachable in *.
    intros i v Hi.
    eapply nth_error_combine_elim in Hi.
    openhyp.
    eapply map_nth_error_2 in Hm; eauto.
    openhyp; subst.
    rename x0 into x'.
    eapply mapM_nth_error_1 in Hmm; eauto.
    openhyp; subst.
    rename x0 into v'.
    unif v'.
    destruct v; simpl in *.
    eexists; eauto.
    assert (x = x').
    eapply related_no_alias; eauto.
    subst.
    eapply Hnr in H1.
    openhyp; subst.
    rewrite H1 in H0.
    simpl in *; discriminate.
  Qed.

  Lemma add_remove_many_fold_store_out_iff :
    forall st vs h2 args triples words cinput coutput input h h' p a,
      related st (vs, h2) ->
      NoDup args ->
      words = List.map (@Word _) triples ->
      cinput = List.map (@ADTIn _) triples ->
      coutput = List.map (@ADTOut _) triples ->
      input = cinput ->
          List.map (fun x => vs x) args = words ->
          mapM (sel st) args = Some input ->
          h2 <= h ->
          let h1 := h - h2 in
          h' == fold_left store_out triples h ->
          h1 <= h' ->
          ((exists x,
              p = Locals.sel vs x /\
              StringMap.find x (add_remove_many args input (wrap_output coutput) st) = Some (ADT a)) <->
           find p (h' - h1) = Some a).
  Proof.
    intros st vs h2 args triples words cinput coutput input h h' p a Hr Hnd Hw Hci Hco Hi Hm Hmm Hsm2 h1 He Hsm1'.
    assert (Hna : no_alias (combine words cinput)) by (eapply NoDup_no_alias; eauto).
    assert (Hsm1 : h1 <= h) by eapply diff_submap.
    assert (Hd : Disjoint h1 h2) by eapply diff_disjoint.
    assert (Hds : direct_sum h1 h2 h) by (eapply diff_direct_sum; eauto).

    rewrite He.
    erewrite (@split_triples' _ triples) by eauto.
    split; intro Hf.

    (* direction 1 *)
    destruct Hf as [x Hf].
    destruct Hf as [Hp Hf].
    eapply find_Some_add_remove_many in Hf.
    openhyp.

    (* not_reachable *)
    unfold_related Hr.
    copy_as H0 H00; eapply H1 in H0; simpl in *.
    eapply diff_find_Some_iff.
    split.

    eapply find_Some_fold_store_out.
    solve [eauto].
    solve [subst; rewrite combine_length_eq; repeat rewrite map_length; eauto].
    left.
    split.
    subst; eapply not_reachable_not_reachable_p; eauto.
    solve [subst; eauto].

    subst; eapply Disjoint_in_not.
    solve [eapply Disjoint_sym; eauto].
    solve [eapply find_Some_in; eauto].

    (* reachable *)
    rename x0 into i.
    rename a into a'.
    rename x1 into a.
    eapply mapM_nth_error_2 in Hmm; eauto; openhyp.
    unif x0.
    eapply nth_error_map_elim in H0; openhyp.
    destruct x0; simpl in *.
    subst.
    unfold wrap_output in H1; eapply nth_error_map_elim in H1; openhyp.
    destruct x0; simpl in *.
    2 : discriminate.
    inject H2.
    eapply nth_error_map_elim in H1; openhyp.
    unif x0; simpl in *; subst.
    eapply map_eq_nth_error_1 in Hm; [ | eauto ..]; openhyp.
    unif x0; simpl in *; subst.

    unfold_related Hr.
    eapply H1 in H3; simpl in *.
    eapply diff_find_Some_iff.
    split.

    eapply find_Some_fold_store_out.
    solve [eauto].
    solve [subst; rewrite combine_length_eq; repeat rewrite map_length; eauto].
    right.
    exists i; exists a.
    unfold Locals.sel in *.
    split.

    solve [erewrite nth_error_combine; eauto; erewrite map_nth_error by eauto; simpl; eauto].
    solve [erewrite map_nth_error by eauto; simpl; eauto].

    subst; eapply Disjoint_in_not.
    solve [eapply Disjoint_sym; eauto].
    solve [eapply find_Some_in; eauto].

    solve [eauto].
    solve [subst; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
    solve [subst; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].

    (* direction 2 *)
    eapply diff_find_Some_iff in Hf; openhyp.
    eapply find_Some_fold_store_out in H.
    openhyp.

    (* p is an address not affected by the call *)
    eapply find_Some_direct_sum in H1; [ | eauto .. ].
    openhyp.
    solve [contradict H0; eapply find_Some_in; eauto].
    unfold_related Hr.
    eapply H3 in H1; simpl in *.
    openhyp'.
    exists x.
    split.
    eauto.
    eapply find_Some_add_remove_many.
    solve [eauto].
    solve [subst; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
    solve [subst; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
    left.
    split.
    subst; eapply not_reachable_p_not_reachable; eauto.
    solve [eauto].

    (* p is the address of an output ADT object (but not the returned ADT object) *)
    rename x into i.
    rename x0 into a0.
    eapply nth_error_combine_elim in H; openhyp.
    subst.
    eapply nth_error_map_elim in H; openhyp.
    destruct x; simpl in *; subst.
    eapply nth_error_map_elim in H2; openhyp.
    unif x; simpl in *; subst.
    eapply nth_error_map_elim in H1; openhyp.
    unif x; simpl in *; subst.
    eapply mapM_nth_error_2 in Hmm.
    2 : solve [repeat eapply map_nth_error; eauto].
    simpl in *.
    openhyp.
    copy_as Hm Hm'; eapply map_eq_nth_error_1 in Hm'; [ | eauto ..]; openhyp.
    unif x0; simpl in *; subst.
    exists x.
    split.
    eauto.
    eapply find_Some_add_remove_many.
    solve [eauto].
    solve [repeat rewrite map_length; eapply map_eq_length_eq; eauto].
    solve [unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
    right.
    exists i; exists a0.
    split.
    eauto.
    split.
    solve [repeat erewrite map_nth_error; eauto; simpl; eauto].
    solve [unfold wrap_output; repeat erewrite map_nth_error; eauto; simpl; eauto].
    solve [eauto].
    solve [subst; rewrite combine_length_eq; repeat rewrite map_length; eauto].

  Qed.

  Lemma add_remove_many_fold_store_out :
    forall st vs h2 args triples words cinput coutput input h h' x p a,
      related st (vs, h2) ->
      NoDup args ->
      words = List.map (@Word _) triples ->
      cinput = List.map (@ADTIn _) triples ->
      coutput = List.map (@ADTOut _) triples ->
      input = cinput ->
          List.map (fun x => vs x) args = words ->
          mapM (sel st) args = Some input ->
          h2 <= h ->
          let h1 := h - h2 in
          h' == fold_left store_out triples h ->
          h1 <= h' ->
          p = Locals.sel vs x ->
          StringMap.find x (add_remove_many args input (wrap_output coutput) st) = Some (ADT a) ->
          find p (h' - h1) = Some a.
  Proof.
    intros.
    eapply add_remove_many_fold_store_out_iff; eauto.
  Qed.

  Import Facade.

  Ltac pick_related := try match goal with | |- related _ _ => eauto end.

  Infix "===" := (@StringMapFacts.M.Equal _) (at level 70).
  Hint Extern 0 (_ === _) => reflexivity.
  Lemma related_Equal_1 st vs h st' vs' h' : st === st' -> (forall x, Locals.sel vs x = Locals.sel vs' x) -> h == h' -> related st (vs, h) -> related st' (vs', h').
  Proof.
    unfold related; intros Hst Hvs Hh; intros [Hr1 Hr2]; simpl in *.
    split.
    intros k v Hfk.
    rewrite <- Hst in Hfk.
    rewrite <- Hh.
    rewrite <- Hvs.
    eauto.
    intros p a Hfp.
    rewrite <- Hh in Hfp.
    eapply Hr2 in Hfp.
    destruct Hfp as [k [Hex Hu]].
    exists k.
    split.
    rewrite <- Hst.
    rewrite <- Hvs.
    eauto.
    intros k'.
    rewrite <- Hst.
    rewrite <- Hvs.
    eauto.
  Qed.

  Lemma related_Equal st vs h st' vs' h' : st === st' -> (forall x, Locals.sel vs x = Locals.sel vs' x) -> h == h' -> (related st (vs, h) <-> related st' (vs', h')).
  Proof.
    intros Hst Hvs Hh; split; intros Hr.
    eapply related_Equal_1; eauto.
    eapply related_Equal_1; pick_related; eauto.
    symmetry; eauto.
    symmetry; eauto.
  Qed.

  Definition new_adt_no_pollute s_st vs s_st' vs' h := forall x, @is_mapsto_adt ADTValue x s_st = false \/ is_mapsto_adt x s_st = true /\ Locals.sel vs x <> Locals.sel vs' x -> @is_mapsto_adt ADTValue x s_st' = true -> ~ @In ADTValue (Locals.sel vs' x) h.
  Lemma new_adt_no_pollute_seq st vs st' vs' st'' vs'' h h' h'' : new_adt_no_pollute st vs st' vs' h -> new_adt_no_pollute st' vs' st'' vs'' h' -> h == h'' -> h' == h'' -> new_adt_no_pollute st vs st'' vs'' h''.
  Proof.
    unfold new_adt_no_pollute; intros Hanew Hbnew Hheq Hheq' x Hmt Hmt''.
    unfold Locals.sel in *.
    destruct (boolcase (is_mapsto_adt x st')) as [Hmt' | Hmtf'].
    destruct (Word.weq (vs' x) (vs'' x)) as [Heq | Hne].
    rewrite <- Heq in *.
    rewrite <- Hheq.
    solve [eapply Hanew; eauto].
    eapply Hbnew in Hmt''.
    rewrite <- Hheq'.
    solve [eauto].
    solve [right; eauto].
    eapply Hbnew in Hmt''.
    rewrite <- Hheq'.
    solve [eauto].
    solve [left; eauto].
  Qed.

  Lemma related_add_sca st vs h lhs w h' : related st (vs, h) -> not_mapsto_adt lhs st = true -> h' == h -> related (StringMap.add lhs (SCA _ w) st) (Locals.upd vs lhs w, h').
  Proof.
    intros Hr Hnmt Hheq.
    unfold related; simpl in *.
    split.
    intros x v Hfx.
    destruct (string_dec x lhs) as [Heq | Hne].
    subst.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject Hfx; simpl in *.
    rewrite Locals.sel_upd_eq in * by eauto.
    eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    rewrite Locals.sel_upd_ne in * by eauto.
    eapply Hr in Hfx; simpl in *.
    solve [rewrite Hheq; eauto].

    intros p a Hfp.
    rewrite Hheq in Hfp.
    eapply Hr in Hfp.
    simpl in *.
    destruct Hfp as [x [[Hvs Hfx] Hu]].
    subst.
    destruct (string_dec x lhs) as [Heq | Hne].
    subst.
    eapply not_mapsto_adt_find in Hfx; eauto.
    openhyp; discriminate.
    exists x.
    split.
    rewrite Locals.sel_upd_ne in * by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    eauto.
    intros x' [Hvs Hfx'].
    destruct (string_dec x' lhs) as [Heq' | Hne'].
    subst.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    discriminate.
    rewrite Locals.sel_upd_ne in * by eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    eauto.
  Qed.

  Lemma new_adt_no_pollute_add_sca st vs lhs w1 w2 h : new_adt_no_pollute st vs (StringMap.add lhs (SCA _ w1) st) (Locals.upd vs lhs w2) h.
  Proof.
    unfold new_adt_no_pollute.
    intros x Hmt Hmt'.
    destruct (string_dec x lhs) as [Heq | Hne].
    subst.
    rewrite Locals.sel_upd_eq in * by eauto.
    rewrite is_mapsto_adt_eq_sca in *.
    discriminate.
    rewrite Locals.sel_upd_ne in * by eauto.
    rewrite is_mapsto_adt_neq in * by eauto.
    intros; openhyp; intuition.
    rewrite H in Hmt'.
    discriminate.
  Qed.

  Theorem compile_runsto :
    forall t t_env t_st t_st',
      CitoRunsTo t_env t t_st t_st' ->
      forall s,
        t = compile s ->
        (* h1 : the heap portion that this program is allowed to change *)
        forall h1,
          h1 <= snd t_st ->
          forall s_st,
            related s_st (fst t_st, h1) ->
            forall s_env,
              cenv_impls_env t_env s_env ->
              Safe s_env s s_st ->
              exists s_st',
                RunsTo s_env s s_st s_st' /\
                (* h2 : the frame heap (the outside portion that won't be touched by this program *)
                let h2 := snd t_st - h1 in
                (* the frame heap will be intacked in the final state *)
                h2 <= snd t_st' /\
                (* variables not appearing as LHS won't change value in Cito state *)
                (forall x, ~ StringSet.In x (assigned s) -> Locals.sel (fst t_st) x = Locals.sel (fst t_st') x) /\
                (* newly allocated ADT objects during this program's execution won't collide with the frame heap *)
                (forall x, is_mapsto_adt x s_st = false \/ is_mapsto_adt x s_st = true /\ Locals.sel (fst t_st) x <> Locals.sel (fst t_st') x -> is_mapsto_adt x s_st' = true -> ~ In (Locals.sel (fst t_st') x) h2) /\
                (* main result: final source-level and target level states are related *)
                related s_st' (fst t_st', snd t_st' - h2).
  Proof.
    induction 1; simpl; intros; destruct s; simpl in *; intros; try discriminate.

    Focus 7.
    {
      (* call-operational *)
      unfold_all.
      inject H2.
      destruct (option_dec (Word2Spec s_env (SemanticsExpr.eval (fst v) e))); simpl in *.
      Focus 2.
      {
        inversion H6; subst.
        replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
        rewrite e0 in *; simpl in *; discriminate.
        replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
        rewrite e0 in *; simpl in *; discriminate.
      }
      Unfocus.
      destruct s0.
      copy_as e0 e0'.
      eapply H5 in e0'.
      rename H5 into Henv.
      rewrite e0' in *; simpl in *.
      inject H.
      destruct x; simpl in *.
      destruct a; simpl in *; simpl in *; discriminate.
      unfold compile_op in *; simpl in *.
      inject H2; simpl in *.
      inversion H6; subst.
      {
        replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
        rewrite e0 in *.
        discriminate.
      }
      unfold_all.
      replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
      rewrite e0 in *.
      inject H9.

      edestruct IHRunsTo; [ .. | clear IHRunsTo].
      solve [eauto].
      3 : solve [eauto].
      3 : solve [eauto].
      Focus 3.
      openhyp.
      copy H; eapply H15 in H.
      openhyp.
      eapply ex_up in H.
      openhyp.
      eexists.
      split.
      eapply RunsToCallOp.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      reflexivity.
      Unfocus.

      {
        instantiate (1 := reachable_heap (fst v) l input).
        eapply reachable_submap_related in H4; openhyp; eauto.
        eapply submap_trans; eauto.
      }
      {
        eapply reachable_submap_related in H4; openhyp; eauto.
        eapply change_var_names; eauto.
        - rewrite map_map in H0; simpl in *; eauto.
        - eapply NoDup_ArgVars; eauto.
        - eapply mapM_length; eauto.
      }

      split' Hsm.
      {
        eapply submap_trans; eauto.
        eapply submap_diff; eauto.
        eapply reachable_submap_related in H4; openhyp; eauto.
      }

      split.
      {
        intros.
        eapply StringSetFacts.singleton_not_iff in H18.
        rewrite Locals.sel_upd_ne by eauto.
        eauto.
      }

      split.
      {
        intros.
        destruct (string_dec x1 s).
        subst.
        eapply is_mapsto_adt_iff in H19.
        destruct H19 as [a H19].
        rewrite StringMapFacts.add_eq_o in * by eauto.
        inject H19.
        rewrite Locals.sel_upd_eq in * by eauto.
        eapply submap_not_in.
        2 : eapply H9.
        eapply submap_diff; eauto.
        solve [eapply reachable_submap_related in H4; openhyp; eauto].
        left.
        eapply is_mapsto_adt_false_iff.
        eapply not_in_no_adt.
        eapply StringMapFacts.make_map_not_in.
        solve [eapply not_incl_spec].
        eapply is_mapsto_adt_iff.
        solve [eexists; eauto].

        eapply is_mapsto_adt_iff in H19.
        destruct H19 as [a H19].
        rewrite StringMapFacts.add_neq_o in * by eauto.
        rewrite Locals.sel_upd_ne  in * by eauto.
        destruct H18 as [H18 | H18].
        eapply is_mapsto_adt_false_iff in H18.
        nintro; eapply H18; clear H18.
        eapply find_ADT_add_remove_many; eauto.
        solve [rewrite map_length; eapply map_eq_length_eq in H0; eauto].
        solve [intuition].
      }

      copy H4; eapply reachable_submap_related in H4; openhyp; eauto.
      destruct v as [vs h]; simpl in *.
      set (h2 := h - h1) in *.
      unfold related; simpl.
      split.

      {
        (* related (1) *)
        rewrite map_map in H0; simpl in *.
        rename x into st_callee'.
        intros x v Hf.

        rename l into args.
        rename s into lhs.
        rename h into h123.
        rename h1 into h12.
        set (h3 := reachable_heap vs args input) in *.
        set (h23 := h123 - h3) in *.

        destruct (string_dec x lhs).
        {
          (* x = lhs *)
          subst.
          rewrite StringMapFacts.add_eq_o in * by eauto.
          rewrite Locals.sel_upd_eq by eauto.
          inject Hf.
          unfold_related H13.
          set (retp := Locals.sel vs_callee' (RetVar spec)) in *.
          eapply H13 in H.
          eapply submap_represent; eauto.
          solve [eapply submap_diff; eauto; eapply submap_diff; eauto].
        }

        (* x <> lhs *)
        rewrite Locals.sel_upd_ne by eauto.
        rewrite StringMapFacts.add_neq_o in * by eauto.
        eapply find_Some_add_remove_many in Hf.
        {
          openhyp.
          {
            (* not reachable *)
            unfold_related H18.
            copy_as H21 Hf; eapply H18 in H21.
            destruct v as [w | a]; simpl in *.
            eauto.
            erewrite <- diff_o in H21.
            Focus 2.
            eapply not_reachable_iff; eauto.
            eapply submap_find; eauto.
            erewrite submap_diff_diff; eauto.
            eapply submap_restrict.
            solve [eauto].
          }

          (* not reachable *)
          symmetry in H0; eapply map_eq_nth_error_1 in H0; [ | eauto ..].
          openhyp.
          unfold Locals.sel in *.
          rewrite H23.
          assert (Hvse : vs_callee x3 = vs_callee' x3).
          eapply H5.
          eapply in_args_not_assigned; eauto.
          solve [eapply Locals.nth_error_In; eauto].
          subst' Hvse.
          rename x1 into i.
          erewrite map_nth_error in H22 by eauto.
          inject H22.
          unfold_related H13.
          eapply H13 in H24.
          unfold Locals.sel in *.
          set (p := vs_callee' x3) in *.
          eapply submap_represent; eauto.
          eapply submap_diff; eauto.
          solve [eapply submap_diff; eauto].
        }
        {
          solve [eauto].
        }
        {
          solve [eapply mapM_length; eauto].
        }
        {
          solve [rewrite map_length; eapply map_eq_length_eq in H0; eauto].
        }
      }

      (* related (2) *)
      rewrite map_map in H0; simpl in *.
      intros.
      rename s into lhs.
      rename l into args.
      (* set up the heap partitioning :
       h3 : the heap portion passed to the callee, i.e. reachable by arguments referring to ADT objects;
       h2 : the heap portion accessible by the caller, modulo h3;
       h1 : the heap portion not accessible by the caller.
       h1, h2 and h3 are mutually disjoint and cover the whole heap h123.
       *)
      rename h into h123.
      rename h1 into h23.
      rename h2 into h1.
      set (h3 := reachable_heap vs args input) in *.
      set (h12 := h123 - h3) in *.
      set (h2 := h12 - h1) in *.
      set (h3' := heap' - h12) in *.
      set (h23' := heap' - h1) in *.
      assert (direct_sum h1 h2 h12) by (eapply direct_sum_sym; eapply diff_direct_sum; eauto; eapply submap_diff; eauto).

      assert (direct_sum h1 h23 h123) by (eapply diff_direct_sum; eauto).
      assert (direct_sum h12 h3 h123).
      {
        eapply diff_direct_sum; eauto.
        eapply submap_trans.
        eauto.
        Arguments direct_sum_submap [_] _ _ _ _.
        solve [eapply (direct_sum_submap h1 h23); eauto].
      }
      assert (Hd13 : Disjoint h1 h3).
      {
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
        eapply (submap_disjoint_1 h12 h3).
        eapply direct_sum_disjoint; eauto.
        solve [eapply (direct_sum_submap h1 h2); eauto].
      }
      assert (direct_sum h2 h3 h23).
      {
        unfold_all.
        rewrite diff_swap.
        rewrite diff_submap_cancel by (eapply (direct_sum_submap _ h23); eauto).
        solve [eapply diff_direct_sum; eauto].
      }
      assert (direct_sum h2 h3' h23').
      {
        unfold_all.
        rewrite diff_swap.
        rewrite diff_submap_cancel by (eapply (direct_sum_submap _ h23); eauto).
        eapply direct_sum_submap_submap.
        solve [eapply submap_diff; eauto].
        solve [eauto].
        solve [erewrite submap_diff_diff; eauto].
      }

      (* case analysis on which partition p falls into *)
      eapply find_Some_direct_sum in H20; eauto; openhyp.

      {
        (* p is in h2 *)
        unfold_related H18.
        copy_as H20 Hf; eapply submap_find in H20.
        2 : eapply (direct_sum_submap h2 h3); eauto.
        eapply H27 in H20.

        openhyp'.
        rename x1 into x3.
        destruct (string_dec x3 lhs).
        {
        subst; solve [contradict H12; eapply not_mapsto_adt_not_true_iff; eexists; eauto].
        }
        (* x3 <> lhs *)
        exists x3.
        split.
        {
          (* exists *)
          rewrite Locals.sel_upd_ne by eauto.
          rewrite StringMapFacts.add_neq_o by eauto.
          split.
          eauto.
          eapply find_Some_add_remove_many.
          solve [eauto].
          solve [eapply mapM_length; eauto].
          rewrite map_length.
          solve [eapply map_eq_length_eq in H0; eauto].
          left.
          split.
          2 : solve [eauto].
          eapply not_reachable_iff; eauto.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.
          eapply (direct_sum_in_not h2 h3); eauto.
          solve [subst; eapply find_Some_in; eauto].
        }

        (* unique *)
        intros.
        openhyp.
        destruct (string_dec x' lhs).
        {
          (* x' = lhs *)
          subst.
          rewrite StringMapFacts.add_eq_o in *.
          rewrite Locals.sel_upd_eq in * by eauto.
          inject H31.
          symmetry in H30; subst' H30.
          (* (vs_callee' RetVar) is a newly allocated ADT object, so it shouldn't be in h2 *)
          assert (Hni : ~ In (vs_callee' (RetVar spec)) h12).
          eapply H9.
          left.
          eapply is_mapsto_adt_false_iff.
          eapply not_in_no_adt.
          solve [eapply StringMapFacts.make_map_not_in; eapply not_incl_spec].
          eapply is_mapsto_adt_iff.
          solve [eexists; eauto].
          contradict Hni.
          eapply submap_in; eauto.
          solve [eapply (direct_sum_submap h1 h2); eauto].
          solve [eapply find_Some_in; eauto].
          solve [eauto].
        }

        (* x' <> lhs *)
        rewrite StringMapFacts.add_neq_o in * by eauto.
        rewrite Locals.sel_upd_ne in * by eauto.
        eapply H28.
        split.
        eauto.
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.
        erewrite <- not_reachable_add_remove_many; eauto.
        solve [eapply mapM_length; eauto].
        solve [rewrite map_length; eapply map_eq_length_eq in H0; eauto].
        eapply find_ADT_add_remove_many in H31; eauto.
        openhyp.
        eapply not_reachable_iff; eauto.
        eapply (direct_sum_in_not h2 h3); eauto.
        subst.
        unfold Locals.sel in *.
        subst' H30.
        solve [eapply find_Some_in; eauto].
        solve [rewrite map_length; eapply map_eq_length_eq in H0; eauto].
      }

      (* p is in h3' *)
      unfold_related H13.
      copy_as H20 Hf; eapply H27 in H20.
      openhyp'.
      rename x1 into x3.
      rename x into st_callee'.
      (* Since there is no memory leak, ADT-holding x3 can only be RetVar or an ADT-holding argument *)
      copy_as H29 Hf3; eapply H17 in H29.
      openhyp.

      {
        (* x3 is RetVar (i.e. p is the address of the returned ADT object) *)
        subst.
        unfold sel in *.
        unif x0.
        exists lhs.
        split.
        {
          (* exists *)
          rewrite Locals.sel_upd_eq by eauto.
          rewrite StringMapFacts.add_eq_o by eauto.
          eauto.
        }

        (* unique *)
        intros.
        openhyp.
        destruct (string_dec x' lhs).
        {
          eauto.
        }
        (* x' <> lhs *)
        rewrite Locals.sel_upd_ne in * by eauto.
        rewrite StringMapFacts.add_neq_o in * by eauto.
        unfold Locals.sel in *.
        symmetry in H; subst' H.
        eapply find_Some_add_remove_many in H20.
        {
          openhyp.
          {
            (* not_reachable *)
            unfold_related H18.
            copy_as H20 Hf'; eapply H18 in H20; simpl in *.
            eapply find_Some_direct_sum in H20; eauto; openhyp.
            eapply find_Some_in in H20.
            eapply find_Some_in in Hf.
            contradict Hf.
            eapply (direct_sum_in_not h2 h3'); eauto.
            eapply not_reachable_iff in H; eauto.
            contradict H.
            solve [eapply find_Some_in; eauto].
          }
          (* reachable *)
          eapply nth_error_map_elim in H29.
          openhyp.
          eapply map_eq_nth_error_1 in H0; [ | eauto ..].
          openhyp.
          unfold StringMap.key in *.
          unif x2.
          unfold Locals.sel in *.
          assert (RetVar spec = x1).
          eapply H28.
          split.
          rewrite <- H31.
          symmetry; eapply H5.
          eapply in_args_not_assigned; eauto.
          eapply Locals.nth_error_In; eauto.
          solve [eauto].
          subst.
          eapply Locals.nth_error_In in H29; eauto.
          contradict H29.
          solve [eapply not_incl_spec].
        }
        {
          solve [eauto].
        }
        {
          solve [eapply mapM_length; eauto].
        }
        {
          solve [rewrite map_length; eapply map_eq_length_eq in H0; eauto].
        }
      }

      (* x3 is an arg referring to an ADT object (i.e. p is the address of an output ADT object, not the returned ADT object) *)
      rename x into i.
      copy_as H0 H00; eapply map_eq_nth_error_1 in H0; [ | eauto ..].
      openhyp.
      rename x into arg.
      destruct (string_dec arg lhs).
      {
        (* arg = lhs *)
        subst.
        contradict H12.
        eapply not_mapsto_adt_not_true_iff.
        eapply mapM_nth_error_1 in H11; eauto.
        openhyp.
        unif x.
        solve [eexists; eauto].
      }
      (* arg <> lhs *)
      exists arg.
      split.
      {
        (* exists *)
        rewrite Locals.sel_upd_ne by eauto.
        rewrite StringMapFacts.add_neq_o in * by eauto.
        unfold Locals.sel in *.
        split.
        subst.
        rewrite <- H31.
        eapply H5.
        eapply in_args_not_assigned; eauto.
        eapply Locals.nth_error_In; eauto.

        eapply find_Some_add_remove_many.
        solve [eauto].
        solve [eapply mapM_length; eauto].
        solve [rewrite map_length; eapply map_eq_length_eq in H00; eauto].
        right.
        exists i, x1.
        split.
        eauto.
        split.
        eauto.
        erewrite map_nth_error by eauto.
        f_equal; solve [eauto].
      }

      (* unique *)
      intros.
      openhyp.
      destruct (string_dec x' lhs).
      {
        (* x' = lhs *)
        subst.
        rewrite Locals.sel_upd_eq in * by eauto.
        rewrite StringMapFacts.add_eq_o in * by eauto.
        inject H33.
        set (retp := Locals.sel vs_callee' (RetVar spec)) in *.
        set (p := Locals.sel vs_callee' x3) in *.
        assert (x3 = RetVar spec).
        eapply H28.
        solve [eauto].
        unfold_all; subst.
        eapply Locals.nth_error_In in H29; eauto.
        contradict H29.
        solve [eapply not_incl_spec].
      }
      (* x' <> lhs *)
      rewrite Locals.sel_upd_ne in * by eauto.
      rewrite StringMapFacts.add_neq_o in * by eauto.
      unfold Locals.sel in *; subst.
      assert (vs arg = vs x').
      rewrite H32.
      rewrite <- H31.
      eapply H5.
      eapply in_args_not_assigned; eauto.
      solve [eapply Locals.nth_error_In; eauto].
      copy_as H11 Hmm; eapply mapM_nth_error_1 in Hmm; eauto.
      openhyp.
      unif x.
      eapply find_ADT_add_remove_many in H33; eauto.
      openhyp.
      eapply (related_no_alias s_st); eauto.
      solve [rewrite map_length; eapply map_eq_length_eq in H00; eauto].
    }
    Unfocus.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.

    Focus 7.
    {
      (* call-axiomatic *)
      unfold_all.
      injection H6; intros; subst; clear H6.
      simpl in *.
      destruct (option_dec (Word2Spec s_env (SemanticsExpr.eval (fst v) e))).
      Focus 2.
      {
        inversion H10; subst.
        replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
        rewrite e0 in *; simpl in *; discriminate.
        replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
        rewrite e0 in *; simpl in *; discriminate.
      }
      Unfocus.
      destruct s0.
      rename H9 into Henv.
      copy_as e0 e0'.
      eapply Henv in e0'.
      rewrite e0' in *; simpl in *.
      inject H.
      destruct x; simpl in *.
      2 : discriminate.
      destruct a; simpl in *.
      injection H6; intros; subst; simpl in *; clear H6.

      inversion H10; subst.
      Focus 2.
      replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
      rewrite e0 in *.
      discriminate.

      unfold_all.
      replace f_w with (SemanticsExpr.eval (fst v) e) in * by  (eapply eval_ceval; eauto).
      rewrite e0 in *.
      inject H13.
      rewrite map_map in H0; simpl in *.

      rename l into args.
      destruct v as [vs h123]; simpl in *.
      rename h1 into h23.

      set (cinput := List.map (Semantics.ADTIn (ADTValue:=ADTValue)) triples) in *.
      set (coutput := List.map (Semantics.ADTOut (ADTValue:=ADTValue)) triples) in *.
      set (words := List.map (Semantics.Word (ADTValue:=ADTValue)) triples) in *.
      set (cinput_coutput := List.map (fun x => (Semantics.ADTIn x, Semantics.ADTOut x)) triples) in *.
      set (words_cinput := List.map (fun x => (Semantics.Word x, Semantics.ADTIn x)) triples) in *.
      assert (input = cinput).
      {
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.

        unfold_all.
        eapply good_input_mapM; eauto.
        solve [rewrite combine_map; destruct H1; eauto].
        solve [repeat rewrite map_length; eauto].
        eapply is_same_types_sound.
        eapply PreCondTypeConform; eauto.
        repeat rewrite map_length; eauto.
        eapply mapM_length in H14; eauto.
        eapply map_eq_length_eq in H0; eauto; rewrite <- H0.
        solve [eauto].
      }

      rewrite H in *.

      eexists.
      split.
      eapply RunsToCallAx.
      eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      simpl.
      eauto.
      instantiate (1 := coutput).
      unfold_all.
      repeat rewrite map_length; eauto.
      simpl.
      assert (combine cinput coutput = cinput_coutput) by (unfold_all; repeat rewrite map_map; rewrite combine_map; eauto).
      rewrite H6.
      eauto.
      reflexivity.

      assert (words_cinput = combine words cinput) by (unfold_all; rewrite combine_map; eauto).

      assert (no_alias words_cinput).
      {
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.

        eapply NoDup_no_alias; eauto.
        rewrite H.
        eauto.
      }

      set (h1 := h123 - h23) in *.
      assert (direct_sum h1 h23 h123) by (eapply diff_direct_sum; eauto).

      rename s into lhs.
      rename e into e_f.

      assert (h1 <= fold_left (store_out (ADTValue:=ADTValue)) triples h123).
      {
        unfold Submap.
        intros p a Hf.
        eapply diff_find_Some_iff in Hf.
        openhyp.

        rewrite (@split_triples _ triples words_cinput coutput) by eauto.

        eapply find_Some_fold_store_out.
        eauto.
        unfold_all; repeat rewrite map_length; eauto.
        rewrite H6.
        left.
        split.
        {
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.
          eapply not_in_not_reachable_p; eauto.
        }
        solve [eauto].
      }

      split.
      {
        (* h1 <= heap' *)
        rewrite H5.
        destruct ret; simpl in *.
        eauto.
        unfold separated in H4; simpl in *.
        openhyp.
        discriminate.
        eapply submap_trans.
        eauto.
        solve [eapply add_new_submap; eauto].
      }

      split.
      {
        (* no illegal local variable overwrite *)
        intros.
        eapply StringSetFacts.singleton_not_iff in H18.
        rewrite Locals.sel_upd_ne by eauto.
        solve [eauto].
      }

      split.
      {
        (* newly allocated objects won't sabotage frame heap *)
        intros.
        destruct (string_dec x lhs).
        {
          (* x = lhs *)
          rewrite e in *.
          eapply is_mapsto_adt_iff in H19.
          destruct H19 as [a H19].
          rewrite Locals.sel_upd_eq in * by eauto.
          rewrite StringMapFacts.add_eq_o in * by eauto.
          destruct ret; simpl in *.
          discriminate.
          inject H19.
          unfold separated in H4; simpl in *.
          destruct H4 as [H4 | H4].
          discriminate.
          solve [eapply submap_not_in; eauto].
        }
        (* x <> lhs *)
        eapply is_mapsto_adt_iff in H19.
        destruct H19 as [a H19].
        rewrite Locals.sel_upd_ne in * by eauto.
        rewrite StringMapFacts.add_neq_o in * by eauto.
        destruct H18 as [H18 | H18].
        eapply is_mapsto_adt_false_iff in H18.
        contradict H18.
        eapply find_ADT_add_remove_many; eauto.
        solve [subst; unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
        solve [intuition].
      }
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.

      (* related *)
      unfold related; simpl.
      split.
      {
        (* related (1) *)
        intros x v Hf.
        destruct (string_dec x lhs).
        {
          (* x = lhs *)
          subst' e.
          rewrite H5.
          rewrite Locals.sel_upd_eq in * by eauto; simpl.
          rewrite StringMapFacts.add_eq_o in * by eauto.
          inject Hf.
          rename v into ret.
          destruct ret; simpl in *.
          eauto.
          eapply diff_find_Some_iff.
          split.
          solve [rewrite add_eq_o in * by eauto; eauto].
          unfold separated in H4; simpl in *.
          openhyp.
          discriminate.
          solve [eapply submap_not_in; eauto].
        }
        (* x <> lhs *)
        rewrite Locals.sel_upd_ne by eauto.
        rewrite StringMapFacts.add_neq_o in * by eauto.
        destruct v; simpl in *.
        {
          (* v is scalar *)
          eapply find_Some_add_remove_many in Hf.
          openhyp.
          unfold_related H8.
          eapply H8 in H19; simpl in *.
          eauto.
          contradict H20.
          eapply wrap_output_not_sca; eauto.
          solve [eauto].
          solve [unfold_all; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
          solve [unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
        }

        (* v is ADT object *)
        rewrite H5.

        destruct (p_addr_ret_dec (Locals.sel vs x) addr ret).
        {
          destruct s; openhyp.
          subst; simpl in *.
          unfold separated in H4; simpl in *.
          openhyp.
          discriminate.
          contradict H.
          eapply add_remove_many_fold_store_out in Hf; eauto.
          eapply diff_find_Some_iff in Hf; openhyp.
          solve [eapply find_Some_in; eauto].
        }

        rewrite find_ret_doesn't_matter by eauto.
        solve [eapply add_remove_many_fold_store_out in Hf; eauto].
      }

      (* related (2) *)
      intros.
      rewrite H5 in H18.

      destruct (p_addr_ret_dec p addr ret).
      {
        (* p is the address of the return ADT object *)
        destruct s; openhyp.
        subst; simpl in *.
        eapply diff_find_Some_iff in H18; openhyp.
        rewrite add_eq_o in * by eauto.
        inject H.
        exists lhs.
        split.
        {
          (* exists *)
          rewrite Locals.sel_upd_eq by eauto.
          rewrite StringMapFacts.add_eq_o by eauto.
          eauto.
        }
        (* unique *)
        intros.
        openhyp.
        destruct (string_dec x' lhs).
        eauto.
        rewrite Locals.sel_upd_ne in * by eauto.
        rewrite StringMapFacts.add_neq_o in * by eauto.
        unfold separated in H4; simpl in *.
        openhyp.
        discriminate.
        contradict H4.
        subst.
        eapply add_remove_many_fold_store_out in H19; eauto.
        eapply diff_find_Some_iff in H19; openhyp.
        solve [eapply find_Some_in; eauto].
      }
      (* p is not the address of the return ADT object *)
      rewrite find_ret_doesn't_matter in H18 by eauto.
      eapply add_remove_many_fold_store_out_iff in H18; eauto.
      2 : solve [rewrite H; eauto].
      rewrite H in H18.
      openhyp.
      destruct (string_dec x lhs).
      {
        subst.
        contradict H16.
        eapply not_mapsto_adt_not_true_iff.
        eapply find_ADT_add_remove_many; eauto.
        solve [unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
      }
      exists x.
      split.
      {
        (* exists *)
        rewrite Locals.sel_upd_ne by eauto.
        rewrite StringMapFacts.add_neq_o by eauto.
        eauto.
      }
      (* unique *)
      intros.
      openhyp.
      destruct (string_dec x' lhs).
      subst' e.
      rewrite StringMapFacts.add_eq_o in * by eauto.
      rewrite Locals.sel_upd_eq in * by eauto.
      destruct ret; simpl in *.
      discriminate.
      inject H21.
      solve [unfold ret_doesn't_matter in *; simpl in *; openhyp; intuition; discriminate].
      rewrite StringMapFacts.add_neq_o in * by eauto.
      rewrite Locals.sel_upd_ne in * by eauto.
      eapply find_ADT_add_remove_many in H19; eauto; openhyp.
      eapply find_ADT_add_remove_many in H21; eauto; openhyp.
      solve [eapply related_no_alias; eauto].
      solve [unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
      solve [unfold_all; unfold wrap_output; repeat rewrite map_length; eapply map_eq_length_eq; eauto].
    }
    Unfocus.

    Focus 3.
    {
      (* if-true *)
      rename H1 into Hcomp.
      inject Hcomp.
      rename IHRunsTo into IHa.
      edestruct IHa as [s_st' [Hart [Hasm [Havs [Hanew Har]]]]]; clear IHa; eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eapply safe_if_true; eauto.
      eapply wneb_is_true; eauto.
      eapply safe_if_is_bool; eauto.
      openhyp.
      eexists.
      split.
      eapply RunsToIfTrue.
      eapply wneb_is_true; eauto.
      eapply safe_if_is_bool; eauto.
      eauto.
      split.
      eauto.
      split.
      intros s Hni.
      eapply Havs.
      not_not.
      solve [eapply StringSetFacts.union_iff; eauto].
      solve [eauto].
    }
    Unfocus.

    Focus 3.
    {
      (* if-false *)
      rename H1 into Hcomp.
      inject Hcomp.
      rename IHRunsTo into IHa.
      edestruct IHa as [s_st' [Hart [Hasm [Havs [Hanew Har]]]]]; clear IHa; eauto.
      eauto.
      eauto.
      eauto.
      eauto.
      eapply safe_if_false; eauto.
      eapply wneb_is_false; eauto.
      eapply safe_if_is_bool; eauto.
      openhyp.
      eexists.
      split.
      eapply RunsToIfFalse.
      eapply wneb_is_false; eauto.
      eapply safe_if_is_bool; eauto.
      eauto.
      split.
      eauto.
      split.
      intros s Hni.
      eapply Havs.
      solve [not_not; eapply StringSetFacts.union_iff; eauto].
      solve [eauto].
    }
    Unfocus.
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.

    Focus 2.
    {
      (* seq *)
      subst.
      rename H1 into Hcomp.
      inject Hcomp.
      rename s1 into a.
      rename s2 into b.
      destruct v as [vs h]; simpl in *.
      destruct v' as [vs' h']; simpl in *.
      destruct v'' as [vs'' h'']; simpl in *.
      rename h1 into h2.
      rename IHRunsTo1 into IHa.
      rename IHRunsTo2 into IHb.
      rename H into Hartt.
      rename H0 into Hbrtt.
      rename H2 into Hsm.
      rename H5 into Hsf.
      rename H3 into Hr.
      edestruct IHa as [s_st' [Hart [Hasm [Havs [Hanew Har]]]]]; clear IHa; eauto.
      eapply safe_seq_1; eauto.
      edestruct IHb as [s_st'' [Hbrt [Hbsm [Hbvs [Hbnew Hbr]]]]]; clear IHb; pick_related; eauto.
      solve [eapply diff_submap; eauto].
      eapply safe_seq_2; eauto.
      set (h1 := h - h2) in *.
      rewrite diff_submap_cancel in Hbsm by eauto.
      exists s_st''.
      split.
      eapply RunsToSeq; eauto.
      split.
      eauto.
      split.
      intros s Hni.
      etransitivity.
      eapply Havs.
      not_not; eapply StringSetFacts.union_iff; eauto.
      eapply Hbvs.
      not_not; eapply StringSetFacts.union_iff; eauto.
      split.
      eapply new_adt_no_pollute_seq; eauto.
      solve [rewrite diff_submap_cancel; eauto].
      eapply related_Equal; pick_related; eauto.
      solve [rewrite diff_submap_cancel; eauto].
    }
    Unfocus.

    Focus 2.
    {
      (* while-true *)
      subst.
      rename H2 into Hcomp.
      inject Hcomp.
      destruct v as [vs h]; simpl in *.
      destruct v' as [vs' h']; simpl in *.
      destruct v'' as [vs'' h'']; simpl in *.
      rename h1 into h2.
      rename e into cond.
      rename s into body.
      rename H into Hcondt.
      rename H3 into Hsm.
      rename H4 into Hr.
      rename H6 into Hsf.
      rename H0 into Hbrtt.
      rename H1 into Hlrtt.
      rename IHRunsTo1 into IHb.
      rename IHRunsTo2 into IHl.
      inversion Hsf as [ | | | | ? ? ? loop' Hcond Hsfb Hrtsf | | | | | ]; unfold_all; subst.
      edestruct IHb as [s_st' [Hbrt [Hbsm [Hbvs [Hbnew Hbr]]]]]; clear IHb; eauto.
      edestruct IHl as [s_st'' [Hlrt [Hlsm [Hlvs [Hlnew Hlr]]]]]; clear IHl; pick_related; eauto; simpl; eauto.
      solve [eapply diff_submap; eauto].
      rewrite diff_submap_cancel in Hlsm by eauto.
      exists s_st''.
      split.
      eapply RunsToWhileTrue; eauto.
      split.
      eauto.
      split.
      intros s Hni.
      etransitivity.
      eapply Hbvs.
      eauto.
      eapply Hlvs.
      simpl in *; eauto.
      split.
      eapply new_adt_no_pollute_seq; eauto.
      solve [rewrite diff_submap_cancel; eauto].
      eapply related_Equal; pick_related; eauto.
      solve [rewrite diff_submap_cancel; eauto].

      exfalso; eapply is_true_is_false; eauto.
      eapply wneb_is_true; eauto.
      eapply is_false_is_bool; eauto.
    }
    Unfocus.

    {
      (* skip *)
      exists s_st.
      split.
      eapply RunsToSkip.
      split.
      solve [eapply diff_submap; eauto].
      split.
      eauto.
      split.
      solve [intros; openhyp; intuition; rewrite H4 in H5; discriminate].
      eapply related_Equal; pick_related; eauto.
      solve [rewrite diff_submap_cancel; eauto].
    }

    {
      (* while-false *)
      subst.
      rename H0 into Hcomp.
      inject Hcomp.
      exists s_st.
      split.
      eapply RunsToWhileFalse.
      eapply wneb_is_false; eauto.
      solve [eapply safe_while_is_bool; eauto].
      split.
      solve [eapply diff_submap; eauto].
      split.
      eauto.
      split.
      intros; openhyp; intuition.
      rewrite H0 in H5.
      discriminate.
      eapply related_Equal; pick_related; eauto.
      solve [rewrite diff_submap_cancel; eauto].
    }
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.
        Arguments direct_sum_submap [_] _ _ _ _.
        Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.
          Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Arguments store_out {_} _ _.
    Arguments ADTOut {_} _.

    {
      (* label *)
      subst.
      rename H0 into Hcomp.
      inject Hcomp.
      rename s into lhs.
      rename g into lbl.
      destruct v as [vs h]; simpl in *.
      rename h1 into h2.
      rename H1 into Hsm.
      rename H4 into Hsf.
      rename H2 into Hr.
      rename H into Hlbl.
      inversion Hsf as [ | | | | | | | ? ? ? w' Hlbl' Hnmt | | ]; unfold_all; subst.
      copy_as Hlbl' Hlbl''.
      eapply H3 in Hlbl''.
      unif w'.
      eexists.
      split.
      eapply RunsToLabel; eauto.
      split.
      solve [eapply diff_submap; eauto].
      split.
      intros x Hni.
      eapply StringSetFacts.singleton_not_iff in Hni.
      solve [rewrite Locals.sel_upd_ne; eauto].
      split.
      solve [eapply new_adt_no_pollute_add_sca].
      eapply related_add_sca; eauto.
      solve [rewrite diff_submap_cancel; eauto].
    }

    {
      (* assign *)
      subst.
      unfold_all.
      rename H into Hcomp.
      inject Hcomp.
      rename s into lhs.
      rename e0 into e.
      destruct v as [vs h]; simpl in *.
      rename h1 into h2.
      rename H0 into Hsm.
      rename H3 into Hsf.
      rename H1 into Hr.
      inversion Hsf as [ | | | | | | ? ? ? w He Hnmt | | | ]; unfold_all; subst.
      eexists.
      split.
      eapply RunsToAssign; eauto.
      split.
      solve [eapply diff_submap; eauto].
      split.
      intros x Hni.
      eapply StringSetFacts.singleton_not_iff in Hni.
      solve [rewrite Locals.sel_upd_ne; eauto].
      split.
      solve [eapply new_adt_no_pollute_add_sca].
      eapply eval_ceval in He; eauto.
      rewrite He in *.
      eapply related_add_sca; eauto.
      solve [rewrite diff_submap_cancel; eauto].
    }
  Qed.

End ADTValue.
