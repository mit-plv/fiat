Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Cito.Semantics.
  Require Import Bedrock.Platform.Cito.SemanticsUtil.
  Require Import Coq.Lists.List.

  Notation make_triples := (@make_triples ADTValue).

  Require Import Bedrock.Platform.Cito.GeneralTactics4.

  Arguments store_out {_} _ _.
  Arguments ADTOut {_} _.

  Require Import Bedrock.Memory.

  Definition no_alias (words_cinput : list (W * Value ADTValue)) := forall i j p (ai aj : ADTValue), nth_error words_cinput i = Some (p, ADT ai) -> nth_error words_cinput j = Some (p, ADT aj) -> i = j.

  Definition not_reachable_p p (words_cinput : list (W * Value ADTValue)) := forall i v, nth_error words_cinput i = Some (p, v) -> exists w, v = SCA _ w.

  Require Import Bedrock.Platform.Cito.WordMap.
  Import WordMap.
  Require Import Bedrock.Platform.Cito.WordMapFacts.

  Require Import Bedrock.Platform.Cito.GeneralTactics.
  Require Import Bedrock.Platform.Cito.ListFacts4.
  Lemma no_alias_tail ls : forall e, no_alias (e :: ls) -> no_alias ls.
  Proof.
    unfold no_alias; intros e Hna.
    intros i j p ai aj Hi Hj.
    assert (S i = S j).
    eapply Hna; eauto.
    inject H; eauto.
  Qed.
  Lemma not_reachable_p_incl ls1 ls2 p : List.incl ls1 ls2 -> not_reachable_p p ls2 -> not_reachable_p p ls1.
    unfold not_reachable_p; intros Hin Hnr.
    intros i v Hi.
    eapply incl_nth_error in Hi; eauto; openhyp.
    eapply Hnr in H; eauto; openhyp.
  Qed.
  Lemma not_reachable_p_tail ls e p : not_reachable_p p (e :: ls) -> not_reachable_p p ls.
    intros; eapply not_reachable_p_incl; eauto.
    eapply incl_tl; eapply incl_refl; eauto.
  Qed.
  Lemma not_not_reachable_p p a ls : ~ not_reachable_p p ((p, ADT a) :: ls).
  Proof.
    unfold not_reachable_p.
    intros H.
    specialize (H 0 (ADT a)).
    simpl in *.
    edestruct H; eauto.
    discriminate.
  Qed.
  Lemma no_alias_not_reachable_p p a ls : no_alias ((p, ADT a) :: ls) -> not_reachable_p p ls.
  Proof.
    intros Hna.
    unfold not_reachable_p.
    intros i v Hi.
    destruct v.
    eauto.
    unfold no_alias in *.
    assert (S i = 0).
    eapply Hna; simpl in *; eauto.
    discriminate.
  Qed.

  Lemma fold_bwd p a triples :
    forall h,
      let words_cinput := List.map (fun x => (Word x, ADTIn x)) triples in
      no_alias words_cinput ->
      ((not_reachable_p p words_cinput /\ find p h = Some a) \/
       exists i input, nth_error triples i = Some {| Word := p; ADTIn := ADT input; ADTOut := Some a |}) ->
      find p (List.fold_left store_out triples h) = Some a.
  Proof.
    induction triples; simpl in *.
    intros h ? H.
    openhyp.
    eauto.
    rewrite nth_error_nil in H; discriminate.

    destruct a0 as [tp ti to]; simpl in *.
    intros h Hna H.
    eapply IHtriples.
    eapply no_alias_tail; eauto.
    destruct H as [[Hnr hf] | [i [ai Ht]] ].
    left.
    split.
    eapply not_reachable_p_tail; eauto.
    unfold store_out; simpl.
    destruct ti as [w | ai].
    eauto.
    destruct to as [ao |].
    destruct (Word.weq p tp).
    subst; solve [eapply not_not_reachable_p in Hnr; intuition].
    solve [rewrite add_neq_o; eauto].
    destruct (Word.weq p tp).
    subst; solve [eapply not_not_reachable_p in Hnr; intuition].
    solve [rewrite remove_neq_o; eauto].
    destruct i as [| i]; simpl in *.
    inject Ht.
    left.
    split.
    eapply no_alias_not_reachable_p; eauto.
    unfold store_out; simpl.
    solve [rewrite add_eq_o; eauto].

    right.
    eauto.
  Qed.

  Lemma fold_fwd :
    forall k (v : ADTValue) ls h,
      WordMap.MapsTo k v (fold_left store_out ls h) ->
      (WordMap.MapsTo k v h /\
       forall a o, ~List.In {| Word := k; ADTIn := ADT a; ADTOut := o |} ls)
      \/ exists a,
           List.In {| Word := k; ADTIn := ADT a; ADTOut := Some v |} ls.
  Proof.
    induction ls; simpl; intuition.
    apply IHls in H; intuition.

    unfold store_out, Semantics.store_out in H; simpl in H.
    destruct a; simpl in *.
    destruct ADTIn.
    left; intuition eauto.
    discriminate.
    destruct ADTOut.
    apply add_mapsto_iff in H; intuition subst.
    eauto.
    left; intuition.
    inject H3.
    eauto.
    eauto 2.
    apply remove_mapsto_iff in H; intuition subst.
    left; intuition.
    inject H3.
    eauto.
    eauto 2.
    destruct H0.
    eauto.
  Qed.

  Lemma fold_store_out_elim p a triples words_cinput coutput h :
    words_cinput = List.map (fun x => (Word x, ADTIn x)) triples ->
    coutput = List.map ADTOut triples ->
    find p (List.fold_left store_out triples h) = Some a ->
    (not_reachable_p p words_cinput /\ find p h = Some a) \/
    exists i input, nth_error triples i = Some {| Word := p; ADTIn := ADT input; ADTOut := Some a |}.
  Proof.
    intros Hwid Hod Hf.
    subst.
    eapply find_mapsto_iff in Hf.
    eapply fold_fwd in Hf.
    destruct Hf as [[Hf Hnr] | [ai Hin]].
    eapply find_mapsto_iff in Hf.
    left.
    split.
    unfold not_reachable_p.
    intros i v Hwi.
    eapply nth_error_map_elim in Hwi.
    destruct Hwi as [[tp ti to] [Ht He]]; simpl in *.
    inject He.
    destruct v.
    eexists; eauto.
    eapply Locals.nth_error_In in Ht.
    solve [eapply Hnr in Ht; intuition].
    solve [eauto].

    right.
    eapply in_nth_error in Hin.
    destruct Hin as [i Ht].
    repeat eexists; eauto.
  Qed.

  Lemma fold_store_out_intro p a triples words_cinput coutput h :
    words_cinput = List.map (fun x => (Word x, ADTIn x)) triples ->
    coutput = List.map ADTOut triples ->
    no_alias words_cinput ->
    ((not_reachable_p p words_cinput /\ find p h = Some a) \/
     exists i input, nth_error triples i = Some {| Word := p; ADTIn := ADT input; ADTOut := Some a |}) ->
    find p (List.fold_left store_out triples h) = Some a.
  Proof.
    intros; subst; eapply fold_bwd; eauto.
  Qed.
  Require Import Bedrock.Platform.Cito.SemanticsFacts7.

  Lemma find_Some_fold_store_out p a words_cinput coutput h :
    no_alias words_cinput ->
    length words_cinput = length coutput ->
    (find p (List.fold_left store_out (make_triples words_cinput coutput) h) = Some a <->
     ((not_reachable_p p words_cinput /\ find p h = Some a) \/
      exists i input,
        nth_error words_cinput i = Some (p, ADT input) /\
        nth_error coutput i = Some (Some a))).
  Proof.
    intros Hna Hl.
    split.
    intros Hf.
    eapply fold_store_out_elim in Hf; simpl; eauto.
    destruct Hf as [[Hnr Hf] | [i [ai Ht]]].
    left.
    rewrite make_triples_Word_ADTIn in *; eauto.
    right.
    exists i, ai.
    eapply nth_error_make_triples_elim in Ht; eauto.

    intros H.
    eapply fold_store_out_intro; eauto.
    rewrite make_triples_Word_ADTIn; eauto.
    destruct H as [[Hnr Hf] | [i [ai [Hwi Ho]]]].
    left.
    split.
    rewrite make_triples_Word_ADTIn; eauto.
    solve [eauto].
    right.
    exists i, ai.
    eapply nth_error_make_triples_intro; eauto.
  Qed.

  Definition ret_doesn't_matter (p addr : W) (ret : Value ADTValue) := p <> addr \/ exists w, ret = SCA _  w.
  Definition p_addr_ret_dec (p addr : W) (ret : Value ADTValue) : { a : ADTValue | ret = ADT a /\ p = addr} + {ret_doesn't_matter p addr ret}.
    destruct ret.
    right; right; eexists; eauto.
    destruct (Word.weq p addr).
    left; eexists; eauto.
    right; left; eauto.
  Defined.

  Import FMapNotations.
  Open Scope fmap_scope.

  Lemma find_ret_doesn't_matter p addr ret triples h h1 : ret_doesn't_matter p addr ret -> find p (heap_upd_option (fold_left store_out triples h) (fst (decide_ret addr ret)) (snd (decide_ret addr ret)) - h1) = find p (fold_left store_out triples h - h1).
  Proof.
    intros Hdm; destruct Hdm.
    2 : solve [openhyp; subst; simpl; eauto].
    destruct ret; simpl in *.
    solve [openhyp; subst; simpl; eauto].
    solve [eapply option_univalence; intros v; split; intros Hf; eapply diff_find_Some_iff in Hf; eapply diff_find_Some_iff; rewrite add_neq_o in *; eauto].
  Qed.

  Notation Value := (@Value ADTValue).

  Definition only_adt := List.map (fun x : Value => match x with | ADT a => Some a | _ => None end).

  Definition reachable_heap (vs : Locals.vals) argvars (input : list Value) := make_mapM (List.map (fun x => vs x) argvars) (only_adt input).

  Lemma in_reachable_heap_iff vs ks : forall ins p, length ks = length ins -> (In p (reachable_heap vs ks ins) <-> exists i k a, nth_error ks i = Some k /\ nth_error ins i = Some (ADT a) /\ vs k = p).
  Proof.
    unfold reachable_heap, only_adt; intros ins p Hl.
    split.
    intros Hi.
    eapply in_make_mapM_iff in Hi.
    destruct Hi as [i [a [Hk Hv]]].
    eapply nth_error_map_elim in Hk.
    destruct Hk as [k [Hk Hvs]].
    subst.
    eapply nth_error_map_elim in Hv.
    destruct Hv as [v [Hv Ha]].
    destruct v as [w | a'].
    discriminate.
    inject Ha.
    solve [exists i, k, a; eauto].
    solve [repeat rewrite map_length; eauto].

    intros Hex.
    destruct Hex as [i [k [a [Hk [Hv Hvs]]]]].
    subst.
    eapply in_make_mapM_iff.
    solve [repeat rewrite map_length; eauto].
    exists i, a.
    split.
    solve [erewrite map_nth_error; eauto].
    solve [erewrite map_nth_error; eauto; simpl; eauto].
  Qed.

  Definition no_aliasM (vs : Locals.vals) ks ins := no_dupM (List.map (fun x => vs x) ks) (only_adt ins).

  Lemma find_Some_reachable_heap_iff vs ks : forall ins p a, length ks = length ins -> no_aliasM vs ks ins -> (find p (reachable_heap vs ks ins) = Some a <-> exists i k, nth_error ks i = Some k /\ nth_error ins i = Some (ADT a) /\ vs k = p).
  Proof.
    unfold reachable_heap, only_adt; intros ins p a Hl Hna.
    split.
    intros Hi.
    eapply find_Some_make_mapM_iff in Hi; eauto.
    destruct Hi as [i [Hk Hv]].
    eapply nth_error_map_elim in Hk.
    destruct Hk as [k [Hk Hvs]].
    subst.
    eapply nth_error_map_elim in Hv.
    destruct Hv as [v [Hv Ha]].
    destruct v as [w | a'].
    discriminate.
    inject Ha.
    solve [exists i, k; eauto].
    solve [repeat rewrite map_length; eauto].

    intros Hex.
    destruct Hex as [i [k [Hk [Hv Hvs]]]].
    subst.
    eapply find_Some_make_mapM_iff; eauto.
    solve [repeat rewrite map_length; eauto].
    exists i.
    split.
    solve [erewrite map_nth_error; eauto].
    solve [erewrite map_nth_error; eauto; simpl; eauto].
  Qed.

End ADTValue.
