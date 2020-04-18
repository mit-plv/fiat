Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Cito.Semantics.

  Notation Value := (@Value ADTValue).

  Arguments SCA {_} _.

  Require Import Bedrock.Platform.Cito.SemanticsExpr.
  Require Import Coq.Lists.List.
  Require Import Bedrock.Platform.Cito.WordMap.
  Import WordMap.
  Require Import Bedrock.Platform.Cito.WordMapFacts.
  Import FMapNotations.
  Open Scope fmap_scope.
  Require Import Bedrock.Platform.Cito.SemanticsUtil.

  Definition combine_ret w o : Value :=
    match o with
      | Some a => ADT a
      | None => SCA w
    end.

  Arguments store_out {_} _ _.

  Definition TransitTo spec words inputs outputs ret_w ret_a (heap heap' : Heap ADTValue) :=
    let ret := combine_ret ret_w ret_a in
    let words_inputs := List.combine words inputs in
    length inputs = length words /\
    length outputs = length words /\
    good_inputs heap words_inputs /\
    PreCond spec inputs /\
    PostCond spec (combine inputs outputs) ret /\
    let heap := fold_left store_out (make_triples words_inputs outputs) heap in
    separated heap ret_w ret_a /\
    heap' == heap_upd_option heap ret_w ret_a.

  Definition TransitSafe spec words inputs (heap : Heap ADTValue) :=
    let words_inputs := List.combine words inputs in
    length inputs = length words /\
    good_inputs heap words_inputs /\
    PreCond spec inputs.

  Require Import Bedrock.Platform.Cito.BedrockTactics.
  Require Import Bedrock.Platform.Cito.GeneralTactics Bedrock.Platform.Cito.GeneralTactics2 Bedrock.Platform.Cito.GeneralTactics3.

  Definition match_ret vs (lhs : option string) (ret_w : W) :=
    match lhs with
      | Some x => ret_w = vs x
      | None => True
    end.

  Require Import Bedrock.Platform.Cito.ListFacts5.
  Require Import Bedrock.Platform.Cito.ListFacts4.
  Arguments ADTIn {_} _.
  Arguments ADTOut {_} _.
  Lemma combine_ret_decide_ret addr ret : combine_ret (fst (decide_ret addr ret)) (snd (decide_ret addr ret)) = ret.
  Proof.
    destruct ret; simpl; eauto.
  Qed.
  Require Import Bedrock.Platform.Cito.SemanticsFacts7.
  Arguments ADTIn {_} _.
  Arguments ADTOut {_} _.
  Arguments ADTIn {_} _.
  Arguments ADTOut {_} _.
  Arguments ADTIn {_} _.
  Arguments ADTOut {_} _.
  Arguments ADTIn {_} _.
  Arguments ADTOut {_} _.

  Lemma RunsTo_TransitTo lhs f args env spec v v' : let f_w := eval (fst v) f in snd env f_w = Some (Foreign spec) -> RunsTo env (Syntax.Call lhs f args) v v' -> exists inputs outputs ret_w ret_a, TransitTo spec (List.map (eval (fst v)) args) inputs outputs ret_w ret_a (snd v) (snd v') /\ match_ret (fst v') lhs ret_w.
  Proof.
    simpl.
    intros.
    inv_clear H0.
    rewrite H4 in H; discriminate.
    rewrite H4 in H; injection H; intros; subst.
    Arguments ADTIn {_} _.
    Arguments ADTOut {_} _.
    set (inputs := List.map ADTIn triples) in *.
    set (outputs := List.map ADTOut triples) in *.
    set (ret_w := fst (decide_ret _ _)) in *.
    set (ret_a := snd (decide_ret _ _)) in *.
    exists inputs, outputs, ret_w, ret_a.
    descend.
    {
      unfold TransitTo.
      descend; trivial.
      {
        unfold_all.
        repeat rewrite map_length.
        eapply map_eq_length_eq in H5.
        eauto.
      }
      {
        unfold_all.
        repeat rewrite map_length.
        eapply map_eq_length_eq in H5.
        eauto.
      }
      {
        unfold_all.
        rewrite H5.
        rewrite combine_map.
        eauto.
      }
      {
        unfold_all.
        rewrite combine_map.
    Arguments ADTIn {_} _.
    Arguments ADTOut {_} _.
        rewrite combine_ret_decide_ret.
        eauto.
      }
      {
        unfold_all.
        rewrite H5.
        rewrite combine_map.
        erewrite <- split_triples; eauto.
      }
      {
        unfold_all.
        rewrite H5.
        rewrite combine_map.
        erewrite <- split_triples; eauto.
      }
    }
    unfold match_ret.
    destruct lhs; simpl in *.
    {
      sel_upd_simpl; eauto.
    }
    eauto.
  Qed.

  Require Import Coq.Lists.List.
  Lemma fst_decide_ret_combine_ret ret_w ret_a : fst (decide_ret ret_w (combine_ret ret_w ret_a)) = ret_w.
  Proof.
    destruct ret_a; simpl; eauto.
  Qed.
  Lemma snd_decide_ret_combine_ret ret_w ret_a : snd (decide_ret ret_w (combine_ret ret_w ret_a)) = ret_a.
  Proof.
    destruct ret_a; simpl; eauto.
  Qed.
  Require Import Bedrock.Platform.Cito.SemanticsFacts6.

  Lemma TransitTo_RunsTo lhs f args env spec v v' : let f_w := eval (fst v) f in snd env f_w = Some (Foreign spec) -> forall inputs outputs ret_w ret_a, TransitTo spec (List.map (eval (fst v)) args) inputs outputs ret_w ret_a (snd v) (snd v') -> fst v' = upd_option (fst v) lhs ret_w -> RunsTo env (Syntax.Call lhs f args) v v'.
  Proof.
    simpl.
    intros.
    destruct v; destruct v'; simpl in *.
    unfold TransitTo in *; simpl in *.
    openhyp.
    subst; simpl in *.
    rewrite <- (fst_decide_ret_combine_ret ret_w ret_a).
    set (words_inputs := List.combine (List.map (eval w) args) inputs) in *.
    set (triples := make_triples words_inputs outputs) in *.
    repeat rewrite map_length in *.
    eapply RunsToCallForeign; simpl; eauto.
    {
      instantiate (1 := triples).
      unfold_all.
      rewrite make_triples_Word by (rewrite combine_length_eq; repeat rewrite map_length; eauto).
      rewrite map_fst_combine by (repeat rewrite map_length; eauto).
      eauto.
    }
    {
      unfold_all.
      rewrite make_triples_Word_ADTIn by (rewrite combine_length_eq; repeat rewrite map_length; eauto).
      eauto.
    }
    {
      unfold_all.
      rewrite make_triples_ADTIn by (rewrite combine_length_eq; repeat rewrite map_length; eauto).
      rewrite map_snd_combine by (repeat rewrite map_length; eauto).
      eauto.
    }
    {
      unfold_all.
      erewrite <- combine_map.
      rewrite make_triples_ADTIn by (rewrite combine_length_eq; repeat rewrite map_length; eauto).
      rewrite make_triples_ADTOut by (rewrite combine_length_eq; repeat rewrite map_length; eauto).
      rewrite map_snd_combine by (repeat rewrite map_length; eauto).
      eauto.
    }
    {
      rewrite fst_decide_ret_combine_ret.
      rewrite snd_decide_ret_combine_ret.
      eauto.
    }
    {
      rewrite fst_decide_ret_combine_ret.
      rewrite snd_decide_ret_combine_ret.
      eauto.
    }
  Qed.

  Lemma Safe_TransitSafe : forall f args env spec v, let f_w := eval (fst v) f in snd env f_w = Some (Foreign spec) -> forall lhs, Safe env (Syntax.Call lhs f args) v -> exists inputs, TransitSafe spec (List.map (eval (fst v)) args) inputs (snd v).
  Proof.
    simpl; intros.
    inv_clear H0.
    rewrite H in H4; discriminate.
    rewrite H in H4; injection H4; intros; subst.
    unfold TransitSafe in *.
    destruct v as [vs h]; simpl in *.
    set (inputs := List.map snd _) in *.
    exists inputs.
    descend; eauto.
    {
      unfold_all.
      repeat rewrite map_length.
      eapply map_eq_length_eq.
      eauto.
    }
    unfold_all.
    rewrite H5.
    rewrite combine_map.
    setoid_rewrite <- surjective_pairing.
    rewrite map_id.
    eauto.
  Qed.

  Lemma TransitSafe_Safe f args env spec v : let f_w := eval (fst v) f in snd env f_w = Some (Foreign spec) -> forall inputs, TransitSafe spec (List.map (eval (fst v)) args) inputs (snd v) -> forall lhs, Safe env (Syntax.Call lhs f args) v.
    simpl; intros.
    unfold TransitSafe in *.
    openhyp.
    destruct v as [vs h]; simpl in *.
    repeat rewrite map_length in *.
    eapply SafeCallForeign; simpl; eauto.
    {
      rewrite map_fst_combine by (repeat rewrite map_length; eauto).
      eauto.
    }
    rewrite map_snd_combine by (repeat rewrite map_length; eauto).
    eauto.
  Qed.

End ADTValue.
