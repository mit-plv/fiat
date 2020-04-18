Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.Facade.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Cito.Option.

  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Value := (@Value ADTValue).
  Notation Sca := (@SCA ADTValue).

  Lemma is_true_is_false : forall (st : State) e, is_true st e -> is_false st e -> False.
  Proof.
    intros.
    unfold is_true, is_false in *.
    rewrite H in *; discriminate.
  Qed.

  Lemma safe_if_true : forall (env : Env) e t f st, Safe env (If e t f) st -> is_true st e -> Safe env t st.
  Proof.
    intros.
    inversion H; subst.
    eauto.
    exfalso; eapply is_true_is_false; eauto.
  Qed.

  Definition is_bool (st : State) e := eval_bool st e <> None.

  Definition value_dec (v : Value) : {w | v = SCA _ w} + {a | v = ADT a}.
    destruct v.
    left; exists w; eauto.
    right; exists a; eauto.
  Defined.

  Definition option_value_dec (v : option Value) : {w | v = Some (SCA _ w)} + {a | v = Some (ADT a)} + {v = None}.
    destruct (option_dec v).
    destruct s; subst.
    destruct (value_dec  x).
    destruct s; subst.
    left; left; eexists; eauto.
    destruct s; subst.
    left; right; eexists; eauto.
    subst.
    right; eauto.
  Qed.

  Lemma is_true_is_bool : forall st e, is_true st e -> is_bool st e.
  Proof.
    intros.
    unfold is_true, is_bool in *.
    rewrite H in *.
    discriminate.
  Qed.

  Lemma is_false_is_bool : forall st e, is_false st e -> is_bool st e.
  Proof.
    intros.
    unfold is_false, is_bool in *.
    rewrite H in *.
    discriminate.
  Qed.

  Lemma safe_if_is_bool : forall (env : Env) e t f st, Safe env (If e t f) st -> is_bool st e.
  Proof.
    intros.
    inversion H; subst.
    eapply is_true_is_bool; eauto.
    eapply is_false_is_bool; eauto.
  Qed.

  Lemma safe_if_false : forall (env : Env) e t f st, Safe env (If e t f) st -> is_false st e -> Safe env f st.
  Proof.
    intros.
    inversion H; subst.
    exfalso; eapply is_true_is_false; eauto.
    eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.SyntaxExpr.

  (* test boolean deciders *)
  Open Scope string_scope.
  Require Import Coq.Lists.List.
  Import ListNotations.

  Require Import Bedrock.StringSet.
  Import StringSet.
  Require Import Bedrock.Platform.Cito.StringSetFacts.

  Import Logic.

  Goal is_in "bb" ["aa"; "bb"; "cc"] = true. Proof. exact eq_refl. Qed.
  Goal is_in "dd" ["aa"; "bb"; "cc"] = false. Proof. exact eq_refl. Qed.
  Goal is_disjoint (of_list ["aa"; "bb"; "cc"]) (of_list ["dd"; "ee"]) = true. Proof. exact eq_refl. Qed.
  Goal is_disjoint (of_list ["aa"; "bb"; "cc"]) (of_list ["dd"; "ee"; "cc"]) = false. Proof. exact eq_refl. Qed.
  Goal equal (assigned (Seq (Assign "x" (Var "a")) (Label "y" ("a", "b")))) (of_list ["x"; "y"]) = true. Proof. exact eq_refl. Qed.
  Goal is_disjoint (assigned (Seq (Assign "x" (Var "a")) (Label "y" ("a", "b")))) (of_list ["aa"; "bb"]) = true. Proof. exact eq_refl. Qed.
  Goal is_disjoint (assigned (Seq (Assign "x" (Var "a")) (Label "y" ("a", "b")))) (of_list ["aa"; "bb"; "x"]) = false. Proof. exact eq_refl. Qed.

  Lemma is_disjoint_sound ls1 ls2 : is_disjoint ls1 ls2 = true -> Disjoint ls1 ls2.
  Proof.
    intros Hdisj.
    eapply inter_is_empty_iff in Hdisj; eauto.
  Qed.

  Lemma is_disjoint_complete ls1 ls2 : Disjoint ls1 ls2 -> is_disjoint ls1 ls2 = true.
  Proof.
    intros Hdisj.
    eapply inter_is_empty_iff; eauto.
  Qed.

  Lemma is_disjoint_iff ls1 ls2 : is_disjoint ls1 ls2 = true <-> Disjoint ls1 ls2.
  Proof.
    split; intros H.
    eapply is_disjoint_sound; eauto.
    eapply is_disjoint_complete; eauto.
  Qed.

  Definition not_reachable key (k : key) ks ins := forall i, nth_error ks i = Some k -> exists w, nth_error ins i = Some (Sca w).

  Require Import Coq.Strings.String.
  Require Import Coq.Lists.List.
  Require Import Bedrock.Platform.Cito.StringMap.
  Import StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.
  Require Import Bedrock.Platform.Cito.ListFacts4.
  Require Import Bedrock.Platform.Cito.GeneralTactics.
  Require Import Bedrock.Platform.Cito.GeneralTactics2.
  Require Import Bedrock.Platform.Cito.GeneralTactics4.
  Lemma no_reachable_nil key (k : key) : not_reachable k [] [].
  Proof.
    unfold not_reachable; intros; rewrite nth_error_nil in *; discriminate.
  Qed.

  Lemma not_reachable_cons_sca key (k : key) ks ins k' w : not_reachable k' ks ins -> not_reachable k' (k :: ks) (SCA ADTValue w :: ins).
  Proof.
    unfold not_reachable; intros Hnr.
    intros i Hk'.
    destruct i as [|i]; simpl in *.
    inject Hk'.
    exists w; eauto.
    eapply Hnr in Hk'.
    eauto.
  Qed.

  Lemma not_reachable_cons_neq key (k : key) ks ins k' v : not_reachable k' ks ins -> k' <> k -> not_reachable k' (k :: ks) (v :: ins).
  Proof.
    unfold not_reachable; intros Hnr Hne.
    intros i Hk'.
    destruct i as [|i]; simpl in *.
    inject Hk'.
    intuition.
    eapply Hnr in Hk'.
    eauto.
  Qed.

  Lemma not_reachable_cons_elim key (k : key) ks v vs k' : not_reachable k' (k :: ks) (v :: vs) -> not_reachable k' ks vs.
  Proof.
    unfold not_reachable; intros Hnr.
    intros i Hk'.
    specialize (Hnr (S i)); simpl in *.
    eauto.
  Qed.
  Lemma not_not_reachable key (k : key) ks a ins : ~ not_reachable k (k :: ks) (ADT a :: ins).
  Proof.
    unfold not_reachable.
    nintro.
    specialize (H 0); simpl in *.
    edestruct H; eauto.
    discriminate.
  Qed.
  Lemma not_in_not_reachable key (k : key) ks ins : ~ List.In k ks -> not_reachable k ks ins.
  Proof.
    unfold not_reachable; intros Hni.
    intros i Hk.
    contradict Hni.
    eapply nth_error_In; eauto.
  Qed.

  Lemma find_Some_add_remove_many ks :
    forall ins outs h k v,
      NoDup ks ->
      length ks = length ins ->
      length ks = length outs ->
      (StringMap.find k (add_remove_many ks ins outs h) = Some v <->
       ((not_reachable k ks ins /\ StringMap.find k h = Some v) \/
        exists i a,
          nth_error ks i = Some k /\
          nth_error ins i = Some (ADT a) /\
          nth_error outs i = Some (Some v))).
  Proof.
    induction ks; destruct ins; destruct outs; simpl in *; try solve [intros; discriminate].
    intros h k v Hnd Hlkin Hlkout.
    split.
    intros Hf.
    left.
    split.
    eapply no_reachable_nil.
    eauto.
    intros H.
    openhyp.
    eauto.
    rewrite nth_error_nil in *; discriminate.

    rename a into k.
    intros h k' v' Hnd Hlkin Hlkout.
    inject Hlkin.
    inject Hlkout.
    inversion Hnd; subst.
    split.
    intros Hf.
    destruct v as [w | a].
    eapply IHks in Hf; eauto.
    destruct Hf as [[Hnr Hfk'] | [i [a [Hk' [Hin Hout]]]]].
    left.
    split.
    solve [eapply not_reachable_cons_sca; eauto].
    eauto.
    right.
    solve [exists (S i), a; eauto].

    destruct o as [ao |].
    eapply IHks in Hf; eauto.
    destruct Hf as [[Hnr Hfk'] | [i [a' [Hk' [Hin Hout]]]]].
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject Hfk'.
    right.
    solve [exists 0, a; eauto].
    rewrite StringMapFacts.add_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_neq; eauto].
    eauto.
    right.
    solve [exists (S i), a'; eauto].

    eapply IHks in Hf; eauto.
    destruct Hf as [[Hnr Hfk'] | [i [a' [Hk' [Hin Hout]]]]].
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    rewrite StringMapFacts.remove_eq_o in * by eauto.
    discriminate.
    rewrite StringMapFacts.remove_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_neq; eauto].
    eauto.
    right.
    solve [exists (S i), a'; eauto].

    intros Hor.
    destruct Hor as [[Hnr Hfk'] | [i [a [Hk' [Hin Hout]]]]].
    destruct v as [w | a].
    eapply IHks; eauto.
    left.
    split.
    solve [eapply not_reachable_cons_elim; eauto].
    eauto.
    destruct o as [ao|].
    eapply IHks; eauto.
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    solve [contradict Hnr; eapply not_not_reachable].
    rewrite StringMapFacts.add_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_elim; eauto].
    eauto.
    eapply IHks; eauto.
    destruct (string_dec k' k) as [Heq | Hne].
    subst.
    solve [contradict Hnr; eapply not_not_reachable].
    rewrite StringMapFacts.remove_neq_o in * by eauto.
    left.
    split.
    solve [eapply not_reachable_cons_elim; eauto].
    eauto.

    eapply IHks; eauto.
    destruct i as [|i]; simpl in *.
    inject Hk'.
    inject Hin.
    inject Hout.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    left.
    split.
    solve [eapply not_in_not_reachable; eauto].
    eauto.
    solve [right; exists i, a; eauto].
  Qed.

  Lemma find_ADT_add_remove_many k ks (ins : list Value) outs st a :
    NoDup ks ->
    mapM (sel st) ks = Some ins ->
    length ks = length outs ->
    StringMap.find k (add_remove_many ks ins outs st) = Some (ADT a)->
    exists a', StringMap.find k st = Some (ADT a').
  Proof.
    intros Hnd Hmm Hl Hf.
    eapply find_Some_add_remove_many in Hf; eauto.
    2 : eapply mapM_length; eauto.
    openhyp.
    eexists; eauto.
    eapply mapM_nth_error_2 in Hmm; eauto; openhyp.
    unif x1.
    eexists; eauto.
  Qed.

  Lemma is_in_iff a ls : is_in a ls = true <-> List.In a ls.
  Proof.
    unfold is_in; split; intros H; destruct (in_dec string_dec a ls); eauto; discriminate.
  Qed.
  Lemma iff_false_iff b P : (b = true <-> P) -> (b = false <-> ~ P).
  Proof.
    split; intros; destruct b; intuition.
  Qed.
  Lemma iff_not_true_iff b P : (b = true <-> P) -> (b <> true <-> ~ P).
  Proof.
    split; intros; destruct b; intuition.
  Qed.
  Lemma iff_negb_iff b P : (b = true <-> P) -> (negb b = true <-> ~ P).
  Proof.
    split; intros; destruct b; intuition.
  Qed.
  Lemma iff_negb_not_true_iff b P : (b = true <-> P) -> (negb b <> true <-> P).
  Proof.
    split; intros; destruct b; intuition.
  Qed.
  Lemma not_is_in_iff a ls : is_in a ls = false <-> ~ List.In a ls.
  Proof.
    eapply iff_false_iff; eapply is_in_iff.
  Qed.
  Lemma negb_is_in_iff a ls : negb (is_in a ls) = true <-> ~ List.In a ls.
  Proof.
    eapply iff_negb_iff; eapply is_in_iff.
  Qed.

  Lemma is_some_p_iff A p (o : option A) : is_some_p p o = true <-> match o with | Some a => p a = true | None => False end.
  Proof.
    destruct o as [a|]; simpl in *; intuition.
  Qed.

  Lemma is_mapsto_adt_iff x st : is_mapsto_adt x st = true <-> exists a : ADTValue, StringMap.find x st = Some (ADT a).
  Proof.
    unfold is_mapsto_adt.
    etransitivity.
    eapply is_some_p_iff.
    destruct (option_dec (StringMap.find x st)) as [[v Heq] | Hne].
    rewrite Heq in *.
    etransitivity.
    eapply is_adt_iff.
    split; intros Hex.
    openhyp; subst; eexists; eauto.
    destruct Hex as [a Ha]; inject Ha; eexists; eauto.

    rewrite Hne.
    split; intros.
    intuition.
    openhyp; discriminate.
  Qed.

  Lemma is_mapsto_adt_false_iff x st : is_mapsto_adt x st = false <-> ~ exists a : ADTValue, StringMap.find x st = Some (ADT a).
  Proof.
    eapply iff_false_iff; eapply is_mapsto_adt_iff.
  Qed.

  Lemma not_mapsto_adt_iff x st : not_mapsto_adt x st = true <-> ~ exists a : ADTValue, StringMap.find x st = Some (ADT a).
  Proof.
    eapply iff_negb_iff; eapply is_mapsto_adt_iff.
  Qed.

  Lemma not_mapsto_adt_not_true_iff x st : not_mapsto_adt x st <> true <-> exists a : ADTValue, StringMap.find x st = Some (ADT a).
  Proof.
    eapply iff_negb_not_true_iff; eapply is_mapsto_adt_iff.
  Qed.

  Lemma find_Some_make_map_iff elt ks :
    forall vs k (v : elt),
      NoDup ks ->
      length ks  = length vs ->
      (StringMap.find k (make_map ks vs) = Some v <->
       exists i,
         nth_error ks i = Some k /\
         nth_error vs i = Some v).
  Proof.
    induction ks; destruct vs; simpl in *; intros k v Hnd Hl; (split; [intros Hf | intros Hex]); try discriminate.
    destruct Hex as [i [Hk Hi]]; rewrite nth_error_nil in *; discriminate.
    rename a into k'.
    inject Hl.
    inversion Hnd; subst.
    destruct (string_dec k k') as [Heq | Hne].
    subst.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    inject Hf.
    exists 0; eauto.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    eapply IHks in Hf; eauto.
    destruct Hf as [i [Hk Hv]].
    solve [exists (S i); eauto].
    rename a into k'.
    inject Hl.
    inversion Hnd; subst.
    destruct Hex as [i [Hk Hv]].
    destruct i as [ | i]; simpl in *.
    inject Hk.
    inject Hv.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    solve [eauto].
    destruct (string_dec k k') as [Heq | Hne].
    subst.
    contradict H2.
    solve [eapply nth_error_In; eauto].
    rewrite StringMapFacts.add_neq_o in * by eauto.
    eapply IHks; eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.ListFacts3.

  Lemma NoDup_ArgVars : forall spec, NoDup (ArgVars spec).
    intros; destruct spec; simpl; eapply is_no_dup_sound; eauto.
  Qed.

  Lemma not_in_no_adt k m : ~ StringMap.In k m -> ~ exists a : ADTValue, StringMap.find k m = Some (ADT a).
  Proof.
    intros; not_not; openhyp; eapply find_Some_in; eauto.
  Qed.

  Lemma NoDup_not_in : forall A (x : A) xs, NoDup (x :: xs) -> ~ List.In x xs.
    inversion 1; subst; eauto.
  Qed.

  Lemma not_incl_spec : forall spec, ~ List.In (RetVar spec) (ArgVars spec).
    intros; destruct spec; simpl; eapply negb_is_in_iff; eauto.
  Qed.

  Lemma in_args_not_assigned spec x : List.In x (ArgVars spec) -> ~ StringSet.In x (assigned (Body spec)).
  Proof.
    destruct spec; simpl in *; nintro.
    eapply is_disjoint_iff; eauto.
    split; eauto.
    eapply StringSetFacts.of_list_spec; eauto.
  Qed.

  Lemma safe_seq_1 : forall (env : Env) a b st, Safe env (Seq a b) st -> Safe env a st.
  Proof.
    intros.
    inversion H; subst.
    openhyp.
    eauto.
  Qed.

  Lemma safe_seq_2 : forall (env : Env) a b st, Safe env (Seq a b) st -> forall st', RunsTo env a st st' -> Safe env b st'.
  Proof.
    intros.
    inversion H; subst.
    openhyp.
    eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.GeneralTactics3.

  Lemma safe_while_is_bool (env : Env) e s st : Safe env (While e s) st -> is_bool st e.
  Proof.
    intros H.
    inversion H; unfold_all; subst.
    eapply is_true_is_bool; eauto.
    eapply is_false_is_bool; eauto.
  Qed.

  Lemma is_mapsto_adt_eq_sca x w st : is_mapsto_adt x (StringMap.add x (SCA ADTValue w) st) = false.
  Proof.
    unfold is_mapsto_adt.
    rewrite StringMapFacts.add_eq_o in * by eauto.
    eauto.
  Qed.

  Lemma is_mapsto_adt_neq x (v : Value) st x' : x' <> x -> is_mapsto_adt x' (StringMap.add x v st) = is_mapsto_adt x' st.
  Proof.
    unfold is_mapsto_adt; intros.
    rewrite StringMapFacts.add_neq_o in * by eauto.
    eauto.
  Qed.

  Lemma not_mapsto_adt_find x st v : not_mapsto_adt x st = true -> StringMap.find x st = Some v -> exists w, v = SCA ADTValue w.
  Proof.
    intros Hnmt Hfx.
    unfold not_mapsto_adt in *.
    unfold is_mapsto_adt in *.
    rewrite Hfx in Hnmt; simpl in *.
    destruct v as [w | a]; simpl in *.
    eauto.
    discriminate.
  Qed.

  Lemma wrap_output_not_sca coutput i w : nth_error (wrap_output coutput) i <> Some (Some (SCA ADTValue w)).
  Proof.
    unfold wrap_output.
    rewrite ListFacts.map_nth_error_full.
    destruct (option_dec (nth_error coutput i)) as [s | e]; simpl in *.
    destruct s as [a e]; rewrite e in *; simpl in *.
    destruct a; simpl in *; discriminate.
    rewrite e in *; discriminate.
  Qed.

  Lemma find_none_not_mapsto_adt x (st : State) : find x st = None -> not_mapsto_adt x st = true.
  Proof.
    intros Hf.
    unfold not_mapsto_adt, is_mapsto_adt.
    rewrite Hf.
    eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.StringMap.
  Import StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Hint Extern 0 (_ == _) => reflexivity.

  Lemma add_remove_many_Equal ks : forall types vs st1 st2, st1 == st2 -> @add_remove_many ADTValue ks types vs st1 == add_remove_many ks types vs st2.
  Proof.
    induction ks; destruct types; destruct vs; simpl; try solve [intuition].
    intros st1 st2 Heq.
    rename a into k.
    destruct v as [w | a].
    - eauto.
    - destruct o as [o|].
      + eapply IHks; eauto.
        rewrite Heq; eauto.
      + eapply IHks; eauto.
        rewrite Heq; eauto.
  Qed.

  Import Logic.
  Require Import Coq.Setoids.Setoid.

  Global Add Morphism (@add_remove_many ADTValue)
      with signature eq ==> eq ==> eq ==> Equal ==> Equal as add_remove_many_m.
  Proof.
    intros; eapply add_remove_many_Equal; eauto.
  Qed.

  Lemma add_remove_many_add_comm ks : forall vs types k v (st : State), ~ List.In k ks -> add_remove_many ks types vs (add k v st) == add k v (add_remove_many ks types vs st).
  Proof.
    induction ks; destruct vs; destruct types; simpl; try solve [intuition].
    intros k' v' st Hnin .
    intuition.
    rename a into k.
    destruct v as [w | a].
    - eauto.
    - destruct o as [o |].
      + rewrite add_add_comm by eauto.
        eauto.
      + rewrite remove_add_comm by eauto.
        eauto.
  Qed.

  Lemma add_remove_many_remove_comm ks : forall vs types k (st : State), ~ List.In k ks -> add_remove_many ks types vs (remove k st) == remove k (add_remove_many ks types vs st).
  Proof.
    induction ks; destruct vs; destruct types; simpl; try solve [intuition].
    intros k' st Hnin .
    intuition.
    rename a into k.
    destruct v as [w | a].
    - eauto.
    - destruct o as [o |].
      + rewrite add_remove_comm by eauto.
        eauto.
      + rewrite remove_remove_comm by eauto.
        eauto.
  Qed.

  Fixpoint output_eqv A (types : list Value) (output1 output2 : list A) :=
    match types, output1, output2 with
      | i :: types', o1 :: output1', o2 :: output2' =>
        match i with
          | ADT _ => o1 = o2
          | _ => True
        end /\ output_eqv types' output1' output2'
      | nil, nil, nil => True
      | _, _, _ => False
    end.

  Lemma output_eqv_refl A types : forall (output : list A), length types = length output -> output_eqv types output output.
  Proof.
    induction types; destruct output; simpl; intuition.
    destruct a; eauto.
  Qed.

  Definition not_mapsto_adt_types (k : string) ks types := forall i, nth_error ks i = Some k -> ~ exists a : ADTValue, nth_error types i = Some (ADT a).

  Lemma not_in_not_mapsto_adt_types k ks types : ~ List.In k ks -> not_mapsto_adt_types k ks types.
  Proof.
    intros Hnin.
    unfold not_mapsto_adt_types in *.
    intros i Hnth Hex.
    contradict Hnin.
    eapply nth_error_In; eauto.
  Qed.

  Lemma not_mapsto_adt_types_cons_neq_elim ks types k k' type : not_mapsto_adt_types k (k' :: ks) (type :: types) -> k <> k' -> not_mapsto_adt_types k ks types.
  Proof.
    intros H Hne.
    unfold not_mapsto_adt_types in *.
    intros i Hnth Hex.
    eapply (H (S i)); simpl in *; eauto.
  Qed.

  Lemma not_mapsto_adt_types_cons_neq_intro ks types k k' type : not_mapsto_adt_types k ks types -> k <> k' -> not_mapsto_adt_types k (k' :: ks) (type :: types).
  Proof.
    intros H Hne.
    unfold not_mapsto_adt_types in *.
    intros i Hnth [a Ha].
    destruct i as [|i]; simpl in *.
    - inject Hnth.
      intuition.
    - eapply H; eauto.
  Qed.

  Lemma not_mapsto_adt_types_adt k ks a types : ~ not_mapsto_adt_types k (k :: ks) (ADT a :: types).
  Proof.
    unfold not_mapsto_adt_types.
    intros H.
    eapply (H 0); simpl in *; eauto.
  Qed.

  Arguments SCA {ADTValue} _.
  Arguments ADT {ADTValue} _.

  Lemma not_mapsto_adt_types_sca k ks w types : not_mapsto_adt_types k ks types -> not_mapsto_adt_types k (k :: ks) (SCA w :: types).
  Proof.
    intros H.
    unfold not_mapsto_adt_types in *.
    intros i Hnth [a Ha].
    destruct i as [|i]; simpl in *.
    - discriminate.
    - eapply H; eauto.
  Qed.

  Lemma not_mapsto_adt_types_nil k types : not_mapsto_adt_types k nil types.
  Proof.
    unfold not_mapsto_adt_types; intros.
    rewrite nth_error_nil in *.
    discriminate.
  Qed.

  Lemma mapM_not_mapsto_adt_types ks : forall types k st, not_mapsto_adt k st = true -> mapM (sel st) ks = Some types -> not_mapsto_adt_types k ks types.
  Proof.
    induction ks; destruct types; simpl; try discriminate; intros k st Hnadt Hmm.
    - eapply not_mapsto_adt_types_nil.
    - rename k into k'.
      rename a into k.
      destruct (option_dec (sel st k)) as [ [v Heq] | Hneq]; [rewrite Heq in Hmm | rewrite Hneq in Hmm]; try discriminate.
      destruct (option_dec (mapM (sel st) ks)) as [ [vs Heqs] | Hneq]; [rewrite Heqs in Hmm | rewrite Hneq in Hmm]; try discriminate.
    - rename k into k'.
      rename a into k.
      destruct (option_dec (sel st k)) as [ [ty Heq] | Hneq]; [rewrite Heq in Hmm | rewrite Hneq in Hmm]; try discriminate.
      destruct (option_dec (mapM (sel st) ks)) as [ [tys Heqs] | Hneq]; [rewrite Heqs in Hmm | rewrite Hneq in Hmm]; try discriminate.
      inject Hmm.
      destruct (string_dec k' k) as [Heqk | Hnek].
      + subst.
        destruct v as [w | a].
        * eapply not_mapsto_adt_types_sca; eauto.
        * eapply not_mapsto_adt_iff in Hnadt.
          contradict Hnadt; eexists; eauto.
      + eapply not_mapsto_adt_types_cons_neq_intro; eauto.
  Qed.

  Lemma add_remove_many_eq_output_eqv ks : forall types st1 st2 vs1 vs2 k, remove k (add_remove_many ks types vs1 st1) == remove k (add_remove_many ks types vs2 st2) -> not_mapsto_adt_types k ks types -> length ks = length types -> length ks = length vs1 -> length ks = length vs2 -> NoDup ks -> output_eqv types vs1 vs2.
  Proof.
    induction ks; destruct types; destruct vs1; destruct vs2; simpl; try solve [intros; try discriminate; intuition eauto]; intros k Heq Hnadt Hlent Hlen1 Hlen2 Hnd.
    {
      inject Hlent.
      rename H into Hlent.
      inject Hlen1.
      rename H into Hlen1.
      inject Hlen2.
      rename H into Hlen2.
      rename a into k0.
      inversion Hnd; subst.
      rename H1 into Hnin.
      rename H2 into Hnd'.
      destruct v as [w | a].
      {
        destruct (string_dec k k0) as [Hkeq | Hkne].
        - subst.
          split; eauto.
          eapply IHks; eauto.
          eapply not_in_not_mapsto_adt_types; eauto.
        - eapply not_mapsto_adt_types_cons_neq_elim in Hnadt; eauto.
      }
      {
        destruct (string_dec k k0) as [Hkeq | Hkne].
        {
          subst.
          eapply not_mapsto_adt_types_adt in Hnadt; intuition.
        }
        {
          eapply not_mapsto_adt_types_cons_neq_elim in Hnadt; eauto.
          destruct o as [o1|]; destruct o0 as [o2|].
          {
            split.
            - repeat rewrite add_remove_many_add_comm in Heq by eauto.
              repeat rewrite remove_add_comm in Heq by eauto.
              eapply add_eq_elim in Heq.
              openhyp; subst; eauto.
            - eauto.
          }
          {
            repeat rewrite add_remove_many_add_comm in Heq by eauto.
            repeat rewrite add_remove_many_remove_comm in Heq by eauto.
            repeat rewrite remove_add_comm in Heq by eauto.
            rewrite remove_remove_comm in Heq by eauto.
            eapply add_remove_eq_false in Heq; intuition.
          }
          {
            repeat rewrite add_remove_many_add_comm in Heq by eauto.
            repeat rewrite add_remove_many_remove_comm in Heq by eauto.
            repeat rewrite remove_add_comm in Heq by eauto.
            rewrite remove_remove_comm in Heq by eauto.
            symmetry in Heq.
            eapply add_remove_eq_false in Heq; intuition.
          }
          {
            eauto.
          }
        }
      }
    }
  Qed.

  Lemma add_add_remove_many_eq_elim types k ks v1 vs1 v2 vs2 (st : State) : not_mapsto_adt k st = true -> List.NoDup ks -> add k v1 (add_remove_many ks types vs1 st) == add k v2 (add_remove_many ks types vs2 st) -> mapM (sel st) ks = Some types -> length ks = length vs1 -> length ks = length vs2 -> v1 = v2 /\ output_eqv types vs1 vs2.
  Proof.
    intros Hnadt Hnd Heq Hlen1 Hlen2.
    eapply add_eq_elim in Heq.
    destruct Heq as [Hveq Hmeq].
    split; eauto.
    eapply add_remove_many_eq_output_eqv; eauto.
    - eapply mapM_not_mapsto_adt_types; eauto.
    - eapply mapM_length; eauto.
  Qed.

  Lemma not_in_add_remove_many' ks : forall types outs x (st1 st2 : State), ~ List.In x ks -> find x st1 = find x st2 -> find x (add_remove_many ks types outs st1) = find x st2.
  Proof.
    induction ks; destruct types; destruct outs; simpl; try solve [intuition].
    intros x st1 st2 Hnin Hst.
    eapply Decidable.not_or in Hnin.
    destruct Hnin as [Hnin1 Hnin2].
    rename a into k.
    rename x into k'.
    destruct v as [w | a].
    {
      eauto.
    }
    destruct o as [o|].
    {
      eapply IHks; eauto.
      rewrite add_neq_o by eauto.
      eauto.
    }
    eapply IHks; eauto.
    rewrite remove_neq_o by eauto.
    eauto.
  Qed.

  Lemma not_in_add_remove_many ks : forall types outs x (st : State), ~ List.In x ks -> find x (add_remove_many ks types outs st) = find x st.
    intros; eapply not_in_add_remove_many'; eauto.
  Qed.

End ADTValue.
