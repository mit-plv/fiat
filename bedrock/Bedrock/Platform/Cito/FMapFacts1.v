Set Implicit Arguments.

Require Import Coq.Structures.DecidableType.
Require Import Coq.FSets.FMapInterface.

Module WFacts_fun (E:DecidableType)(Import M:WSfun E).

  Require Import Coq.FSets.FMapFacts.

  Module Import P := WProperties_fun E M.
  Import F.

  Section Elt.

    Variable elt:Type.

    Implicit Types m : t elt.
    Implicit Types x y z k : key.
    Implicit Types e v : elt.
    Implicit Types ls : list (key * elt).

    Notation eqke := (@eq_key_elt elt).
    Notation eqk := (@eq_key elt).

    Definition to_map := of_list.

    Definition keys m := List.map (@fst _ _) (elements m).

    Definition find_list k := findA (B := elt) (eqb k).

    Require Import Bedrock.Platform.Cito.GeneralTactics.
    Require Import Bedrock.Platform.Cito.GeneralTactics2.

    Definition NoDupKey := NoDupA eqk.
    Definition InPair := InA eqke.

    Require Import Bedrock.Platform.Cito.Option.

    Lemma NoDup_cons : forall ls k1 v1 k2 v2, NoDupKey ((k1, v1) :: ls) -> InPair (k2, v2) ls -> ~ E.eq k1 k2.
      unfold InPair.
      intros.
      inversion H; subst.
      not_not.
      eapply InA_eqA.
      eapply eqk_equiv.
      Focus 2.
      eapply InA_eqke_eqk.
      2 : eauto.
      eauto.
      unfold eq_key.
      eauto.
      Grab Existential Variables.
      eauto.
    Qed.

    Lemma update_with_empty : forall m, update m (@empty _) = m.
      unfold update; intros.
      rewrite fold_1.
      rewrite elements_empty.
      reflexivity.
    Qed.

    Lemma In_find_list_Some_left : forall k v ls, NoDupKey ls -> InPair (k, v) ls -> find_list k ls = Some v.
    Proof.
      induction ls; simpl; intros.
      eapply InA_nil in H0; intuition.
      inversion H0; subst.
      unfold find_list in *; destruct a; simpl in *.
      destruct H2; simpl in *.
      subst.
      unfold eqb.
      destruct (eq_dec k k0).
      eauto.
      intuition.
      destruct a; simpl in *.
      generalize H2; eapply NoDup_cons in H2; eauto; intro.
      eapply IHls in H1.
      unfold find_list in *; simpl in *.
      unfold eqb in *.
      destruct (eq_dec k k0); intuition.
      eapply E.eq_sym in e0.
      intuition.
      inversion H; subst.
      eauto.
    Qed.

    Lemma In_find_list_Some_right : forall ls k v, NoDupKey ls -> find_list k ls = Some v -> InPair (k, v) ls.
    Proof.
      induction ls; simpl; intros.
      unfold find_list in *; simpl in *.
      discriminate.
      unfold find_list in *; destruct a; simpl in *.
      unfold eqb in *.
      destruct (eq_dec k k0); intuition.
      injection H0; intros; subst.
      left.
      econstructor; simpl; eauto.
      right.
      eapply IHls.
      inversion H; subst.
      eauto.
      eauto.
    Qed.

    Lemma In_find_list_Some : forall ls k v, NoDupKey ls -> (InPair (k, v) ls <-> find_list k ls = Some v).
      split; intros.
      eapply In_find_list_Some_left; eauto.
      eapply In_find_list_Some_right; eauto.
    Qed.

    Lemma In_find_Some : forall k v m, InPair (k, v) (elements m) <-> find k m = Some v.
      split; intros.
      eapply find_1.
      eapply elements_2; eauto.
      eapply find_2 in H.
      eapply elements_1 in H; eauto.
    Qed.

    Lemma None_not_Some : forall a, a = None <-> ~ exists v, a = Some v.
      split; intros.
      intuition.
      openhyp.
      subst.
      discriminate.
      destruct (option_dec a); eauto.
      destruct s.
      contradict H.
      eexists; eauto.
    Qed.

    Lemma option_univalence : forall A a b, a = b <-> forall (v : A), a = Some v <-> b = Some v.
      split; intros.
      subst; split; eauto.
      destruct (option_dec a).
      destruct s.
      subst.
      symmetry.
      eapply H; eauto.
      subst.
      destruct (option_dec b).
      destruct s.
      subst.
      eapply H; eauto.
      eauto.
    Qed.

    Lemma find_list_elements : forall m k, find_list k (elements m) = find k m.
      intros.
      eapply option_univalence.
      intros.
      split; intros.
      eapply In_find_Some.
      eapply In_find_list_Some in H.
      eauto.
      eapply elements_3w.
      eapply In_find_Some in H.
      eapply In_find_list_Some.
      eapply elements_3w.
      eauto.
    Qed.

    Lemma In_find_list_not_None_left : forall ls k, InA E.eq k (List.map (@fst _ _) ls) -> find_list k ls <> None.
    Proof.
      induction ls; simpl; intros.
      eapply InA_nil in H; intuition.
      inversion H; subst.
      unfold find_list in *; destruct a; simpl in *.
      unfold eqb in *.
      destruct (eq_dec k k0); intuition.
      discriminate.
      eapply IHls in H1.
      unfold find_list in *; destruct a; simpl in *.
      destruct (eqb k k0); intuition.
      discriminate.
    Qed.

    Lemma In_find_list_not_None_right : forall ls k, find_list k ls <> None -> InA E.eq k (List.map (@fst _ _) ls).
    Proof.
      induction ls; simpl; intros.
      intuition.
      unfold find_list in *; destruct a; simpl in *.
      unfold eqb in *.
      destruct (eq_dec k k0); intuition.
    Qed.

    Lemma In_find_list_not_None : forall ls k, InA E.eq k (List.map (@fst _ _) ls) <-> find_list k ls <> None.
      intros.
      split.
      eapply In_find_list_not_None_left.
      eapply In_find_list_not_None_right.
    Qed.

    Lemma ex_up : forall A (e : option A),
                    (e = None -> False)
                    -> exists (v : A), e = Some v.
      destruct e; intuition eauto.
    Qed.

    Lemma In_find_not_None : forall k m, find k m <> None <-> In k m.
      unfold In.
      split; intros.
      eapply ex_up in H.
      openhyp.
      eapply find_2 in H.
      eexists; eauto.

      openhyp.
      eapply find_1 in H.
      rewrite H.
      intuition.
      discriminate.
    Qed.

    Lemma In_In_keys : forall k m, In k m <-> InA E.eq k (keys m).
      split; intros.
      eapply In_find_not_None in H.
      eapply In_find_list_not_None.
      rewrite find_list_elements.
      eauto.
      eapply In_find_not_None.
      unfold keys in *.
      eapply In_find_list_not_None in H.
      rewrite find_list_elements in H.
      eauto.
    Qed.

    Lemma add_4 : forall m x y e, ~ E.eq x y -> find y (add x e m) = find y m.
      intros.
      eapply option_univalence.
      split; intros.
      eapply find_1.
      eapply add_3; eauto.
      eapply find_2; eauto.
      eapply find_1.
      eapply add_2; eauto.
      eapply find_2; eauto.
    Qed.

    Lemma map_3 : forall B (f : elt -> B) k m, In k m -> In k (map f m).
      intros; eapply map_in_iff; eauto.
    Qed.

    Lemma map_4 : forall B (f : elt -> B) k m, In k (map f m) -> In k m.
      intros; eapply map_in_iff; eauto.
    Qed.

    Lemma find_map : forall B (f : elt -> B) k v m, find k m = Some v -> find k (map f m) = Some (f v).
      intros.
      eapply find_2 in H.
      eapply find_1.
      eapply map_1; eauto.
    Qed.

    Lemma MapsTo_In : forall k v m, MapsTo k v m -> In k m.
      intros; eexists; eauto.
    Qed.

  End Elt.

End WFacts_fun.

Definition sumbool_to_bool A B (x : {A} + {B}) := if x then true else false.

Require Import Bedrock.Platform.Cito.SetoidListFacts.

Require Import Coq.Structures.DecidableTypeEx.

Module UWFacts_fun (E : UsualDecidableType) (Import M : WSfun E).

  Module Import WFacts := WFacts_fun E M.
  Import P.
  Import F.

  Section Elt.

    Variable elt:Type.

    Implicit Types m : t elt.
    Implicit Types x y z k : key.
    Implicit Types e v : elt.
    Implicit Types ls : list (key * elt).

    Notation eqke := (@eq_key_elt elt).
    Notation eqk := (@eq_key elt).

    Require Import Bedrock.Platform.Cito.GeneralTactics.
    Require Import Bedrock.Platform.Cito.GeneralTactics2.

    Lemma eqke_eq : equiv_2 eqke eq.
      split; intros.
      unfold eq_key_elt in *.
      openhyp.
      destruct a; destruct b; simpl in *; subst; eauto.
      subst.
      unfold eq_key_elt in *.
      eauto.
    Qed.

    Lemma InA_eqke_InA_eq : equiv_2 (InA eqke) (InA eq).
      intros; eapply equiv_InA; eapply eqke_eq.
    Qed.

    Lemma InA_eqke_In : forall ls p, InA eqke p ls <-> List.In p ls.
      intros; eapply equiv_2_trans.
      eapply InA_eqke_InA_eq.
      unfold equiv_2; intros; eapply InA_eq_In_iff.
    Qed.

    Notation fst := (@fst _ _).

    Lemma In_fst_elements_In : forall m k, List.In k (List.map fst (elements m)) <-> In k m.
      split; intros.
      eapply InA_eq_In_iff in H.
      eapply In_In_keys in H; eauto.
      eapply InA_eq_In_iff.
      specialize In_In_keys; intros; unfold keys in *; eapply H0; eauto.
    Qed.

    Lemma InA_eqk_elim : forall ls k v, InA eqk (k, v) ls -> exists v', InA eqke (k, v') ls.
      induction ls; simpl; intros.
      eapply InA_nil in H; intuition.
      destruct a; simpl in *.
      inversion H; subst.
      unfold eq_key in *; simpl in *.
      subst.
      eexists.
      econstructor.
      unfold eq_key_elt; simpl in *.
      eauto.
      eapply IHls in H1.
      openhyp.
      eexists.
      econstructor 2.
      eauto.
    Qed.

    Lemma NoDupKey_NoDup_fst : forall ls, NoDupKey ls <-> NoDup (List.map fst ls).
      induction ls; simpl; intros.
      split; intros; econstructor.
      destruct a; simpl in *.
      split; intros.
      inversion H; subst.
      econstructor.
      intuition.
      contradict H2.
      eapply in_map_iff in H0.
      openhyp.
      destruct x; simpl in *.
      subst.
      eapply InA_eqke_eqk.
      eauto.
      eapply InA_eqke_In.
      eauto.
      eapply IHls.
      eauto.

      inversion H; subst.
      econstructor.
      intuition.
      contradict H2.
      eapply InA_eqk_elim in H0.
      openhyp.
      eapply InA_eqke_In in H0.
      eapply in_map_iff.
      eexists.
      split.
      2 : eauto.
      eauto.
      eapply IHls; eauto.
    Qed.

    Lemma MapsTo_to_map : forall k v ls, NoDupKey ls -> List.In (k, v) ls -> MapsTo k v (to_map ls).
      unfold to_map; intros.
      eapply of_list_1.
      eauto.
      eapply InA_eqke_In; eauto.
    Qed.

    Lemma MapsTo_to_map_elim : forall k v ls, NoDupKey ls -> MapsTo k v (to_map ls) -> List.In (k, v) ls.
      unfold to_map; intros.
      eapply InA_eqke_In; eauto.
      eapply of_list_1.
      eauto.
      eauto.
    Qed.

    Definition InKey k ls := List.In k (List.map fst ls).

    Lemma In_to_map : forall ls k, In k (to_map ls) <-> InKey k ls.
      unfold to_map.
      unfold InKey.
      induction ls; simpl; intros.
      eapply empty_in_iff.
      unfold uncurry in *.
      destruct a; simpl in *.
      split; intros.
      eapply add_in_iff in H.
      openhyp.
      eauto.
      right.
      eapply IHls; eauto.
      eapply add_in_iff.
      openhyp.
      eauto.
      right.
      eapply IHls; eauto.
    Qed.

    Lemma NoDupKey_unapp1 : forall ls1 ls2, NoDupKey (ls1 ++ ls2) -> NoDupKey ls1.
      induction ls1; simpl; intuition.
      econstructor.
      econstructor.
      inversion H; subst.
      not_not.
      intuition.
      eapply InA_app_iff; eauto.
      eapply IHls1.
      inversion H; subst; eauto.
    Qed.

    Lemma NoDupKey_unapp2 : forall ls1 ls2, NoDupKey (ls1 ++ ls2) -> NoDupKey ls2.
      induction ls1; simpl; intuition.
      eapply IHls1.
      inversion H; subst; eauto.
    Qed.

    Lemma inkey_app_or : forall k ls1 ls2, InKey k (ls1 ++ ls2) <-> InKey k ls1 \/ InKey k ls2.
      unfold InKey.
      split; intros.
      eapply in_map_iff in H.
      openhyp.
      eapply in_app_or in H0.
      openhyp.
      left.
      eapply in_map_iff; eexists; eauto.
      right.
      eapply in_map_iff; eexists; eauto.
      openhyp.
      eapply in_map_iff in H.
      openhyp.
      subst.
      eapply in_map_iff; eexists; intuition.
      eapply in_map_iff in H.
      openhyp.
      subst.
      eapply in_map_iff; eexists; intuition.
    Qed.

    Definition DisjointKey ls1 ls2 := forall k, ~ (InKey k ls1 /\ InKey k ls2).

    Lemma NoDupKey_app : forall ls1 ls2, NoDupKey ls1 -> NoDupKey ls2 -> DisjointKey ls1 ls2 -> NoDupKey (ls1 ++ ls2).
      unfold DisjointKey.
      induction ls1; simpl; intros.
      eauto.
      econstructor.
      intuition.
      eapply InA_app in H2.
      openhyp.
      inversion H; subst.
      contradiction.
      destruct a; simpl in *.
      eapply H1.
      unfold InKey.
      simpl.
      split; eauto.
      eapply InA_eqk_elim in H2.
      openhyp.
      eapply InA_eqke_In in H2.
      eapply in_map_iff.
      eexists; intuition.
      2 : eauto.
      eauto.
      eauto.
      eapply IHls1.
      inversion H; subst.
      eauto.
      eauto.
      intros.
      firstorder.
    Qed.

    Definition InKey_dec k ls : {InKey k ls} + {~ InKey k ls}.
      unfold InKey.
      eapply in_dec.
      eapply E.eq_dec.
    Defined.

    Definition diff_map ls1 ls2 :=
      let f p := negb (sumbool_to_bool (InKey_dec (fst p) ls2)) in
      List.filter f ls1.

    Lemma diff_NoDupKey : forall ls1 ls2, NoDupKey ls1 -> NoDupKey (diff_map ls1 ls2).
      unfold diff_map.
      induction ls1; simpl; intros.
      eauto.
      unfold sumbool_to_bool in *.
      destruct a; simpl in *.
      destruct (InKey_dec k ls2) in *.
      simpl in *.
      eapply IHls1; inversion H; subst; eauto.
      simpl in *.
      econstructor.
      2 : eapply IHls1; inversion H; subst; eauto.
      intuition.
      inversion H; subst.
      contradict H3.
      eapply filter_InA in H0.
      openhyp.
      eauto.
      eauto.
      unfold Proper; unfold respectful; intros.
      destruct x; destruct y; unfold eq_key in *; simpl in *; subst; eauto.
    Qed.

    Lemma diff_In : forall ls1 ls2 x, InKey x (diff_map ls1 ls2) -> InKey x ls1 /\ ~ InKey x ls2.
      unfold InKey.
      unfold diff_map.
      intros.
      eapply in_map_iff in H.
      openhyp.
      subst.
      eapply filter_In in H0.
      openhyp.
      split.
      eapply in_map_iff.
      eexists; eauto.
      unfold sumbool_to_bool in *.
      destruct (InKey_dec _ _); simpl in *.
      intuition.
      intuition.
    Qed.

    Lemma diff_DisjointKey : forall ls1 ls2, DisjointKey (diff_map ls1 ls2) ls2.
      unfold DisjointKey.
      intros.
      intuition.
      eapply diff_In in H0.
      openhyp.
      intuition.
    Qed.

    Definition Equal_map ls1 ls2 := forall k, find_list k ls1 = find_list k ls2.

    Lemma NoDupKey_diff_union : forall ls1 ls2, NoDupKey ls1 -> NoDupKey ls2 -> NoDupKey (diff_map ls1 ls2 ++ ls2).
      intros.
      eapply NoDupKey_app.
      eapply diff_NoDupKey.
      eauto.
      eauto.
      eapply diff_DisjointKey.
    Qed.

    Lemma In_of_list : forall k ls, NoDupKey ls -> (In k (of_list ls) <-> InKey k ls).
      unfold InKey, In.
      split; intros.
      openhyp.
      eapply of_list_1 in H0; eauto.
      eapply InA_eqke_In in H0.
      eapply in_map_iff.
      eexists; intuition.
      2 : eauto.
      eauto.
      eapply in_map_iff in H0.
      openhyp.
      subst.
      destruct x; simpl in *.
      eapply InA_eqke_In in H1.
      eapply of_list_1 in H1; eauto.
    Qed.

    Lemma of_list_app : forall ls1 ls2, NoDupKey (ls1 ++ ls2) -> Equal (of_list (ls1 ++ ls2)) (update (of_list ls1) (of_list ls2)).
      induction ls1; simpl; intros.
      unfold Equal.
      intros.
      eapply option_univalence.
      split; intros.
      eapply find_1.
      eapply update_mapsto_iff.
      left.
      eapply find_2; eauto.
      eapply find_2 in H0.
      eapply update_mapsto_iff in H0.
      openhyp.
      eapply find_1; eauto.
      eapply empty_mapsto_iff in H0.
      intuition.
      unfold uncurry.
      destruct a; simpl in *.
      unfold Equal.
      intros.
      destruct (eq_dec y k).
      subst.
      erewrite add_eq_o; eauto.
      symmetry.
      eapply find_1.
      eapply update_mapsto_iff.
      right.
      split.
      eapply add_1; eauto.
      inversion H; subst.
      not_not.
      eapply In_of_list in H0.
      unfold InKey in *.
      eapply in_map_iff in H0.
      openhyp.
      subst.
      destruct x; simpl in *.
      eapply InA_eqke_eqk; eauto.
      eapply InA_eqke_In.
      instantiate (1 := e0).
      intuition.
      eapply NoDupKey_unapp2; eauto.
      erewrite add_neq_o; eauto.
      erewrite IHls1.
      eapply option_univalence.
      split; intros.
      eapply find_2 in H0.
      eapply update_mapsto_iff in H0.
      eapply find_1.
      openhyp.
      eapply update_mapsto_iff.
      eauto.
      eapply update_mapsto_iff.
      right.
      split; eauto.
      eapply add_2; eauto.
      eapply find_2 in H0.
      eapply update_mapsto_iff in H0.
      eapply find_1.
      openhyp.
      eapply update_mapsto_iff.
      eauto.
      eapply update_mapsto_iff.
      right.
      split; eauto.
      eapply add_3 in H0; eauto.
      inversion H; subst; eauto.
    Qed.

    Lemma of_list_diff : forall ls1 ls2, NoDupKey ls1 -> NoDupKey ls2 -> Equal (of_list (diff_map ls1 ls2)) (diff (of_list ls1) (of_list ls2)).
      induction ls1; simpl; intros.
      unfold Equal.
      intros.
      rewrite empty_o.
      symmetry.
      eapply not_find_in_iff.
      intuition.
      eapply diff_in_iff in H1.
      openhyp.
      eapply empty_in_iff; eauto.
      unfold sumbool_to_bool.
      unfold uncurry.
      destruct (InKey_dec (fst a) ls2); simpl.
      erewrite IHls1; eauto.
      Focus 2.
      inversion H; subst; eauto.
      destruct a; simpl in *.
      unfold Equal.
      intros.
      eapply option_univalence.
      split; intros.
      eapply find_2 in H1.
      generalize H1; intro.
      eapply MapsTo_In in H1.
      eapply diff_in_iff in H1.
      openhyp.
      destruct (eq_dec y k).
      subst.
      inversion H; subst.
      contradict H6.
      unfold In in H1.
      openhyp.
      eapply of_list_1 in H1; eauto.
      eapply InA_eqke_eqk; eauto.
      eapply find_1.
      eapply diff_mapsto_iff in H2.
      openhyp.
      eapply diff_mapsto_iff.
      split.
      2 : eauto.
      eapply add_2.
      intuition.
      eauto.
      eapply find_2 in H1.
      eapply diff_mapsto_iff in H1.
      openhyp.
      eapply add_mapsto_iff in H1.
      openhyp.
      subst.
      contradict H2.
      eapply In_of_list; eauto.
      eapply find_1.
      eapply diff_mapsto_iff.
      eauto.
      unfold uncurry.
      unfold Equal.
      intros.
      destruct a; simpl in *.
      destruct (eq_dec y k).
      subst.
      erewrite add_eq_o; eauto.
      symmetry.
      eapply find_1.
      eapply diff_mapsto_iff.
      split.
      eapply add_1; eauto.
      not_not.
      eapply In_of_list; eauto.
      erewrite add_neq_o; eauto.
      erewrite IHls1; eauto.
      eapply option_univalence.
      split; intros.
      eapply find_2 in H1.
      generalize H1; intro.
      eapply diff_mapsto_iff in H1.
      openhyp.
      eapply find_1.
      eapply diff_mapsto_iff.
      split; eauto.
      eapply add_2; eauto.
      eapply find_2 in H1.
      eapply diff_mapsto_iff in H1.
      openhyp.
      eapply add_3 in H1; eauto.
      eapply find_1.
      eapply diff_mapsto_iff; eauto.
      inversion H; subst; eauto.
    Qed.

    Lemma diff_union : forall ls1 ls2, NoDupKey ls1 -> NoDupKey ls2 ->  incl ls2 ls1 -> Equal_map (diff_map ls1 ls2 ++ ls2) ls1.
      unfold Equal_map.
      intros.
      unfold find_list.
      erewrite <- of_list_1b.
      erewrite <- of_list_1b.
      2 : eauto.
      2 : eapply NoDupKey_diff_union; eauto.
      erewrite of_list_app.
      2 : eapply NoDupKey_diff_union; eauto.
      eapply option_univalence.
      split; intros.
      eapply find_2 in H2.
      eapply update_mapsto_iff in H2.
      openhyp.
      eapply of_list_1 in H2; eauto.
      eapply find_1.
      eapply of_list_1; eauto.
      eapply InA_eqke_In in H2.
      eapply InA_eqke_In.
      eauto.
      eapply find_1 in H2.
      rewrite of_list_diff in H2; eauto.
      eapply find_2 in H2.
      eapply diff_mapsto_iff in H2.
      openhyp.
      eapply find_1.
      eauto.
      eapply find_1.
      eapply update_mapsto_iff.
      destruct (In_dec (of_list ls2) k).
      unfold In in i.
      openhyp.
      generalize H3; intro.
      eapply of_list_1 in H3; eauto.
      eapply InA_eqke_In in H3.
      eapply H1 in H3.
      eapply InA_eqke_In in H3.
      eapply of_list_1 in H3; eauto.
      eapply find_1 in H3.
      rewrite H3 in H2.
      injection H2; intro; subst.
      eauto.
      right.
      split.
      2 : eauto.
      eapply find_2.
      rewrite of_list_diff; eauto.
      eapply find_1.
      eapply diff_mapsto_iff.
      eapply find_2 in H2.
      eauto.
    Qed.

    Lemma InKey_InA_eqk : forall k v ls, InKey k ls <-> InA eqk (k, v) ls.
      unfold InKey.
      split; intros.
      eapply in_map_iff in H.
      openhyp.
      subst.
      destruct x; simpl in *.
      eapply InA_eqke_In in H0.
      eapply InA_eqke_eqk; eauto.
      eapply InA_eqk_elim in H.
      openhyp.
      eapply InA_eqke_In in H.
      eapply in_map_iff.
      eexists; intuition.
      2 : eauto.
      eauto.
    Qed.

    Lemma NoDupKey_app_DisjointKey : forall ls1 ls2, NoDupKey (ls1 ++ ls2) -> DisjointKey ls1 ls2.
      unfold DisjointKey.
      unfold InKey.
      induction ls1; simpl; intuition.
      subst.
      simpl in *.
      inversion H; subst.
      contradict H3.
      eapply InKey_InA_eqk.
      unfold InKey.
      rewrite map_app.
      eapply in_or_app.
      eauto.
      eapply IHls1.
      inversion H; subst; eauto.
      eauto.
    Qed.

    Lemma NoDup_app_find_list : forall ls1 ls2 k v, NoDupKey (ls1 ++ ls2) -> find_list k ls1 = Some v -> find_list k (ls1 ++ ls2) = Some v.
      unfold find_list.
      intros.
      erewrite <- of_list_1b.
      erewrite <- of_list_1b in H0.
      erewrite of_list_app; eauto.
      eapply find_1.
      eapply find_2 in H0.
      eapply update_mapsto_iff.
      right.
      split; eauto.
      generalize H; intros.
      eapply NoDupKey_app_DisjointKey in H.
      unfold DisjointKey in *.
      intuition.
      eapply In_of_list in H2.
      eapply MapsTo_In in H0.
      eapply In_of_list in H0.
      eauto.
      eapply NoDupKey_unapp1; eauto.
      eapply NoDupKey_unapp2; eauto.
      eapply NoDupKey_unapp1; eauto.
      eauto.
    Qed.

    Lemma NoDup_app_find_list_2 : forall ls1 ls2 k v, NoDupKey (ls1 ++ ls2) -> find_list k ls2 = Some v -> find_list k (ls1 ++ ls2) = Some v.
      unfold find_list.
      intros.
      erewrite <- of_list_1b; eauto.
      erewrite <- of_list_1b in H0.
      erewrite of_list_app; eauto.
      eapply find_1.
      eapply find_2 in H0.
      eapply update_mapsto_iff.
      eauto.
      eapply NoDupKey_unapp2; eauto.
    Qed.

    Lemma find_list_neq : forall ls k v k', NoDupKey ls -> ~ E.eq k' k -> find_list k' ls = find_list k' (ls ++ (k, v) :: nil).
      unfold E.eq.
      unfold find_list.
      unfold eqb.
      induction ls; simpl; intuition.
      destruct (eq_dec _ _); intuition.
      destruct (eq_dec _ _); eauto.
      eapply IHls; eauto.
      inversion H; subst; eauto.
    Qed.

  End Elt.

End UWFacts_fun.
