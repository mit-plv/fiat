Set Implicit Arguments.

Require Import Coq.Structures.DecidableTypeEx.
Require Import Coq.FSets.FMapInterface.
Require Bedrock.Platform.Cito.ListFacts1.
Require Bedrock.Platform.Cito.FMapFacts1.
Require Bedrock.Platform.Cito.GeneralTactics.
Require Bedrock.Platform.Cito.GeneralTactics2.
Require Bedrock.Platform.Cito.Option.
Require Bedrock.Platform.Cito.GeneralTactics4.
Require Bedrock.Platform.Cito.ListFacts4.
Require Bedrock.Platform.Cito.SetoidListFacts.

Module UWFacts_fun (E : UsualDecidableType) (Import M : WSfun E).

  Import Bedrock.Platform.Cito.ListFacts1.

  Import Bedrock.Platform.Cito.FMapFacts1.
  Module Import UWFacts := UWFacts_fun E M.
  Import WFacts.
  Import P.
  Import F.

  Definition Submap {elt} m1 m2 := forall {k v}, @find elt k m1 = Some v -> find k m2 = Some v.
  Definition direct_sum elt (h1 h2 h12 : t elt) := (Equal (update h1 h2) h12 /\ Disjoint h1 h2).

  Module FMapNotations.
    Infix "==" := (@Equal _) (at level 70) : fmap_scope.
    Notation "{}" := (@empty _) : fmap_scope.
    Infix "-" := (@diff _) : fmap_scope.
    Infix "+" := (@update _) : fmap_scope.
    Infix "<=" := Submap : fmap_scope.
    Notation "h1 * h2 === h12" := (direct_sum h1 h2 h12) (at level 100) : fmap_scope.
    Delimit Scope fmap_scope with fmap.
  End FMapNotations.

  Section TopSection.

    Import Bedrock.Platform.Cito.GeneralTactics.
    Import Bedrock.Platform.Cito.GeneralTactics2.
    Import Bedrock.Platform.Cito.Option.
    Import ListNotations.
    Import FMapNotations.
    Open Scope fmap_scope.

    Hint Extern 1 => reflexivity.

    Section Elt.

      Variable elt:Type.

      Implicit Types m : t elt.
      Implicit Types x y z k : key.
      Implicit Types e v : elt.
      Implicit Types ls : list (key * elt).

      Notation eqke := (@eq_key_elt elt).
      Notation eqk := (@eq_key elt).

      Lemma In_MapsTo : forall k m, In k m -> exists v, MapsTo k v m.
        unfold In; eauto.
      Qed.

      Lemma not_in_find : forall k m, ~ In k m -> find k m = None.
        intros; eapply not_find_in_iff; eauto.
      Qed.

      Lemma of_list_empty : of_list [] == @empty elt.
        eauto.
      Qed.

      (* update *)

      Lemma update_o_1 : forall k m1 m2, ~ In k m2 -> find k (m1 + m2) = find k m1.
        intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H0; eapply update_mapsto_iff in H0; openhyp.
        eapply MapsTo_In in H0; intuition.
        eapply find_1; eauto.
        eapply find_2 in H0.
        eapply find_1; eapply update_mapsto_iff; eauto.
      Qed.

      Lemma update_o_2 : forall k m1 m2, In k m2 -> find k (m1 + m2) = find k m2.
        intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H0; eapply update_mapsto_iff in H0; openhyp.
        eapply find_1; eauto.
        intuition.
        eapply find_2 in H0.
        eapply find_1; eapply update_mapsto_iff; eauto.
      Qed.

      Lemma update_empty_1 : forall m, {} + m == m.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H.
        eapply update_mapsto_iff in H; openhyp.
        eapply find_1; eauto.
        eapply empty_mapsto_iff in H; intuition.
        eapply find_2 in H.
        eapply find_1; eapply update_mapsto_iff; eauto.
      Qed.

      Lemma update_empty_2 : forall m, m + {} == m.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H.
        eapply update_mapsto_iff in H; openhyp.
        eapply empty_mapsto_iff in H; intuition.
        eapply find_1; eauto.
        eapply find_2 in H.
        eapply find_1; eapply update_mapsto_iff.
        right; split; eauto.
        intuition.
        eapply empty_in_iff; eauto.
      Qed.

      Lemma update_assoc : forall m1 m2 m3, m1 + m2 + m3 == m1 + (m2 + m3).
        intros.
        unfold Equal.
        intros.
        eapply option_univalence.
        split; intros.
        eapply find_2 in H.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        left.
        eapply update_mapsto_iff.
        eauto.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        left.
        eapply update_mapsto_iff.
        eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        not_not.
        eapply update_in_iff in H2.
        intuition.

        eapply find_2 in H.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        eapply update_mapsto_iff.
        eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        not_not.
        eapply update_in_iff.
        eauto.
        not_not.
        eapply update_in_iff.
        eauto.
      Qed.

      Lemma update_self : forall m, m + m == m.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply update_mapsto_iff in H; openhyp.
        eapply find_1; eauto.
        eapply MapsTo_In in H; intuition.
        eapply find_2 in H.
        eapply find_1; eapply update_mapsto_iff; eauto.
      Qed.

      Lemma update_same : forall m1 m2, m1 == m2 -> m1 + m2 == m1.
        intros.
        rewrite H.
        eapply update_self.
      Qed.

      Lemma update_diff_same : forall m1 m2 m3, m1 - m3 + (m2 - m3) == m1 + m2 - m3.
        intros.
        unfold Equal.
        intros.
        eapply option_univalence.
        split; intros.
        eapply find_2 in H.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply diff_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply diff_mapsto_iff.
        split; eauto.
        eapply update_mapsto_iff.
        eauto.
        eapply diff_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply diff_mapsto_iff.
        split; eauto.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        not_not.
        eapply diff_in_iff; eauto.

        eapply find_2 in H.
        eapply diff_mapsto_iff in H.
        openhyp.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        left.
        eapply diff_mapsto_iff; eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split.
        eapply diff_mapsto_iff; eauto.
        not_not.
        eapply diff_in_iff in H2.
        intuition.
      Qed.

      Lemma Disjoint_diff_update_comm : forall m1 m2 m3, Disjoint m2 m3 -> m1 - m2 + m3 == m1 + m3 - m2.
        intros.
        unfold Equal.
        intros.
        eapply option_univalence.
        split; intros.
        eapply find_2 in H0.
        eapply update_mapsto_iff in H0.
        openhyp.
        eapply find_1.
        eapply diff_mapsto_iff.
        split.
        eapply update_mapsto_iff.
        eauto.
        unfold Disjoint in *.
        intuition.
        eapply H.
        split; eauto.
        eapply MapsTo_In; eauto.
        eapply diff_mapsto_iff in H0.
        openhyp.
        eapply find_1.
        eapply diff_mapsto_iff.
        split; eauto.
        eapply update_mapsto_iff.
        eauto.

        eapply find_2 in H0.
        eapply diff_mapsto_iff in H0.
        openhyp.
        eapply update_mapsto_iff in H0.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        eapply diff_mapsto_iff.
        eauto.
      Qed.

      (* update_all *)

      Definition update_all ms := List.fold_left (fun acc m => update acc m) ms (@empty elt).

      Lemma update_all_nil : update_all [] == {}.
        eauto.
      Qed.

      Lemma update_all_single : forall m, update_all [m] == m.
        intros.
        unfold update_all; simpl.
        eapply update_empty_1.
      Qed.

      Definition update_all' m ms := fold_left (fun acc m0 : t elt => acc + m0) ms m.

      Lemma update_all'_m' : forall ms m1 m2, m1 == m2 -> update_all' m1 ms == update_all' m2 ms.
        unfold update_all'.
        induction ms; simpl; intros.
        eauto.
        erewrite IHms.
        eauto.
        rewrite H.
        eauto.
      Qed.

      Global Add Morphism update_all'
          with signature Equal ==> Logic.eq ==> Equal as update_all'_m.
        intros; eapply update_all'_m'; eauto.
      Qed.

      Lemma update_all_cons : forall ms m, update_all (m :: ms) == m + (update_all ms).
        induction ms; simpl; intros.
        rewrite update_all_nil.
        rewrite update_all_single.
        rewrite update_empty_2.
        eauto.
        unfold update_all in *.
        simpl in *.
        rewrite IHms.
        replace (fold_left (fun acc m0 : t elt => acc + m0) ms ({} + m + a)) with (update_all' ({} + m + a) ms) by reflexivity.
        rewrite update_assoc.
        unfold update_all'.
        rewrite IHms.
        rewrite update_assoc.
        eauto.
      Qed.

      Lemma update_all_Equal : forall ms1 ms2, List.Forall2 (@Equal elt) ms1 ms2 -> update_all ms1 == update_all ms2.
        induction 1; simpl; intros.
        eauto.
        repeat rewrite update_all_cons.
        rewrite H.
        rewrite IHForall2.
        eauto.
      Qed.

      Lemma app_all_update_all : forall lsls, @NoDupKey elt (app_all lsls) -> of_list (app_all lsls) == update_all (List.map (@of_list _) lsls).
        induction lsls; simpl; intros.
        eauto.
        rewrite update_all_cons.
        rewrite of_list_app; eauto.
        rewrite IHlsls; eauto.
        eapply NoDupKey_unapp2; eauto.
      Qed.

      Lemma update_all_elim : forall ms k v, MapsTo k v (update_all ms) -> exists m, List.In m ms /\ MapsTo k v m.
        induction ms; simpl; intros.
        rewrite update_all_nil in H.
        eapply empty_mapsto_iff in H; intuition.
        rewrite update_all_cons in H.
        eapply update_mapsto_iff in H; openhyp.
        eapply IHms in H; openhyp.
        eexists; split; eauto.
        eexists; split; eauto.
      Qed.

      (* diff *)

      Lemma diff_empty : forall m, diff m {} == m.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply find_1; eauto.
        eapply find_2 in H.
        eapply find_1.
        eapply diff_mapsto_iff; split; eauto.
        intuition; eapply empty_in_iff; eauto.
      Qed.

      Lemma empty_diff : forall m, {} - m == {}.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply empty_mapsto_iff in H; intuition.
        eapply find_2 in H; eapply empty_mapsto_iff in H; intuition.
      Qed.

      Lemma diff_same : forall m, m - m == {}.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply MapsTo_In in H; intuition.
        eapply find_2 in H; eapply empty_mapsto_iff in H; intuition.
      Qed.

      Lemma diff_update : forall m1 m2 m3, m1 - (m2 + m3) == m1 - m2 - m3.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply find_1.
        eapply diff_mapsto_iff; split.
        eapply diff_mapsto_iff; split; eauto.
        not_not; eapply update_in_iff; eauto.
        not_not; eapply update_in_iff; eauto.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply diff_mapsto_iff in H; openhyp.
        eapply find_1.
        eapply diff_mapsto_iff; split; eauto.
        not_not; eapply update_in_iff in H2; intuition.
      Qed.

      Lemma diff_diff_sym : forall m1 m2 m3, m1 - m2 - m3 == m1 - m3 - m2.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply diff_mapsto_iff in H; openhyp.
        eapply find_1.
        eapply diff_mapsto_iff; split; eauto.
        eapply diff_mapsto_iff; split; eauto.
        eapply find_2 in H; eapply diff_mapsto_iff in H; openhyp.
        eapply diff_mapsto_iff in H; openhyp.
        eapply find_1.
        eapply diff_mapsto_iff; split; eauto.
        eapply diff_mapsto_iff; split; eauto.
      Qed.

      Lemma diff_o : forall k m1 m2, ~ In k m2 -> find k (m1 - m2) = find k m1.
        intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H0; eapply diff_mapsto_iff in H0; openhyp.
        eapply find_1; eauto.
        eapply find_2 in H0.
        eapply find_1; eapply diff_mapsto_iff; split; eauto.
      Qed.

      Lemma diff_o_none : forall k m1 m2, In k m2 -> find k (m1 - m2) = None.
        intros.
        eapply not_in_find.
        intuition.
        eapply diff_in_iff in H0.
        intuition.
      Qed.

      (* Compat *)

      Definition Compat m1 m2 := forall k, In k m1 -> In k m2 -> find k m1 = find k m2.

      Lemma Compat_sym : forall m1 m2, Compat m1 m2 -> Compat m2 m1.
        unfold Compat; intros; symmetry; eauto.
      Qed.

      Lemma Compat_refl : forall m, Compat m m.
        unfold Compat; intros; eauto.
      Qed.

      Global Add Parametric Relation : (t elt) Compat
          reflexivity proved by Compat_refl
          symmetry proved by Compat_sym
            as Compat_rel.

      Global Add Morphism Compat
          with signature Equal ==> Equal ==> iff as Compat_m.
        unfold Compat; intros.
        intuition.
        rewrite <- H in *.
        rewrite <- H0 in *.
        eauto.
        rewrite H in *.
        rewrite H0 in *.
        eauto.
      Qed.

      Lemma Compat_diff : forall m1 m2 m, Compat m1 m2 -> Compat (m1 - m) m2.
        unfold Compat; intros.
        rewrite <- H; eauto.
        rewrite diff_o; eauto.
        eapply diff_in_iff in H0; intuition.
        eapply diff_in_iff in H0; intuition.
      Qed.

      Lemma Compat_empty : forall m, Compat m {}.
        unfold Compat; intros.
        eapply empty_in_iff in H0; intuition.
      Qed.

      Lemma Compat_update : forall m1 m2 m3, Compat m1 m2 -> Compat m1 m3 -> Compat m1 (m2 + m3).
        unfold Compat; intros.
        destruct (In_dec m3 k).
        rewrite update_o_2; eauto.
        rewrite update_o_1; eauto.
        eapply H; eauto.
        eapply update_in_iff in H2; intuition.
      Qed.

      Lemma Compat_update_sym : forall m1 m2, Compat m1 m2 -> m1 + m2 == m2 + m1.
        unfold Compat; intros.
        unfold Equal; intros.
        destruct (In_dec m1 y); destruct (In_dec m2 y).
        rewrite update_o_2 by eauto.
        rewrite update_o_2 by eauto.
        symmetry; eauto.
        rewrite update_o_1 by eauto.
        rewrite update_o_2 by eauto.
        eauto.
        rewrite update_o_2 by eauto.
        rewrite update_o_1 by eauto.
        eauto.
        rewrite update_o_1 by eauto.
        rewrite update_o_1 by eauto.
        repeat rewrite not_in_find; eauto.
      Qed.

      Lemma Compat_update_all : forall ms m, List.Forall (Compat m) ms -> Compat m (update_all ms).
        induction ms; simpl; intros.
        unfold update_all; simpl.
        eapply Compat_empty.
        rewrite update_all_cons.
        inversion H; subst.
        eapply Compat_update; eauto.
      Qed.

      Lemma Compat_add_not_In : forall k v m1 m2, Compat (add k v m1) m2 -> ~ In k m1 -> Compat m1 m2.
        intros.
        unfold Compat in *.
        intros.
        erewrite <- H; eauto.
        rewrite add_neq_o; eauto.
        not_not.
        subst; eauto.
        eapply add_in_iff; eauto.
      Qed.

      Lemma Compat_eq : forall k v1 v2 m1 m2, Compat m1 m2 -> find k m1 = Some v1 -> find k m2 = Some v2 -> v1 = v2.
        intros.
        unfold Compat in *.
        erewrite H in H0.
        congruence.
        eapply find_2 in H0.
        eapply MapsTo_In; eauto.
        eapply find_2 in H1.
        eapply MapsTo_In; eauto.
      Qed.

      Lemma Compat_MapsTo : forall m1 m2, Compat m1 m2 -> forall k v1 v2, MapsTo k v1 m1 -> MapsTo k v2 m2 -> v1 = v2.
        intros.
        generalize H0; intro.
        generalize H1; intro.
        eapply find_1 in H0.
        eapply find_1 in H1.
        rewrite H in H0.
        rewrite H0 in H1.
        injection H1; intros; eauto.
        eapply MapsTo_In; eauto.
        eapply MapsTo_In; eauto.
      Qed.

      Definition AllCompat := ForallOrdPairs Compat.

      Lemma update_all_intro : forall ms, AllCompat ms -> forall k v m, List.In m ms -> MapsTo k v m -> MapsTo k v (update_all ms).
        induction 1; simpl; intros.
        intuition.
        openhyp.
        subst.
        rewrite update_all_cons.
        destruct (In_dec (update_all l) k).
        eapply In_MapsTo in i.
        openhyp.
        eapply Compat_update_all in H.
        eapply Compat_MapsTo in H; eauto.
        subst.
        eapply update_mapsto_iff; eauto.
        eapply update_mapsto_iff; eauto.
        rewrite update_all_cons.
        eapply update_mapsto_iff; eauto.
      Qed.

      (* Disjoint *)

      Global Add Parametric Relation : (t elt) (@Disjoint elt)
          symmetry proved by (@Disjoint_sym elt)
            as Disjoint_rel.

      Lemma Disjoint_Compat : forall m1 m2, Disjoint m1 m2 -> Compat m1 m2.
        unfold Disjoint, Compat; intros; firstorder.
      Qed.

      Lemma Disjoint_empty : forall m, Disjoint m {}.
        unfold Disjoint; intros.
        intuition.
        eapply empty_in_iff in H1; intuition.
      Qed.

      Lemma Disjoint_update : forall m1 m2 m3, Disjoint m1 m2 -> Disjoint m1 m3 -> Disjoint m1 (m2 + m3).
        unfold Disjoint; intros.
        intuition.
        eapply update_in_iff in H3; firstorder.
      Qed.

      Lemma Disjoint_update_sym : forall m1 m2, Disjoint m1 m2 -> update m1 m2 == update m2 m1.
        intros.
        eapply Compat_update_sym.
        eapply Disjoint_Compat; eauto.
      Qed.

      Lemma Disjoint_diff : forall m1 m2 m3, Disjoint m1 m2 -> Disjoint m1 (m2 - m3).
        unfold Disjoint; intros.
        intuition.
        eapply diff_in_iff in H2; firstorder.
      Qed.

      Lemma Disjoint_after_diff : forall m1 m2, Disjoint (m1 - m2) m2.
        unfold Disjoint; intros.
        intuition.
        eapply diff_in_iff in H0; firstorder.
      Qed.

      Lemma Disjoint_diff_no_effect : forall m1 m2, Disjoint m1 m2 -> m1 - m2 == m1.
        unfold Equal; intros.
        eapply option_univalence; split; intros.
        eapply find_2 in H0; eapply diff_mapsto_iff in H0; openhyp.
        eapply find_1; eauto.
        eapply find_2 in H0.
        eapply find_1; eapply diff_mapsto_iff; split; eauto.
        intuition; eapply H; split; eauto.
        eapply MapsTo_In; eauto.
      Qed.

      Lemma Disjoint_update_all : forall ms m, List.Forall (Disjoint m) ms -> Disjoint m (update_all ms).
        induction ms; simpl; intros.
        unfold update_all; simpl.
        eapply Disjoint_empty.
        rewrite update_all_cons.
        inversion H; subst.
        eapply Disjoint_update; eauto.
      Qed.

      (* map *)

      Lemma map_empty : forall B (f : elt -> B), map f {} == {}.
        unfold Equal; intros.
        rewrite map_o.
        repeat rewrite empty_o.
        eauto.
      Qed.

      Lemma map_add : forall B (f : _ -> B) k v m, map f (add k v m) == add k (f v) (map f m).
        unfold Equal; intros.
        rewrite map_o.
        repeat rewrite add_o.
        destruct (eq_dec k y).
        eauto.
        rewrite map_o.
        eauto.
      Qed.

      Lemma map_update : forall B (f : _ -> B) m1 m2, map f (m1 + m2) == map f m1 + map f m2.
        unfold Equal; intros.
        eapply option_univalence.
        split; intros.
        eapply find_2 in H.
        eapply map_mapsto_iff in H.
        openhyp.
        subst.
        eapply update_mapsto_iff in H0.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        left.
        eapply map_mapsto_iff.
        eexists; eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split.
        eapply map_mapsto_iff.
        eexists; eauto.
        not_not.
        eapply map_in_iff; eauto.

        eapply find_2 in H.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply map_mapsto_iff in H.
        openhyp.
        subst.
        eapply find_1.
        eapply map_mapsto_iff.
        eexists; split; eauto.
        eapply update_mapsto_iff.
        eauto.
        eapply map_mapsto_iff in H.
        openhyp.
        subst.
        eapply find_1.
        eapply map_mapsto_iff.
        eexists; split; eauto.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        not_not.
        eapply map_in_iff; eauto.
      Qed.

      Lemma map_of_list : forall B (f : elt -> B) ls, map f (of_list ls) == of_list (List.map (fun p => (fst p, f (snd p))) ls).
        induction ls; simpl; intros.
        eapply map_empty.
        unfold uncurry; simpl in *.
        rewrite <- IHls.
        destruct a; simpl in *.
        eapply map_add.
      Qed.

      (* mapi *)

      Global Add Parametric Morphism elt' : (@mapi elt elt')
          with signature Logic.eq ==> Equal ==> Equal as mapi_m.
        intros; subst; eauto.
        unfold Equal; intros.
        repeat rewrite mapi_o.
        rewrite H; eauto.
        intros; subst; eauto.
        intros; subst; eauto.
      Qed.

      Lemma find_mapi :
        forall B (f : _ -> _ -> B) k v m,
          find k m = Some v ->
          find k (mapi f m) = Some (f k v).
        intros.
        rewrite mapi_o.
        rewrite H.
        eauto.
        intros; subst; eauto.
      Qed.

      Lemma mapi_empty : forall B (f : _ -> elt -> B), mapi f {} == {}.
        unfold Equal; intros.
        rewrite mapi_o.
        repeat rewrite empty_o.
        eauto.
        intros.
        subst.
        eauto.
      Qed.

      Lemma mapi_add : forall B (f : _ -> _ -> B) k v m, mapi f (add k v m) == add k (f k v) (mapi f m).
        unfold Equal; intros.
        rewrite mapi_o.
        repeat rewrite add_o.
        destruct (eq_dec k y).
        subst.
        eauto.
        rewrite mapi_o.
        eauto.
        intros; subst; eauto.
        intros; subst; eauto.
      Qed.

      Lemma mapi_of_list : forall B (f : _ -> _ -> B) ls, mapi f (of_list ls) == of_list (List.map (fun p => (fst p, f (fst p) (snd p))) ls).
        induction ls; simpl; intros.
        eapply mapi_empty.
        unfold uncurry; simpl in *.
        rewrite <- IHls.
        destruct a; simpl in *.
        eapply mapi_add.
      Qed.

      Lemma mapi_update : forall B (f : _ -> _ -> B) m1 m2, mapi f (m1 + m2) == mapi f m1 + mapi f m2.
        unfold Equal; intros.
        eapply option_univalence.
        split; intros.
        eapply find_2 in H.
        eapply mapi_mapsto_iff in H.
        openhyp.
        subst.
        eapply update_mapsto_iff in H0.
        openhyp.
        eapply find_1.
        eapply update_mapsto_iff.
        left.
        eapply mapi_mapsto_iff.
        intros; subst; eauto.
        eexists; eauto.
        eapply find_1.
        eapply update_mapsto_iff.
        right.
        split.
        eapply mapi_mapsto_iff.
        intros; subst; eauto.
        eexists; eauto.
        not_not.
        eapply mapi_in_iff; eauto.
        intros; subst; eauto.

        eapply find_2 in H.
        eapply update_mapsto_iff in H.
        openhyp.
        eapply mapi_mapsto_iff in H.
        openhyp.
        subst.
        eapply find_1.
        eapply mapi_mapsto_iff.
        intros; subst; eauto.
        eexists; split; eauto.
        eapply update_mapsto_iff.
        eauto.
        intros; subst; eauto.
        eapply mapi_mapsto_iff in H.
        openhyp.
        subst.
        eapply find_1.
        eapply mapi_mapsto_iff.
        intros; subst; eauto.
        eexists; split; eauto.
        eapply update_mapsto_iff.
        right.
        split; eauto.
        not_not.
        eapply mapi_in_iff; eauto.
        intros; subst; eauto.
      Qed.

      Lemma NoDupKey_app_all_elim : forall lsls, NoDupKey (app_all lsls) -> forall ls, List.In ls lsls -> NoDupKey ls.
        induction lsls; simpl; intuition.
        subst.
        eapply NoDupKey_unapp1; eauto.
        eapply IHlsls; eauto.
        eapply NoDupKey_unapp2; eauto.
      Qed.

      Lemma NoDupKey_app_all_AllCompat : forall lsls, NoDupKey (app_all lsls) -> AllCompat (List.map (@of_list _) lsls).
        induction lsls; simpl; intuition.
        econstructor.
        econstructor.
        eapply Forall_forall.
        intros.
        eapply in_map_iff in H0; openhyp; subst.
        eapply Disjoint_Compat.
        unfold Disjoint.
        intros.
        nintro.
        openhyp.
        eapply In_of_list in H0.
        eapply In_of_list in H2.
        generalize H; intros.
        eapply NoDupKey_app_DisjointKey in H.
        eapply H.
        split; eauto.
        unfold InKey in *.
        rewrite map_app_all.
        eapply In_app_all_intro; eauto.
        eapply in_map; eauto.
        eapply NoDupKey_unapp2 in H.
        eapply NoDupKey_app_all_elim; eauto.
        eapply NoDupKey_unapp1; eauto.
        eapply IHlsls.
        eapply NoDupKey_unapp2; eauto.
      Qed.

    End Elt.

    Lemma map_update_all_comm : forall elt B (f : elt -> B) ms, map f (update_all ms) == update_all (List.map (map f) ms).
      induction ms; simpl; intros.
      repeat rewrite update_all_nil.
      rewrite map_empty.
      eauto.
      repeat rewrite update_all_cons.
      rewrite map_update.
      rewrite IHms.
      eauto.
    Qed.


    Lemma mapi_update_all_comm : forall elt B (f : _ -> elt -> B) ms, mapi f (update_all ms) == update_all (List.map (mapi f) ms).
      induction ms; simpl; intros.
      repeat rewrite update_all_nil.
      rewrite mapi_empty; eauto.
      eauto.
      repeat rewrite update_all_cons.
      rewrite mapi_update.
      rewrite IHms.
      eauto.
    Qed.

    (* newly added from Facade *)

    Lemma find_Some_in : forall elt k m (v : elt), find k m = Some v -> In k m.
      intros; eapply MapsTo_In; eapply find_mapsto_iff; eauto.
    Qed.

    Lemma in_find_Some elt k m : In k m -> exists v : elt, find k m = Some v.
      intros H.
      eapply In_MapsTo in H.
      destruct H as [v H].
      eapply find_mapsto_iff in H.
      eauto.
    Qed.

    Lemma diff_disjoint elt m1 m2 : @Disjoint elt (m1 - m2) m2.
    Proof.
      unfold Disjoint.
      intros k.
      nintro.
      openhyp.
      eapply diff_in_iff in H.
      openhyp; intuition.
    Qed.

    Lemma Disjoint_in_not elt h1 h2 x : @Disjoint elt h1 h2 -> In x h1 -> ~ In x h2.
    Proof.
      intros Hdisj Hin1 Hin2.
      eapply Hdisj; eauto.
    Qed.

    Lemma diff_find_Some_iff : forall elt k (v : elt) m m', find k (m - m') = Some v <-> find k m = Some v /\ ~ In k m'.
      split; intros.
      eapply find_mapsto_iff in H.
      eapply diff_mapsto_iff in H; openhyp.
      eapply find_mapsto_iff in H.
      eauto.
      openhyp.
      eapply find_mapsto_iff.
      eapply diff_mapsto_iff.
      eapply find_mapsto_iff in H.
      eauto.
    Qed.

    Lemma diff_swap_find elt k (v : elt) h h1 h2 : find k (h - h1 - h2) = Some v -> find k (h - h2 - h1) = Some v.
    Proof.
      intros Hf.
      eapply diff_find_Some_iff in Hf.
      destruct Hf as [Hf Hni2].
      eapply diff_find_Some_iff in Hf.
      destruct Hf as [Hf Hni1].
      eapply diff_find_Some_iff.
      split.
      eapply diff_find_Some_iff.
      eauto.
      eauto.
    Qed.

    Lemma diff_swap elt (h h1 h2 : t elt) : h - h1 - h2 == h - h2 - h1.
    Proof.
      unfold Equal.
      intros k.
      eapply option_univalence.
      intros v; split; intros Hf; eapply diff_swap_find; eauto.
    Qed.

    Global Add Parametric Morphism elt : (@Submap elt)
        with signature Equal ==> Equal ==> iff as Submap_m.
    Proof.
      intros x y Hxy x' y' Hx'y'.
      unfold Submap.
      split; intros H.
      intros k v Hf.
      rewrite <- Hx'y' in *.
      rewrite <- Hxy in *.
      eauto.
      intros k v Hf.
      rewrite Hx'y' in *.
      rewrite Hxy in *.
      eauto.
    Qed.

    Lemma submap_trans elt (a b c : t elt) : a <= b -> b <= c -> a <= c.
    Proof.
      intros Hab Hbc; unfold Submap; intros k v Hf; eapply Hbc; eauto.
    Qed.

    Lemma submap_find : forall elt k (v : elt) m1 m2, m1 <= m2 -> find k m1 = Some v -> find k m2 = Some v.
      unfold Submap; eauto.
    Qed.

    Lemma submap_in elt h1 h2 : h1 <= h2 -> forall k, @In elt k h1 -> In k h2.
    Proof.
      intros Hsm k Hi.
      eapply in_find_Some in Hi.
      destruct Hi as [v Hf].
      eapply find_Some_in; eauto.
    Qed.

    Lemma diff_submap elt (m1 m2 : t elt) : m1 - m2 <= m1.
    Proof.
      unfold Submap.
      intros k v Hf.
      eapply diff_find_Some_iff in Hf; openhyp; eauto.
    Qed.

    Lemma submap_not_in : forall elt h1 h2, h1 <= h2 -> forall k, ~ @In elt k h2 -> ~ In k h1.
      intros; not_not; eapply submap_in; eauto.
    Qed.
    Lemma submap_diff elt (a b c : t elt) : c <= b -> b <= a -> a - b <= a - c.
    Proof.
      intros Hcb Hba.
      unfold Submap.
      intros k v Hf.
      eapply diff_find_Some_iff in Hf.
      destruct Hf as [Hf Hni].
      eapply diff_find_Some_iff.
      split.
      solve [eauto].
      solve [eapply submap_not_in; eauto].
    Qed.

    Lemma submap_restrict elt (h1 h2 h : t elt) : h1 <= h2 -> h1 - h <= h2 - h.
    Proof.
      unfold Submap; intros Hsml k v Hf.
      eapply diff_find_Some_iff in Hf; openhyp; rewrite diff_o; eauto.
    Qed.

    Import Bedrock.Platform.Cito.GeneralTactics4.

    Lemma submap_diff_diff elt (h1 h2 h3 : t elt) : h1 <= h2 -> h2 <= h3 -> h2 - h1 == (h3 - h1) - (h3 - h2).
    Proof.
      intros H12 H23.
      unfold Equal.
      intros k.
      eapply option_univalence.
      intros v; split; intros Hf.
      eapply diff_find_Some_iff in Hf.
      destruct Hf as [Hf Hni].
      eapply diff_find_Some_iff.
      split.
      eapply diff_find_Some_iff.
      split.
      eapply submap_find; eauto.
      eauto.
      not_not.
      eapply diff_in_iff in H.
      destruct H as [Hi3 Hni2].
      eapply find_Some_in in Hf; contradiction.
      eapply diff_find_Some_iff in Hf.
      destruct Hf as [Hf Hni].
      eapply diff_find_Some_iff in Hf.
      destruct Hf as [Hf Hni1].
      eapply diff_find_Some_iff.
      split.
      destruct (option_dec (find k h2)) as [[v' Hs] | Hn].
      copy Hs; eapply H23 in Hs; unif v'; eauto.
      eapply not_find_in_iff in Hn.
      contradict Hni.
      eapply diff_in_iff.
      split.
      eapply find_Some_in; eauto.
      eauto.
      eauto.
    Qed.

    Lemma submap_case elt h2 h12 : h2 <= h12 -> forall k (v : elt), find k h12 = Some v <-> find k (h12 - h2) = Some v \/ find k h2 = Some v.
    Proof.
      intros Hsm k v; split.
      intros Hf12.
      destruct (In_dec h2 k) as [Hin | Hni].
      right.
      eapply in_find_Some in Hin.
      destruct Hin as [v' Hf2].
      copy_as Hf2 Hf2'; eapply Hsm in Hf2'.
      unif v'.
      eauto.
      left.
      eapply diff_find_Some_iff; eauto.

      intros [Hfd | Hf2].
      eapply diff_find_Some_iff in Hfd; eauto.
      destruct Hfd as [Hf12 Hni].
      eauto.
      eapply Hsm; eauto.
    Qed.

    Lemma submap_disjoint_1 elt (h1 h2 h1' : t elt) : Disjoint h1 h2 -> h1' <= h1 -> Disjoint h1' h2.
    Proof.
      intros Hdisj Hsm.
      unfold Disjoint.
      intros k [Hin1 Hin2].
      eapply submap_in in Hin1; eauto.
      eapply Hdisj; eauto.
    Qed.

    Arguments submap_disjoint_1 [_] _ _ _ _ _ _ _.

    Lemma diff_submap_cancel elt (h1 h12 : t elt) : h1 <= h12 -> h12 - (h12 - h1) == h1.
    Proof.
      intros Hsm.
      unfold Equal.
      intros k.
      eapply option_univalence.
      intros v; split; intros Hf.
      eapply diff_find_Some_iff in Hf.
      destruct Hf as [Hf12 Hni].
      eapply submap_case in Hf12; eauto.
      openhyp.
      contradict Hni; eapply find_Some_in; eauto.
      eauto.
      eapply diff_find_Some_iff.
      split.
      eapply Hsm; eauto.
      intros Hin.
      eapply diff_in_iff in Hin.
      destruct Hin as [? Hni].
      contradict Hni; eapply find_Some_in; eauto.
    Qed.

    Global Add Parametric Morphism elt : (@direct_sum elt)
        with signature Equal ==> Equal ==> Equal ==> iff as direct_sum_m.
    Proof.
      intros.
      unfold direct_sum.
      rewrite H.
      rewrite H0.
      rewrite H1.
      intuition.
    Qed.

    Lemma direct_sum_disjoint elt h1 h2 h12 : direct_sum h1 h2 h12 -> @Disjoint elt h1 h2.
    Proof.
      intros H; destruct H; eauto.
    Qed.

    Lemma direct_sum_in_not elt h1 h2 h12 x : @direct_sum elt h1 h2 h12 -> In x h1 -> ~ In x h2.
    Proof.
      intros; eapply Disjoint_in_not; eauto.
      eapply direct_sum_disjoint; eauto.
    Qed.
    Arguments direct_sum_in_not [_] _ _ _ _ _ _ _.

    Lemma disjoint_update_iff elt h1 h2 : Disjoint h1 h2 -> forall k (v : elt), find k (h1 + h2) = Some v <-> find k h1 = Some v \/ find k h2 = Some v.
    Proof.
      intros Hdisj k v.
      split; intros Hf12.
      eapply find_mapsto_iff in Hf12.
      eapply update_mapsto_iff in Hf12.
      destruct Hf12 as [Hf2 | [Hf1 Hni2]].
      eapply find_mapsto_iff in Hf2.
      eauto.
      eapply find_mapsto_iff in Hf1.
      eauto.
      eapply find_mapsto_iff.
      eapply update_mapsto_iff.
      destruct Hf12 as [Hf1 | Hf2].
      right.
      split.
      eapply find_mapsto_iff; eauto.
      eapply Disjoint_in_not; eauto.
      eapply find_Some_in; eauto.
      left.
      eapply find_mapsto_iff; eauto.
    Qed.

    Lemma direct_sum_intro elt h1 h2 h12 : @Disjoint elt h1 h2 -> (forall k v, find k h12 = Some v <-> find k h1 = Some v \/ find k h2 = Some v) -> direct_sum h1 h2 h12.
    Proof.
      intros Hdisj Hiff.
      unfold direct_sum.
      split.
      unfold Equal.
      intros k.
      eapply option_univalence.
      intros v.
      etransitivity.
      2 : symmetry; eauto.
      eapply disjoint_update_iff; eauto.
      eauto.
    Qed.

    Lemma find_Some_direct_sum elt h1 h2 h12 : direct_sum h1 h2 h12 -> forall k (v : elt), find k h12 = Some v <-> find k h1 = Some v \/ find k h2 = Some v.
    Proof.
      intros Hds k v.
      destruct Hds as [Hheq Hdisj].
      rewrite <- Hheq.
      eapply disjoint_update_iff; eauto.
    Qed.

    Lemma diff_direct_sum elt (h2 h12 : t elt) : h2 <= h12 -> direct_sum (h12 - h2) h2 h12.
    Proof.
      intros Hsm.
      eapply direct_sum_intro.
      eapply diff_disjoint.
      eapply submap_case; eauto.
    Qed.

    Lemma direct_sum_submap elt (h1 h2 h12 : t elt) : direct_sum h1 h2 h12 -> h1 <= h12 /\ h2 <= h12.
      intros Hds.
      specialize (find_Some_direct_sum Hds).
      intros Hiff.
      unfold Submap.
      split; intros k v Hf; eapply Hiff; eauto.
    Qed.

    Arguments direct_sum_submap [_] _ _ _ _.

    Lemma direct_sum_sym elt (h1 h2 h12 : t elt) : direct_sum h1 h2 h12 -> direct_sum h2 h1 h12.
    Proof.
      intros Hds.
      specialize (find_Some_direct_sum Hds).
      intros Hiff.
      eapply direct_sum_intro.
      eapply Disjoint_sym; eapply direct_sum_disjoint; eauto.
      intros k v.
      etransitivity.
      eauto.
      intuition.
    Qed.

    Lemma direct_sum_submap_submap elt (h1 h12 h123 h2 : t elt) : h1 <= h12 -> h12 <= h123 -> h2 == h12 - h1 -> direct_sum h2 (h123 - h12) (h123 - h1).
    Proof.
      intros Hsm1 Hsm12 Heq2.
      eapply direct_sum_intro.
      rewrite Heq2.
      eapply submap_disjoint_1; eauto.
      2 : solve [eapply diff_submap; eauto].
      eapply Disjoint_sym; eapply diff_disjoint; eauto.
      intros k v; split.
      intros Hfd.
      eapply diff_find_Some_iff in Hfd; eauto.
      destruct Hfd as [Hf123 Hni1].
      eapply submap_case in Hf123; eauto.
      destruct Hf123 as [Hfd | Hf12].
      eauto.
      left.
      rewrite Heq2.
      eapply submap_case in Hf12; eauto.
      destruct Hf12 as [Hfd | Hf1].
      eauto.
      contradict Hni1; eapply find_Some_in; eauto.

      intros Hor.
      eapply diff_find_Some_iff.
      rewrite Heq2 in Hor.
      destruct Hor as [Hf2 | Hfd].
      eapply diff_find_Some_iff in Hf2.
      openhyp.
      split.
      eapply Hsm12; eauto.
      eauto.
      eapply diff_find_Some_iff in Hfd.
      openhyp.
      split.
      eauto.
      not_not.
      eapply submap_in; eauto.
    Qed.

    Fixpoint make_map {elt} keys values :=
      match keys, values with
        | k :: keys', v :: values' => add k v (make_map keys' values')
        | _, _ => @empty elt
      end.

    Lemma make_map_in elt ks : forall (vs : list elt) k, In k (make_map ks vs) -> List.In k ks.
    Proof.
      induction ks; destruct vs; simpl; intros k' Hi.
      eapply empty_in_iff in Hi; contradiction.
      eapply empty_in_iff in Hi; contradiction.
      eapply empty_in_iff in Hi; contradiction.
      rename a into k.
      eapply add_in_iff in Hi.
      destruct Hi as [He | Hi].
      subst; eauto.
      right; eauto.
    Qed.

    Lemma make_map_not_in elt k ks (vs : list elt) : ~ List.In k ks -> ~ In k (make_map ks vs).
    Proof.
      intros; not_not.
      rename H0 into H.
      eapply make_map_in; eauto.
    Qed.

    Lemma make_map_find_None A k ks (vs : list A) :
      ~ List.In k ks ->
      find k (make_map ks vs) = None.
    Proof.
      intros H.
      eapply make_map_not_in in H.
      eapply not_find_in_iff; eauto.
    Qed.

    Lemma make_map_Equal_elim A :
      forall ks (vs vs' : list A),
        NoDup ks ->
        length vs = length ks ->
        length vs' = length ks ->
        make_map ks vs == make_map ks vs' ->
        vs = vs'.
    Proof.
      induction ks; destruct vs; destruct vs'; simpl; try solve [intros; intuition; try discriminate].
      intros Hnd Hlen Hlen' Heqv.
      inversion Hnd; subst.
      inject Hlen.
      inject Hlen'.
      rename a into k.
      f_equal.
      {
        unfold Equal in *.
        specialize (Heqv k).
        repeat rewrite add_eq_o in * by eauto.
        inject Heqv.
        eauto.
      }
      eapply IHks; eauto.
      unfold Equal in *.
      intros k'.
      destruct (eq_dec k' k) as [? | Hne]; subst.
      {
        repeat rewrite make_map_find_None by eauto.
        eauto.
      }
      specialize (Heqv k').
      repeat rewrite add_neq_o in * by eauto.
      eauto.
    Qed.

    Fixpoint make_mapM {elt} keys values :=
      match keys, values with
        | k :: keys', v :: values' =>
          match v with
            | Some a => add k a (make_mapM keys' values')
            | None => make_mapM keys' values'
          end
        | _, _ => @empty elt
      end.

    Import Bedrock.Platform.Cito.ListFacts4.

    Lemma in_make_mapM_iff elt ks : forall vs k, length ks = length vs -> (In k (make_mapM ks vs) <-> exists i (a : elt), nth_error ks i = Some k /\ nth_error vs i = Some (Some a)).
    Proof.
      induction ks; try (rename a into k'); destruct vs as [|v' vs]; simpl; intros k Hl; (split; [intros Hi | intros Hex]); try discriminate.
      eapply empty_in_iff in Hi; contradiction.
      destruct Hex as [i [a [Hk Hv]]]; rewrite nth_error_nil in *; discriminate.

      inject Hl.
      destruct v' as [a' | ].
      eapply add_in_iff in Hi.
      destruct Hi as [Heq | Hi].
      subst.
      solve [exists 0, a'; eauto].
      solve [eapply IHks in Hi; eauto; destruct Hi as [i [a [Hk Hv]]]; exists (S i), a; eauto].
      solve [eapply IHks in Hi; eauto; destruct Hi as [i [a [Hk Hv]]]; exists (S i), a; eauto].

      inject Hl.
      destruct Hex as [i [a [Hk Hv]]].
      destruct i as [ | i]; simpl in *.
      inject Hk.
      inject Hv.
      eapply add_in_iff; eauto.
      destruct v' as [a' |].
      eapply add_in_iff.
      right.
      eapply IHks; eauto.
      eapply IHks; eauto.
    Qed.

    Definition no_dupM elt ks vs := forall i j (k : key) (ai aj : elt), nth_error ks i = Some k -> nth_error vs i = Some (Some ai) -> nth_error ks j = Some k -> nth_error vs j = Some (Some aj) -> i = j.

    Lemma no_dupM_cons_elim elt ks vs k (v : option elt) : no_dupM (k :: ks) (v :: vs) -> no_dupM ks vs.
    Proof.
      unfold no_dupM.
      intros Hnd i j k' ai aj Hik Hiv Hjk Hjv.
      assert (S i = S j).
      eapply Hnd; eauto; simpl; eauto.
      inject H; eauto.
    Qed.

    Lemma find_Some_make_mapM_iff elt ks : forall vs k (a : elt), length ks = length vs -> no_dupM ks vs -> (find k (make_mapM ks vs) = Some a <-> exists i, nth_error ks i = Some k /\ nth_error vs i = Some (Some a)).
    Proof.
      induction ks; try (rename a into k'); destruct vs as [ | v' vs]; simpl in *; intros k a Hl Hnd; (split; [intros Hi | intros Hex]); try rewrite empty_o in *; try discriminate.
      destruct Hex as [i [Hk Hv]]; rewrite nth_error_nil in *; discriminate.

      inject Hl.
      destruct v' as [a' | ].
      destruct (eq_dec k k') as [Heq | Hne].
      subst.
      rewrite add_eq_o in * by eauto.
      inject Hi.
      solve [exists 0; eauto].
      rewrite add_neq_o in * by eauto.
      eapply IHks in Hi; eauto.
      solve [destruct Hi as [i [Hk Hv]]; exists (S i); eauto].
      solve [eapply no_dupM_cons_elim; eauto].
      eapply IHks in Hi; eauto.
      solve [destruct Hi as [i [Hk Hv]]; exists (S i); eauto].
      solve [eapply no_dupM_cons_elim; eauto].

      inject Hl.
      destruct Hex as [i [Hk Hv]].
      destruct i as [ | i]; simpl in *.
      inject Hk.
      inject Hv.
      rewrite add_eq_o in * by eauto.
      solve [eauto].
      destruct v' as [a' |].
      destruct (eq_dec k k') as [Heq | Hne].
      subst.
      assert (0 = S i).
      eapply Hnd; eauto; simpl; eauto.
      discriminate.
      rewrite add_neq_o in * by eauto.
      eapply IHks; eauto.
      solve [eapply no_dupM_cons_elim; eauto].
      eapply IHks; eauto.
      solve [eapply no_dupM_cons_elim; eauto].
    Qed.

    Lemma add_new_submap elt k m : ~ In k m -> forall (v : elt), m <= add k v m.
    Proof.
      intros Hni v.
      unfold Submap.
      intros k' v' Hf.
      destruct (eq_dec k' k).
      subst.
      contradict Hni.
      eapply find_Some_in; eauto.
      rewrite add_neq_o by eauto; eauto.
    Qed.

    Lemma NoDup_elements elt (m : t elt) : NoDup (List.map fst (elements m)).
    Proof.
      eapply NoDupKey_NoDup_fst.
      eapply elements_3w.
    Qed.

    Lemma add_eq_elim elt k (v1 v2 : elt) m1 m2 : add k v1 m1 == add k v2 m2 -> v1 = v2 /\ remove k m1 == remove k m2.
    Proof.
      intros Heq.
      unfold Equal in *.
      split.
      - specialize (Heq k).
        rewrite add_eq_o in * by eauto.
        rewrite add_eq_o in * by eauto.
        inject Heq; eauto.
      - intros k'.
        destruct (eq_dec k' k).
        + subst.
          repeat rewrite remove_eq_o by eauto.
          eauto.
        + repeat rewrite remove_neq_o by eauto.
          specialize (Heq k').
          rewrite add_neq_o in * by eauto.
          rewrite add_neq_o in * by eauto.
          eauto.
    Qed.

    Lemma add_add_comm elt k k' (v v' : elt) m : k <> k' -> add k v (add k' v' m) == add k' v' (add k v m).
    Proof.
      intros Hne.
      unfold Equal.
      intros k''.
      destruct (eq_dec k'' k).
      - subst.
        rewrite add_eq_o by eauto.
        destruct (eq_dec k k').
        + subst.
          intuition.
        + rewrite add_neq_o by eauto.
          rewrite add_eq_o by eauto.
          eauto.
      - rewrite add_neq_o by eauto.
        destruct (eq_dec k'' k').
        + subst.
          rewrite add_eq_o by eauto.
          rewrite add_eq_o by eauto.
          eauto.
        + rewrite add_neq_o by eauto.
          rewrite add_neq_o by eauto.
          rewrite add_neq_o by eauto.
          eauto.
    Qed.

    Global Arguments add_add_comm [elt] k k' _ _ _ _ _.

    Lemma remove_add_comm elt k k' (v' : elt) m : k <> k' -> remove k (add k' v' m) == add k' v' (remove k m).
    Proof.
      intros Hne.
      unfold Equal.
      intros k''.
      destruct (eq_dec k'' k).
      - subst.
        rewrite remove_eq_o by eauto.
        destruct (eq_dec k k').
        + subst.
          intuition.
        + rewrite add_neq_o by eauto.
          rewrite remove_eq_o by eauto.
          eauto.
      - rewrite remove_neq_o by eauto.
        destruct (eq_dec k'' k').
        + subst.
          rewrite add_eq_o by eauto.
          rewrite add_eq_o by eauto.
          eauto.
        + rewrite add_neq_o by eauto.
          rewrite add_neq_o by eauto.
          rewrite remove_neq_o by eauto.
          eauto.
    Qed.

    Lemma add_remove_comm elt k k' (v : elt) m : k <> k' -> add k v (remove k' m) == remove k' (add k v m).
    Proof.
      intros Hne.
      unfold Equal.
      intros k''.
      destruct (eq_dec k'' k).
      - subst.
        rewrite add_eq_o by eauto.
        destruct (eq_dec k k').
        + subst.
          intuition.
        + rewrite remove_neq_o by eauto.
          rewrite add_eq_o by eauto.
          eauto.
      - rewrite add_neq_o by eauto.
        destruct (eq_dec k'' k').
        + subst.
          rewrite remove_eq_o by eauto.
          rewrite remove_eq_o by eauto.
          eauto.
        + rewrite remove_neq_o by eauto.
          rewrite remove_neq_o by eauto.
          rewrite add_neq_o by eauto.
          eauto.
    Qed.

    Lemma remove_remove_comm elt k k' (m : t elt) : k <> k' -> remove k (remove k' m) == remove k' (remove k m).
    Proof.
      intros Hne.
      unfold Equal.
      intros k''.
      destruct (eq_dec k'' k).
      - subst.
        rewrite remove_eq_o by eauto.
        destruct (eq_dec k k').
        + subst.
          intuition.
        + rewrite remove_neq_o by eauto.
          rewrite remove_eq_o by eauto.
          eauto.
      - rewrite remove_neq_o by eauto.
        destruct (eq_dec k'' k').
        + subst.
          rewrite remove_eq_o by eauto.
          rewrite remove_eq_o by eauto.
          eauto.
        + rewrite remove_neq_o by eauto.
          rewrite remove_neq_o by eauto.
          rewrite remove_neq_o by eauto.
          eauto.
    Qed.
    Global Arguments remove_remove_comm [elt] k k' _ _ _.

    Lemma add_remove_eq_false elt k (v : elt) m1 m2 : ~ add k v m1 == remove k m2.
    Proof.
      intro H.
      unfold Equal in *.
      specialize (H k).
      rewrite add_eq_o in * by eauto.
      rewrite remove_eq_o in * by eauto.
      discriminate.
    Qed.

    Section EqualOn.

      Variable Domain : key -> Prop.

      Variable elt : Type.

      Definition EqualOn (m1 m2 : t elt) := forall k, Domain k -> find k m1 = find k m2.

      Lemma EqualOn_refl a : EqualOn a a.
      Proof.
        unfold EqualOn.
        eauto.
      Qed.

      Lemma EqualOn_sym a b : EqualOn a b -> EqualOn b a.
      Proof.
        intros H.
        unfold EqualOn in *; intros.
        symmetry; eauto.
      Qed.

      Lemma EqualOn_trans a b c : EqualOn a b -> EqualOn b c -> EqualOn a c.
      Proof.
        intros H1 H2.
        unfold EqualOn in *; intros.
        etransitivity.
        - eapply H1; eauto.
        - eauto.
      Qed.

      Global Add Relation (t elt) EqualOn
          reflexivity proved by EqualOn_refl
          symmetry proved by EqualOn_sym
          transitivity proved by EqualOn_trans
            as EqualOn_rel.

      Lemma Equal_EqualOn a a' b b' : a == a' -> b == b' -> (EqualOn a b <-> EqualOn a' b').
      Proof.
        intros Ha Hb.
        split; intros H.
        - unfold EqualOn in *.
          intros k Hk.
          rewrite <- Ha.
          rewrite <- Hb.
          eapply H; eauto.
        - unfold EqualOn in *.
          intros k Hk.
          rewrite Ha.
          rewrite Hb.
          eapply H; eauto.
      Qed.

      Global Add Morphism EqualOn
          with signature Equal ==> Equal ==> iff as Equal_EqualOn_m.
      Proof.
        intros; eapply Equal_EqualOn; eauto.
      Qed.

      Lemma add_EqualOn k v m1 m2 : EqualOn m1 m2 -> EqualOn (add k v m1) (add k v m2).
      Proof.
        intros Heq.
        unfold EqualOn in *.
        intros k' Hk'.
        destruct (eq_dec k' k) as [Heqk | Hnek].
        - subst.
          repeat rewrite add_eq_o by eauto.
          eauto.
        - repeat rewrite add_neq_o by eauto.
          eauto.
      Qed.

      Lemma remove_EqualOn k m1 m2 : EqualOn m1 m2 -> EqualOn (remove k m1) (remove k m2).
      Proof.
        intros Heq.
        unfold EqualOn in *.
        intros k' Hk'.
        destruct (eq_dec k' k) as [Heqk | Hnek].
        - subst.
          repeat rewrite remove_eq_o by eauto.
          eauto.
        - repeat rewrite remove_neq_o by eauto.
          eauto.
      Qed.

      Global Add Morphism (@add elt) with signature eq ==> eq ==> EqualOn ==> EqualOn as add_EqualOn_m.
      Proof.
        intros; eapply add_EqualOn; eauto.
      Qed.

      Global Add Morphism (@remove elt) with signature eq ==> EqualOn ==> EqualOn as remove_EqualOn_m.
      Proof.
        intros; eapply remove_EqualOn; eauto.
      Qed.

      Lemma out_add_EqualOn a b k v : EqualOn a b -> ~ Domain k -> EqualOn (add k v a) b.
      Proof.
        intros Heq Hk.
        unfold EqualOn in *.
        intros k' Hk'.
        destruct (eq_dec k' k) as [? | Hne].
        - subst.
          contradiction.
        - rewrite add_neq_o by eauto.
          eapply Heq; eauto.
      Qed.

    End EqualOn.

    Lemma empty_submap elt m : @empty elt <= m.
    Proof.
      intros k v Hin.
      rewrite empty_o in Hin.
      discriminate.
    Qed.

    Definition sub_domain elt1 elt2 (m1 : t elt1) (m2 : t elt2) := forall k, In k m1 -> In k m2.

    Definition equal_domain elt1 elt2 (m1 : t elt1) (m2 : t elt2) := sub_domain m1 m2 /\ sub_domain m2 m1.

    Definition is_sub_domain elt1 elt2 (m1 : t elt1) (m2 : t elt2) := forallb (fun k => mem k m2) (keys m1).

    Import Bedrock.Platform.Cito.SetoidListFacts.

    Lemma is_sub_domain_sound : forall elt1 elt2 (m1 : t elt1) (m2 : t elt2), is_sub_domain m1 m2 = true -> sub_domain m1 m2.
      intros.
      unfold is_sub_domain, sub_domain in *.
      intros.
      eapply forallb_forall in H.
      eapply mem_in_iff; eauto.
      eapply InA_In.
      eapply In_In_keys; eauto.
    Qed.

    Lemma is_sub_domain_complete : forall elt1 elt2 (m1 : t elt1) (m2 : t elt2), sub_domain m1 m2 -> is_sub_domain m1 m2 = true.
    Proof.
      intros.
      unfold is_sub_domain, sub_domain in *.
      eapply forallb_forall.
      intros k Hin.
      eapply mem_in_iff; eauto.
      eapply H.
      Require Import SetoidListFacts.
      eapply In_InA in Hin.
      eapply In_In_keys; eauto.     
    Qed.

    Definition equal_domain_dec elt1 elt2 (m1 : t elt1) (m2 : t elt2) := (is_sub_domain m1 m2 && is_sub_domain m2 m1)%bool.

    Lemma equal_domain_dec_sound : forall elt1 elt2 (m1 : t elt1) (m2 : t elt2), equal_domain_dec m1 m2 = true -> equal_domain m1 m2.
      unfold equal_domain_dec, equal_domain; intros.
      eapply Bool.andb_true_iff in H; openhyp.
      eapply is_sub_domain_sound in H.
      eapply is_sub_domain_sound in H0.
      eauto.
    Qed.

    Lemma in_elements_find elt k (v : elt) d : List.In (k, v) (elements d) -> find k d = Some v.
    Proof.
      intros H.
      eapply InA_eqke_In in H.
      eapply elements_2 in H.
      eapply find_mapsto_iff; eauto.
    Qed.

    Lemma find_in_elements elt k (v : elt) d : find k d = Some v -> List.In (k, v) (elements d).
    Proof.
      intros H.
      eapply InA_eqke_In.
      eapply elements_1.
      eapply find_mapsto_iff; eauto.
    Qed.

    Lemma submap_diff_empty_equal elt a b : a <= b -> b - a == empty elt -> b == a.
    Proof.
      intros Hsm Hdiff.
      intros k.
      destruct (option_dec (find k a)) as [ [v Hv] | Hnone].
      {
        rewrite Hv.
        eapply Hsm; eauto.
      }
      rewrite Hnone.
      destruct (option_dec (find k b)) as [ [v Hv] | Hnone'].
      {
        assert (MapsTo k v (b - a)).
        {
          eapply diff_mapsto_iff.
          split.
          - eapply find_mapsto_iff; eauto.
          - eapply not_find_in_iff; eauto.
        }
        rewrite Hdiff in H.
        eapply empty_mapsto_iff in H.
        intuition.
      }
      eauto.
    Qed.

    Lemma submap_refl elt (m : t elt) : m <= m.
    Proof.
      intros k.
      intros; eauto.
    Qed.

    Lemma sub_domain_refl A a : @sub_domain A A a a.
    Proof.
      intros k; eauto.
    Qed.

    Lemma sub_domain_update_1 A B a b c : @sub_domain A B a b -> sub_domain a (b + c).
    Proof.
      intros Hsd.
      intros k H.
      eapply update_in_iff.
      left; eauto.
    Qed.

    Lemma sub_domain_update_2 A B a b c : @sub_domain A B a c -> sub_domain a (b + c).
    Proof.
      intros Hsd.
      intros k H.
      eapply update_in_iff.
      right; eauto.
    Qed.

    Lemma sub_domain_map_1 A B C (f : A -> C) a b : @sub_domain A B a b -> sub_domain (map f a) b.
    Proof.
      intros Hsd.
      intros k H.
      eapply map_4 in H; eauto.
    Qed.

    Lemma sub_domain_map_2 A B C (f : B -> C) a b : @sub_domain A B a b -> sub_domain a (map f b).
    Proof.
      intros Hsd.
      intros k H.
      eapply map_3; eauto.
    Qed.

    Lemma sub_domain_update_sub_domain A a b : @sub_domain A A b a -> sub_domain (a + b) a.
    Proof.
      intros Hsd.
      intros k H.
      eapply update_in_iff in H.
      intuition.
    Qed.

    Arguments empty {elt}.

    Definition filterM_f {A B} (f : key -> A -> option B) k v acc := match f k v with | Some v' => add k v' acc | None => acc end.

    Definition filterM A B (f : key -> A -> option B) d :=  fold (filterM_f f) d empty.

    Lemma filterM_elim A B f k (b : B) d : find k (filterM f d) = Some b -> exists a : A, find k d = Some a /\ f k a = Some b.
    Proof.
      unfold filterM.
      eapply fold_rec_bis.
      {
        intros m1 m2 a Heq H1 H.
        rewrite <- Heq.
        eauto.
      }
      {
        intros H.
        rewrite empty_o in H.
        discriminate.
      }
      {
        intros k' e a d'.
        intros Hk' Hnin H1 H.
        unfold filterM_f in *.
        destruct (option_dec (f k' e)) as [ [v Heq] | Heq ]; rewrite Heq in *.
        {
          destruct (eq_dec k k') as [? | Hneq].
          {
            subst.
            rewrite add_eq_o in H by eauto.
            inject H.
            exists e.
            split; eauto.
            rewrite add_eq_o by eauto.
            eauto.
          }
          {
            rewrite add_neq_o in H by eauto.
            eapply H1 in H.
            destruct H as [v' [H Heq'] ].
            exists v'; split; eauto.
            rewrite add_neq_o by eauto.
            eauto.
          }
        }
        {
          eapply H1 in H.
          destruct H as [v [H Heq'] ].
          destruct (eq_dec k k') as [? | Hneq].
          {
            subst.
            contradict Hnin.
            eapply find_Some_in; eauto.
          }
          {
            exists v; split; eauto.
            rewrite add_neq_o by eauto; eauto.
          }
        }
      }
    Qed.

    Definition inter elt1 elt2 (d1 : t elt1) (d2 : t elt2) := filterM (fun k v1 => match find k d2 with | Some v2 => Some (v1, v2) | None => None end ) d1.

    Lemma find_inter_elim A B k d1 d2 (v1 : A) (v2 : B) : find k (inter d1 d2) = Some (v1, v2) -> find k d1 = Some v1 /\ find k d2 = Some v2.
    Proof.
      intros H.
      unfold inter in *.
      eapply filterM_elim in H.
      destruct H as [v1' [H1 H2] ].
      destruct (option_dec (find k d2)) as [ [v2' Heq] | Heq ]; rewrite Heq in *.
      {
        inject H2.
        eauto.
      }
      discriminate.
    Qed.

    Lemma singleton_in_iff elt k' k (v : elt) : In k' (add k v empty) <-> k = k'.
    Proof.
      split; intros H.
      {
        eapply add_in_iff in H.
        destruct H as [? | H]; trivial.
        eapply empty_in_iff in H; intuition.
      }
      subst.
      eapply add_in_iff; eauto.
    Qed.

    Lemma add_diff_singleton elt k (v : elt) d : ~ In k d -> add k v d - add k v empty == d.
    Proof.
      intros Hnin.
      intros k'.
      destruct (eq_dec k' k) as [? | Heq].
      {
        subst.
        rewrite diff_o_none.
        - eapply not_find_in_iff in Hnin; eauto.
        - eapply add_in_iff; eauto.
      }
      {
        rewrite diff_o.
        - rewrite add_neq_o by eauto; eauto.
        - intros Hin.
          eapply singleton_in_iff in Hin.
          subst; intuition.
      }
    Qed.

    Definition Disjoint2 {A B} (m1 : t A) (m2 : t B) := forall k, In k m1 -> ~ In k m2.

  End TopSection.

End UWFacts_fun.
