Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Bedrock.Platform.Cito.ListFacts1 Bedrock.Platform.Cito.ListFacts2 Bedrock.Platform.Cito.ListFacts3.
Require Import Bedrock.ListFacts.
Require Import Bedrock.Platform.Cito.GeneralTactics.
Require Import Bedrock.Platform.Cito.GeneralTactics4.
Require Import Bedrock.Platform.Cito.Option.

Lemma combine_length_eq A B (ls1 : list A) : forall (ls2 : list B), length ls1 = length ls2 -> length (combine ls1 ls2) = length ls1.
Proof.
  induction ls1; destruct ls2; simpl in *; intros; intuition.
Qed.

Lemma nth_error_combine A B ls1 : forall ls2 i (a : A) (b : B), nth_error ls1 i = Some a -> nth_error ls2 i = Some b -> nth_error (combine ls1 ls2) i = Some (a, b).
Proof.
  induction ls1; destruct ls2; destruct i; simpl in *; intros; try discriminate.
  inject H; inject H0; eauto.
  eauto.
Qed.

Lemma nth_error_combine_elim A B ls1 : forall ls2 i (a : A) (b : B), nth_error (combine ls1 ls2) i = Some (a, b) -> nth_error ls1 i = Some a /\ nth_error ls2 i = Some b.
Proof.
  induction ls1; destruct ls2; destruct i; simpl in *; intros; try discriminate.
  inject H; eauto.
  eauto.
Qed.

Lemma nth_error_map_elim : forall A B (f : A -> B) ls i b, nth_error (List.map f ls) i = Some b -> exists a, nth_error ls i = Some a /\ f a = b.
  intros.
  rewrite ListFacts.map_nth_error_full in H.
  destruct (option_dec (nth_error ls i)).
  destruct s; rewrite e in *; inject H; eexists; eauto.
  rewrite e in *; discriminate.
Qed.

Lemma map_nth_error_1 : forall A B (f : A -> B) ls1 ls2 i a, List.map f ls1 = ls2 -> nth_error ls1 i = Some a -> nth_error ls2 i = Some (f a).
  intros.
  rewrite <- H.
  erewrite map_nth_error; eauto.
Qed.

Lemma map_nth_error_2 A B (f : A -> B) ls1 : forall ls2 i b, List.map f ls1 = ls2 -> nth_error ls2 i = Some b -> exists a, nth_error ls1 i = Some a /\ f a = b.
Proof.
  induction ls1; destruct ls2; destruct i; simpl in *; intros; try discriminate.
  inject H; inject H0; eexists; eauto.
  inject H; eauto.
Qed.

Lemma map_eq_nth_error_1 : forall A1 A2 B (f1 : A1 -> B) (f2 : A2 -> B) ls1 ls2 i a1, List.map f1 ls1 = List.map f2 ls2 -> nth_error ls1 i = Some a1 -> exists a2, nth_error ls2 i = Some a2 /\ f1 a1 = f2 a2.
  intros.
  eapply map_nth_error_1 in H; eauto.
  eapply nth_error_map_elim in H; openhyp.
  eexists; eauto.
Qed.

Lemma in_nth_error A ls : forall (a : A), List.In a ls -> exists i, nth_error ls i = Some a.
Proof.
  induction ls; simpl in *; intros.
  intuition.
  openhyp.
  subst.
  exists 0; eauto.
  eapply IHls in H; eauto.
  openhyp.
  exists (S x); eauto.
Qed.

Lemma nth_error_nil A i : nth_error (@nil A) i = None.
Proof.
  destruct i; simpl in *; eauto.
Qed.

Fixpoint mapM A B (f : A -> option B) ls :=
  match ls with
    | x :: xs =>
      match f x, mapM f xs with
        | Some y, Some ys => Some (y :: ys)
        | _, _ => None
      end
    | nil => Some nil
  end.

Lemma mapM_length A B (f : A -> option B) ls1 : forall ls2, mapM f ls1 = Some ls2 -> length ls1 = length ls2.
Proof.
  induction ls1; destruct ls2; simpl in *; intros; try discriminate.
  eauto.
  destruct (option_dec (f a)) as [[y Hy] | Hnone].
  rewrite Hy in *.
  destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
  rewrite Hys in *.
  discriminate.
  rewrite Hnone in *; discriminate.
  rewrite Hnone in *; discriminate.

  f_equal.
  destruct (option_dec (f a)) as [[y Hy] | Hnone].
  rewrite Hy in *.
  destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
  rewrite Hys in *.
  inject H; eauto.
  rewrite Hnone in *; discriminate.
  rewrite Hnone in *; discriminate.
Qed.

Lemma mapM_nth_error_1 A B (f : A -> option B) ls1 : forall ls2 i a, mapM f ls1 = Some ls2 -> nth_error ls1 i = Some a -> exists b, nth_error ls2 i = Some b /\ f a = Some b.
Proof.
  induction ls1; destruct ls2; destruct i; simpl in *; intros; try discriminate.
  destruct (option_dec (f a)) as [[y Hy] | Hnone].
  rewrite Hy in *.
  destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
  rewrite Hys in *.
  discriminate.
  rewrite Hnone in *; discriminate.
  rewrite Hnone in *; discriminate.
  destruct (option_dec (f a)) as [[y Hy] | Hnone].
  rewrite Hy in *.
  destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
  rewrite Hys in *.
  discriminate.
  rewrite Hnone in *; discriminate.
  rewrite Hnone in *; discriminate.
  destruct (option_dec (f a)) as [[y Hy] | Hnone].
  rewrite Hy in *.
  destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
  rewrite Hys in *.
  inject H; inject H0; eexists; eauto.
  rewrite Hnone in *; discriminate.
  rewrite Hnone in *; discriminate.
  destruct (option_dec (f a)) as [[y Hy] | Hnone].
  rewrite Hy in *.
  destruct (option_dec (mapM f ls1)) as [[ys Hys] | Hnone].
  rewrite Hys in *.
  inject H; eauto.
  rewrite Hnone in *; discriminate.
  rewrite Hnone in *; discriminate.
Qed.

Lemma length_eq_nth_error A B ls1 : forall ls2 i (a : A), nth_error ls1 i = Some a -> length ls1 = length ls2 -> exists b : B, nth_error ls2 i = Some b.
Proof.
  induction ls1; destruct ls2; destruct i; simpl in *; intros; try discriminate.
  inject H; inject H0; eexists; eauto.
  inject H0; eauto.
Qed.

Lemma mapM_nth_error_2 A B (f : A -> option B) ls1 ls2 i a2 : mapM f ls1 = Some ls2 -> nth_error ls2 i = Some a2 -> exists a1, nth_error ls1 i = Some a1 /\ f a1 = Some a2.
Proof.
  intros Hmm Ha2.
  copy_as Ha2 Ha2'; eapply length_eq_nth_error in Ha2'.
  2 : symmetry; eapply mapM_length; eauto.
  destruct Ha2' as [a1 Ha1].
  eapply mapM_nth_error_1 in Hmm; eauto.
  destruct Hmm as [a2' [Ha2' Hf]].
  unif a2'.
  rewrite <- Hf in *.
  eexists; eauto.
Qed.

Lemma cons_incl_elim A (a : A) ls1 ls2 : incl (a :: ls1) ls2 -> List.In a ls2 /\ incl ls1 ls2.
Proof.
  unfold incl.
  intros Hincl.
  split.
  eapply Hincl.
  eapply in_eq.
  intros a' Hin.
  eapply Hincl.
  eapply in_cons; eauto.
Qed.

Lemma incl_nth_error A ls1 : forall i ls2 (a : A), List.incl ls1 ls2 -> nth_error ls1 i = Some a -> exists i', nth_error ls2 i' = Some a.
Proof.
  induction ls1; destruct i; simpl in *; intros; try discriminate.
  inject H0.
  eapply cons_incl_elim in H.
  openhyp.
  eapply in_nth_error; eauto.
  eapply IHls1; eauto.
  eapply cons_incl_elim in H.
  openhyp.
  eauto.
Qed.

Lemma combine_map A B C (f1 : A -> B) (f2 : A -> C) ls : combine (List.map f1 ls) (List.map f2 ls) = List.map (fun x => (f1 x, f2 x)) ls.
Proof.
  induction ls; simpl in *; intros; try f_equal; eauto.
Qed.

Lemma nth_error_In : forall A (x : A) ls n,
                       nth_error ls n = Some x
                       -> In x ls.
  induction ls; destruct n; simpl; intuition; try discriminate; eauto.
  injection H; intros; subst; auto.
Qed.

Lemma NoDup_nth_error A ls : NoDup ls -> forall i i' (x : A), nth_error ls i = Some x -> nth_error ls i' = Some x -> i = i'.
Proof.
  induction 1; destruct i; destruct i'; simpl in *; intros; try discriminate.
  eauto.
  inject H1.
  contradict H; eapply nth_error_In; eauto.
  inject H2.
  contradict H; eapply nth_error_In; eauto.
  f_equal; eauto.
Qed.

Arguments fst {A B} _ .
Arguments snd {A B} _ .

Lemma map_fst_combine A B (ls1 : list A) : forall (ls2 : list B), length ls1 = length ls2 -> List.map fst (combine ls1 ls2) = ls1.
  induction ls1; destruct ls2; simpl in *; intros; try discriminate; intuition.
  f_equal; eauto.
Qed.

Lemma map_snd_combine A B (ls1 : list A) : forall (ls2 : list B), length ls1 = length ls2 -> List.map snd (combine ls1 ls2) = ls2.
  induction ls1; destruct ls2; simpl in *; intros; try discriminate; intuition.
  f_equal; eauto.
Qed.

Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

Global Add Parametric Morphism A B : (@List.map A B)
    with signature pointwise_relation A eq ==> eq ==> eq as list_map_m.
Proof.
  intros; eapply map_ext; eauto.
Qed.

Lemma In_map_ext A B (f g : A -> B) : forall ls, (forall x, List.In x ls -> f x = g x) -> List.map f ls = List.map g ls.
Proof.
  induction ls; simpl; intros Hfg; trivial.
  f_equal.
  {
    eapply Hfg.
    eauto.
  }
  eapply IHls.
  intuition.
Qed.

Lemma in_singleton_iff A (x' x : A) : List.In x' (x :: nil) <-> x' = x.
Proof.
  intros; subst; simpl in *; intuition.
Qed.

Require Import Bedrock.Platform.Cito.GeneralTactics2.

Lemma singleton_iff_not : forall elt (e e' : elt), ~ List.In e' (e :: nil) <-> e <> e'.
  unfold List.In; split; intros; not_not; intuition.
Qed.

Lemma combine_fst_snd A B (pairs : list (A * B)) : List.combine (List.map fst pairs) (List.map snd pairs) = pairs.
Proof.
  rewrite combine_map.
  setoid_rewrite <- surjective_pairing.
  rewrite map_id.
  eauto.
Qed.

Lemma map_eq_length_eq : forall A B C (f1 : A -> B) ls1 (f2 : C -> B) ls2, map f1 ls1 = map f2 ls2 -> length ls1 = length ls2.
  intros; assert (length (map f1 ls1) = length (map f2 ls2)) by congruence; repeat rewrite map_length in *; eauto.
Qed.

Lemma Forall_forall_1 A P (ls : list A) : Forall P ls -> (forall x, List.In x ls -> P x).
  intros; eapply Forall_forall; eauto.
Qed.
