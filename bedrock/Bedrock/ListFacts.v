Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Bedrock.Tactics.
Require Import Bedrock.Reflection.

Lemma skipn_length_gt : forall T (ls : list T) n,
  length ls <= n ->
  skipn n ls = nil.
Proof.
  induction ls; destruct n; simpl; intuition; auto. exfalso; omega.
Qed.

Lemma skipn_length_all : forall T U (F : T -> U) ls ls',
  map F ls = ls' ->
  skipn (length ls) ls' = nil.
Proof.
  intros. eapply skipn_length_gt. rewrite <- H. rewrite map_length. omega.
Qed.

Lemma rw_skipn_app : forall T (ls ls' : list T) n,
  length ls = n ->
  skipn n (ls ++ ls') = ls'.
Proof.
  clear. induction ls; destruct n; simpl in *; intros; auto; congruence.
Qed.
Lemma length_equal_map_rev : forall T U (F : T -> U) ls ls',
  map F ls' = rev ls ->
  length ls = length ls'.
Proof.
  clear. intros. rewrite <- rev_length. rewrite <- H. rewrite map_length. auto.
Qed.
Hint Resolve length_equal_map_rev : list_length.
Lemma eq_proves_gt : forall a b,
  a = b -> a <= b.
Proof.
  clear. intros; omega.
Qed.
Lemma map_length_hint : forall T U (F : T -> U) a b,
  map F a = b -> length b = length a.
Proof.
  clear. intros. subst. rewrite map_length. auto.
Qed.
Hint Resolve eq_proves_gt map_length_hint skipn_length_gt : list_length.

Hint Resolve skipn_length_all : list_length.
Hint Rewrite skipn_length_all using (eauto with list_length) : list_length.

Lemma nth_error_None_length : forall (T : Type) (ls : list T) (n : nat),
  nth_error ls n = None -> length ls <= n.
Proof.
  induction ls; destruct n; simpl; intros; think; try omega. inversion H.
  eapply IHls in H. omega.
Qed.

Lemma map_nth_error_full : forall T U (F : T -> U) ls n,
  nth_error (map F ls) n = match nth_error ls n with
                             | None => None
                             | Some v => Some (F v)
                           end.
Proof.
  induction ls; destruct n; simpl; intros; think; auto.
Qed.

Lemma app_len_2 : forall T (a b c d : list T),
  a ++ b = c ++ d ->
  length b = length d ->
  a = c /\ b = d.
Proof.
  clear. induction a; destruct c; simpl; intuition; subst; auto;
  simpl in *; try rewrite app_length in H0;
    try solve [ try generalize dependent (length d); intros; exfalso; omega ].
  inversion H. subst. f_equal. eapply IHa in H3; eauto. intuition.
  inversion H. eapply IHa in H3; intuition.
Qed.

Lemma not_sure : forall T U (F : T -> U) vars X,
  map F vars = X ->
  map F nil = skipn (length vars) X.
Proof.
  induction vars; intros; simpl in *; intros; auto. destruct X; auto.  eapply IHvars.
  inversion H. auto.
Qed.
Lemma map_skipn_all_map : forall T U (F : T -> U) ls,
  map F nil = skipn (length ls) (map F ls).
Proof.
  clear. induction ls; auto.
Qed.
Lemma map_skipn_all_map_is_nil : forall T U (F : T -> U) ls ls',
  map F ls' = skipn (length ls) (map F ls) ->
  ls' = nil.
Proof.
  clear; intros. rewrite <- map_skipn_all_map in H. destruct ls'; simpl in *; congruence.
Qed.
