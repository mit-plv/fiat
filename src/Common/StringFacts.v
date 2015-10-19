Require Import Coq.omega.Omega.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Global Set Implicit Arguments.

Lemma substring_correct3 {s : string} m (H : length s <= m)
  : substring 0 m s = s.
Proof.
  revert m H.
  induction s; simpl.
  { intros; destruct m; trivial. }
  { intros; destruct m.
    { apply Lt.lt_n_0 in H.
      destruct H. }
    { rewrite IHs; trivial.
      apply Le.le_S_n; trivial. } }
Qed.

Lemma substring_correct3' {s : string}
  : substring 0 (length s) s = s.
Proof.
  apply substring_correct3; reflexivity.
Qed.

Lemma substring_correct0 {s : string} {n}
  : substring n 0 s = ""%string.
Proof.
  revert n; induction s; intro n; destruct n; simpl; trivial.
Qed.

Lemma substring_correct0' {s : string} {n m} (H : length s <= n)
  : substring n m s = ""%string.
Proof.
  revert n m H; induction s; simpl; intros n m H.
  { destruct n, m; trivial. }
  { destruct n, m; trivial.
    { apply le_Sn_0 in H; destruct H. }
    { rewrite IHs; eauto with arith. }
    { rewrite IHs; eauto with arith. } }
Qed.

Lemma substring_correct4 {s : string} {n m m'}
      (H : length s <= n + m) (H' : length s <= n + m')
  : substring n m s = substring n m' s.
Proof.
  revert n m m' H H'.
  induction s; simpl in *.
  { intros; destruct m, m', n; trivial. }
  { intros; destruct m, m', n; trivial; simpl in *;
    try (apply Lt.lt_n_0 in H; destruct H);
    try (apply Lt.lt_n_0 in H'; destruct H');
    try apply Le.le_S_n in H;
    try apply Le.le_S_n in H';
    try solve [ try rewrite plus_comm in H;
                try rewrite plus_comm in H';
                simpl in *;
                rewrite !substring_correct0' by auto with arith; trivial ].
    { apply f_equal.
      apply IHs; trivial. }
    { apply IHs; trivial. } }
Qed.

Lemma string_concat_empty_r {s} : (s ++ "" = s)%string.
Proof.
  induction s; simpl; f_equal; trivial.
Qed.

Lemma string_concat_empty_l {s} : ("" ++ s = s)%string.
Proof.
  reflexivity.
Qed.

Lemma substring_concat {x y z} {s : string}
  : (substring x y s ++ substring (x + y) z s)%string = substring x (y + z) s.
Proof.
  revert x y z.
  induction s; simpl; intros.
  { destruct (y + z), x, y, z; reflexivity. }
  { destruct x, y, z; try reflexivity; simpl;
    rewrite ?plus_0_r, ?substring_correct0, ?string_concat_empty_r;
    try reflexivity.
    { apply f_equal.
      apply IHs. }
    { rewrite IHs; simpl; reflexivity. } }
Qed.

Lemma substring_concat' {y z} {s : string}
  : (substring 0 y s ++ substring y z s)%string = substring 0 (y + z) s.
Proof.
  rewrite <- substring_concat; reflexivity.
Qed.

Lemma substring_concat0 {s1 s2 : string}
  : substring 0 (length s1) (s1 ++ s2) = s1.
Proof.
  induction s1; simpl.
  { rewrite substring_correct0; trivial. }
  { rewrite IHs1; trivial. }
Qed.

Lemma concat_length {s1 s2 : string}
  : length (s1 ++ s2) = length s1 + length s2.
Proof.
  induction s1.
  { reflexivity. }
  { simpl.
    rewrite IHs1; reflexivity. }
Qed.

Lemma substring_concat_length {s1 s2 : string}
  : substring (length s1) (length s2) (s1 ++ s2) = s2.
Proof.
  induction s1; simpl.
  { rewrite substring_correct3'; trivial. }
  { erewrite substring_correct4.
    { exact IHs1. }
    { rewrite concat_length; reflexivity. }
    { rewrite concat_length; reflexivity. } }
Qed.

Lemma substring_length {s n m}
  : length (substring n m s) = (min (length s) (m + n)) - n.
Proof.
  revert n m; induction s; intros.
  { destruct n, m; reflexivity. }
  { simpl.
    destruct n, m; simpl; trivial; rewrite IHs; simpl;
    try omega; [].
    rewrite (plus_comm m (S n)); simpl.
    rewrite (plus_comm n m); simpl.
    reflexivity. }
Qed.

Lemma substring_substring {s n m n' m'}
  : substring n m (substring n' m' s) = substring (n + n') (min m (m' - n)) s.
Proof.
  revert n m n' m'.
  induction s; intros.
  { destruct n, m, n', m'; reflexivity. }
  { destruct n', m';
    rewrite <- ?plus_n_O, <- ?minus_n_O, ?Min.min_0_r, ?Min.min_0_l;
    destruct n, m;
    trivial; simpl;
    rewrite ?IHs, ?substring_correct0, <- ?plus_n_O, <- ?minus_n_O;
    simpl;
    try reflexivity.
    rewrite (plus_comm _ (S _)); simpl.
    rewrite (plus_comm n n').
    reflexivity. }
Qed.

Lemma substring1_get {n str}
  : substring n 1 str
    = option_rect (fun _ => String.string) (fun a => String.String a ""%string) ""%string (get n str).
Proof.
  revert n; induction str; intro n.
  { destruct n; reflexivity. }
  { destruct n; simpl.
    { destruct str; reflexivity. }
    { rewrite <- IHstr; reflexivity. } }
Qed.

Lemma substring_min {x x' y y' z str} (H : substring x y str = substring x' y' str)
  : substring x (min y z) str = substring x' (min y' z) str.
Proof.
  pose proof (fun y x => @substring_substring str 0 z x y) as H'; simpl in *.
  setoid_rewrite Nat.sub_0_r in H'.
  setoid_rewrite Min.min_comm in H'.
  rewrite <- !H', H; reflexivity.
Qed.
