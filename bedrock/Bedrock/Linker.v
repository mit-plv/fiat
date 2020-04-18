Require Import Coq.omega.Omega.
(* Laying out labels, and generally coming up with final "machine code" programs *)

Require Import Coq.NArith.NArith.

Require Import Bedrock.Nomega Bedrock.Word Bedrock.IL Bedrock.LabelMap Bedrock.PropX Bedrock.XCAP Bedrock.Memory.

Set Implicit Arguments.


Definition labelsOf' (M : LabelMap.t (assert * block)) (acc : (W * ((label -> option W) * (W -> option block))))
  : (label -> option W) * (W -> option block) :=
  snd (LabelMap.fold (fun k (v : assert * block) p => let (_, bl) := v in let '(w, (labels, prog)) := p in
    (natToWord _ 1 ^+ w,
      ((fun k' => if LabelKey.eq_dec k' k then Some w else labels k'),
        (fun w' => if weq w' w then Some bl else prog w'))))
  M acc).

Definition labelsOf (M : LabelMap.t (assert * block)) : (label -> option W) * (W -> option block) :=
  labelsOf' M (wzero _, (fun _ => None, fun _ => None)).

Lemma lt_trans : forall n m o, (n < o)%N -> m = n -> (m < o)%N.
  congruence.
Qed.

Lemma lt_rearrange : forall n p m k,
  (n + (p + m) < k)%N
  -> (p + n < k)%N.
  intros; nomega.
Qed.

Lemma contra : forall x b n,
  (n < b)%nat
  -> (S x * b <= n)%nat
  -> False.
  simpl; intros.
  assert (b <= n)%nat.
  generalize dependent (x * b)%nat.
  intros; omega.
  omega.
Qed.

Lemma labelsOf'_inj : forall M l1 l2 w w' labels prog,
  let labels' := fst (labelsOf' M (w', (labels, prog))) in
    labels' l1 = Some w
    -> labels' l2 = Some w
    -> (forall l1' l2' w'', labels l1' = Some w'' -> labels l2' = Some w'' -> l1' = l2')
    -> (forall l w'', labels l = Some w'' -> (wordToNat w'' < wordToNat w')%nat)
    -> (wordToN w' + N_of_nat (LabelMap.cardinal M) < Npow2 32)%N
    -> l1 = l2.
  unfold labelsOf'; simpl; intros.
  rewrite LabelMap.fold_1 in *.
  rewrite LabelMap.cardinal_1 in *.
  generalize dependent prog.
  generalize dependent labels.
  generalize dependent w'.
  induction (LabelMap.elements M); simpl; intuition.
  eauto.
  simpl in *.
  eapply IHl; clear IHl; try (apply H || apply H0); simpl; intuition.
  generalize H3; clear.
  unfold wplus, wordBin.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  intro; eapply lt_trans; eauto.
  replace (Npos (P_of_succ_nat (length l))) with (1 + N_of_nat (length l))%N in *.
  replace (wordToN (NToWord 32 (1 + wordToN w'))) with (1 + wordToN w')%N.
  ring.
  rewrite NToWord_nat.
  assert (1 + wordToN w' < 4294967296)%N.

  eapply lt_rearrange; eauto.

  rewrite nat_of_Nplus.
  change (nat_of_N 1) with 1.
  repeat rewrite wordToN_nat.
  rewrite nat_of_N_of_nat.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w')); intuition.
  rewrite H1.
  rewrite N_of_minus.
  rewrite N_of_plus.
  rewrite N_of_mult.
  change (N_of_nat 1) with 1%N.
  destruct x.
  change (N_of_nat 0) with 0%N.
  rewrite Nmult_0_l.
  clear.
  nomega.
  elimtype False.
  clear H1.

  eapply contra; [ | eassumption ].
  generalize H; clear; intro.
  rewrite <- Npow2_nat.
  change 1 with (nat_of_N 1) at 1.
  rewrite <- (nat_of_N_of_nat (wordToNat w')).
  rewrite <- nat_of_Nplus.
  apply Nlt_out.
  rewrite wordToN_nat in H.
  apply H.
  clear.
  apply nat_of_N_eq.
  change (nat_of_N (Npos (P_of_succ_nat (length l)))) with (nat_of_P (P_of_succ_nat (length l))).
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ.
  rewrite nat_of_Nplus.
  simpl.
  autorewrite with N; reflexivity.

  repeat match goal with
           | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
           | [ H : LabelKey.eq _ _ |- _ ] => hnf in H; subst
         end; auto.
  elimtype False.
  injection H5; clear H5; intro; subst.
  apply H2 in H4; omega.
  elimtype False.
  injection H4; clear H4; intro; subst.
  apply H2 in H5; omega.
  eauto.

  repeat match goal with
           | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
           | [ H : LabelKey.eq _ _ |- _ ] => hnf in H; subst
         end; auto.
  injection H4; clear H4; intro; subst.
  generalize H3; clear; intros.
  apply Nlt_out in H3.
  autorewrite with N in *.
  change (nat_of_N (Npos (P_of_succ_nat (length l)))) with (nat_of_P (P_of_succ_nat (length l))) in H3.
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H3.
  rewrite wordToN_nat in H3.
  autorewrite with N in *.
  unfold wplus, wordBin.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  rewrite NToWord_nat.
  rewrite nat_of_Nplus.
  change (nat_of_N 1) with 1.
  rewrite wordToN_nat.
  autorewrite with N.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w'')); intuition.
  rewrite H0; clear H0.
  destruct x.
  omega.
  elimtype False.
  change 4294967296%N with (Npow2 32) in *.
  rewrite Npow2_nat in *.
  eapply contra; [ | eassumption ].
  generalize H3; clear; intro.
  generalize dependent (pow2 32).
  intros; omega.

  apply H2 in H4.
  generalize H3 H4; clear; intros.
  change 4294967296%N with (Npow2 32) in *.
  unfold wplus, wordBin.
  rewrite NToWord_nat.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  rewrite nat_of_Nplus.
  change (nat_of_N 1) with 1.
  rewrite wordToN_nat.
  autorewrite with N.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w')); intuition.
  rewrite H0; clear H0.
  destruct x.
  omega.
  elimtype False.
  eapply contra; [ | eassumption ].
  generalize H3; clear; intro.
  apply Nlt_out in H3.
  autorewrite with N in *.
  change (nat_of_N (Npos (P_of_succ_nat (length l)))) with (nat_of_P (P_of_succ_nat (length l))) in H3.
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H3.
  rewrite wordToN_nat in H3.
  autorewrite with N in *.
  rewrite Npow2_nat in *.
  generalize dependent (pow2 32).
  intros; omega.
Qed.

Theorem labelsOf_inj : forall M l1 l2 w, fst (labelsOf M) l1 = Some w
  -> fst (labelsOf M) l2 = Some w
  -> (N_of_nat (LabelMap.cardinal M) < Npow2 32)%N
  -> l1 = l2.
  intros; eapply labelsOf'_inj; eauto; simpl; intuition; discriminate.
Qed.

Lemma labels_keep : forall k v w ls w' labels prog,
  labels k = Some w
  -> ~SetoidList.InA (@LabelMap.eq_key _) (k, v) ls
  -> fst (snd (List.fold_left
    (fun
      (a : word 32 *
        ((LabelKey.t -> option (word 32)) *
          (word 32 -> option block)))
        (p : LabelMap.key * (assert * block)) =>
        let (_, bl0) := snd p in
          let '(w, (labels0, prog0)) := a in
            (WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
              ^+ w,
              (fun k' : LabelKey.t =>
                if LabelFacts.eq_dec k' (fst p) then Some w else labels0 k',
                  fun w'0 : word 32 =>
                    if weq w'0 w then Some bl0 else prog0 w'0))) ls
      (w', (labels, prog))))
     k = Some w.
  induction ls as [ | [ ? [ ] ] ]; simpl; intuition.
  apply IHls; auto.
  destruct (LabelFacts.eq_dec k k0).
  elimtype False; apply H0.
  hnf in e; subst.
  constructor; hnf; auto.
  auto.
Qed.

Lemma slow : forall x ln w' n,
  (w' + S ln < n)%nat
  -> (S x * n <= 1 + w')%nat
  -> False.
  simpl; intros.
  generalize dependent (x * n); intros; omega.
Qed.

Lemma prog_keep : forall w bl ls w' labels prog,
  prog w = Some bl
  -> w < w'
  -> (wordToN w' + N_of_nat (length ls) < Npow2 32)%N
  -> snd (snd (List.fold_left
    (fun
      (a : word 32 *
        ((LabelKey.t -> option (word 32)) *
            (word 32 -> option block)))
        (p : LabelMap.key * (assert * block)) =>
        let (_, bl0) := snd p in
          let '(w, (labels0, prog0)) := a in
            (WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1
              ^+ w,
              (fun k' : LabelKey.t =>
                if LabelFacts.eq_dec k' (fst p) then Some w else labels0 k',
                  fun w'0 : word 32 =>
                    if weq w'0 w then Some bl0 else prog0 w'0))) ls
      (w', (labels, prog))))
     w = Some bl.
  induction ls as [ | [ ? [ ] ] ]; simpl; intuition.
  apply IHls; auto.
  destruct (weq w w').
  subst.
  elimtype False.
  unfold wlt in H0.
  apply Nlt_not_eq in H0; tauto.
  auto.

  generalize H0 H1; clear; intros.
  change 4294967296%N with (Npow2 32) in *.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w')); intuition.
  rewrite <- Npow2_nat in *.
  generalize dependent (Npow2 32); intros.
  apply Nlt_out in H1.
  autorewrite with N in *.
  change (nat_of_N (Npos (P_of_succ_nat (length ls)))) with (nat_of_P (P_of_succ_nat (length ls))) in H1.
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H1.
  rewrite wordToN_nat in H1.
  autorewrite with N in *.
  unfold wlt in *.
  unfold wplus, wordBin.
  rewrite NToWord_nat.
  repeat rewrite wordToN_nat in *.
  autorewrite with N in *.
  match goal with
    | [ |- context[wordToNat ?N] ] =>
      match N with
        | _~1 => change (wordToNat N) with 1
      end
  end.
  rewrite H2; clear H2.
  destruct x.
  generalize H0; clear.
  intros; nomega.
  elimtype False.
  clear H0.

  eapply slow; eassumption.

  generalize H1; clear; intros.
  change 4294967296%N with (Npow2 32) in *.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w')); intuition.
  rewrite <- Npow2_nat in *.
  generalize dependent (Npow2 32); intros.
  unfold wplus, wordBin.
  rewrite NToWord_nat.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  rewrite nat_of_Nplus.
  change (nat_of_N 1) with 1.
  rewrite wordToN_nat.
  autorewrite with N.
  repeat rewrite wordToN_nat in *.
  autorewrite with N in *.
  rewrite H0; clear H0.
  rewrite N_of_minus.
  rewrite N_of_plus.
  rewrite N_of_mult.
  change (N_of_nat 1) with 1%N.
  apply Nlt_out in H1.
  autorewrite with N in *.
  change (nat_of_N (Npos (P_of_succ_nat (length ls)))) with (nat_of_P (P_of_succ_nat (length ls))) in H1.
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H1.
  destruct x.
  change (N_of_nat 0) with 0%N.
  apply Nlt_in.
  autorewrite with N.
  change (nat_of_N 1) with 1.
  change (nat_of_N (0 * N_of_nat (pow2 32))) with 0.
  omega.
  elimtype False.
  eapply contra; [ | eassumption ].
  omega.
Qed.

Lemma labelsOf'_agree : forall M l pre bl w' labels prog, LabelMap.MapsTo l (pre, bl) M
  -> (forall l w'', labels l = Some w'' -> (wordToNat w'' < wordToNat w')%nat)
  -> (wordToN w' + N_of_nat (LabelMap.cardinal M) < Npow2 32)%N
  -> exists w, fst (labelsOf' M (w', (labels, prog))) l = Some w
    /\ snd (labelsOf' M (w', (labels, prog))) w = Some bl.
  unfold labelsOf'; simpl; intros.
  rewrite LabelMap.fold_1 in *.
  rewrite LabelMap.cardinal_1 in *.
  apply LabelMap.elements_1 in H.
  generalize dependent prog.
  generalize dependent labels.
  generalize dependent w'.
  generalize (LabelMap.elements_3w M).
  induction 1; simpl; intuition.
  inversion H.

  inversion H; clear H; intros; subst.
  hnf in H5; simpl in H5; intuition; subst.
  destruct x; simpl in *; subst.

  exists w'; intuition.

  eapply labels_keep; eauto.
  destruct (LabelFacts.eq_dec k k); auto.
  elimtype False; apply n; reflexivity.

  apply prog_keep.
  destruct (weq w' w'); tauto.

  generalize H2; clear; intros.
  change 4294967296%N with (Npow2 32) in *.
  apply Nlt_out in H2.
  autorewrite with N in H2.
  change (nat_of_N (Npos (P_of_succ_nat (length l0)))) with (nat_of_P (P_of_succ_nat (length l0))) in H2.
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H2.
  unfold wlt, wplus, wordBin.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  rewrite NToWord_nat in *.
  rewrite wordToN_nat in *.
  autorewrite with N in *.
  rewrite wordToN_nat in *.
  change (nat_of_N 1) with 1.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w')); intuition.
  rewrite H0.
  rewrite <- Npow2_nat in *.
  generalize dependent (Npow2 32); intros.
  apply Nlt_in.
  autorewrite with N.
  destruct x.
  omega.
  elimtype False.
  eapply slow; eauto.

  generalize H2; clear.
  change 4294967296%N with (Npow2 32).
  destruct (wordToNat_natToWord 32 (1 + wordToNat w')); intuition.
  rewrite <- Npow2_nat in *.
  generalize dependent (Npow2 32); intros.
  eapply lt_trans; eauto.
  apply nat_of_N_eq.
  autorewrite with N.
  change (nat_of_N (Npos (P_of_succ_nat (length l0)))) with (nat_of_P (P_of_succ_nat (length l0))).
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ.
  rewrite wordToN_nat.
  autorewrite with N.
  unfold wplus, wordBin.
  rewrite NToWord_nat.
  autorewrite with N.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  change (nat_of_N 1) with 1.
  rewrite wordToN_nat; autorewrite with N.
  rewrite H0; clear H0.
  apply Nlt_out in H2.
  autorewrite with N in *.
  change (nat_of_N (Npos (P_of_succ_nat (length l0)))) with (nat_of_P (P_of_succ_nat (length l0))) in H2.
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H2.
  destruct x.
  omega.
  elimtype False.
  eapply slow; eauto.
  rewrite wordToN_nat; autorewrite with N; eauto.


  destruct x as [ ? [ ] ]; simpl in *.
  apply IHNoDupA; auto.
  generalize H2; clear.
  change 4294967296%N with (Npow2 32) in *.
  unfold wplus, wordBin.
  rewrite NToWord_nat.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  rewrite nat_of_Nplus.
  change (nat_of_N 1) with 1.
  repeat rewrite wordToN_nat.
  autorewrite with N.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w')); intuition.
  rewrite H0; clear H0.
  repeat rewrite <- Npow2_nat in *.
  generalize dependent (Npow2 32); intros.
  rewrite N_of_minus.
  rewrite N_of_plus.
  rewrite N_of_mult.
  change (N_of_nat 1) with 1%N.
  apply Nlt_out in H2.
  autorewrite with N in H2.
  change (nat_of_N (Npos (P_of_succ_nat (length l0)))) with (nat_of_P (P_of_succ_nat (length l0))) in H2.
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H2.
  autorewrite with N.
  destruct x.
  apply Nlt_in.
  autorewrite with N.
  change (nat_of_N 1) with 1.
  change (nat_of_N (N_of_nat 0 * n))%N with 0.
  omega.
  elimtype False.
  eapply contra; [ | eassumption ].
  omega.

  intros.
  repeat match goal with
           | [ _ : context[if ?E then _ else _] |- _ ] => destruct E
           | [ H : LabelKey.eq _ _ |- _ ] => hnf in H; subst
         end; auto.
  injection H; clear H; intro; subst.
  generalize H2; clear; intros.
  apply Nlt_out in H2.
  autorewrite with N in *.
  change (nat_of_N (Npos (P_of_succ_nat (length l0)))) with (nat_of_P (P_of_succ_nat (length l0))) in H2.
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H2.
  rewrite wordToN_nat in H2.
  autorewrite with N in *.
  unfold wplus, wordBin.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  rewrite NToWord_nat.
  rewrite nat_of_Nplus.
  change (nat_of_N 1) with 1.
  rewrite wordToN_nat.
  autorewrite with N.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w'')); intuition.
  rewrite H0; clear H0.
  destruct x.
  omega.
  elimtype False.
  change 4294967296%N with (Npow2 32) in *.
  rewrite Npow2_nat in *.
  eapply contra; [ | eassumption ].
  omega.

  apply H3 in H.
  generalize H H2; clear; intros.
  change 4294967296%N with (Npow2 32) in *.
  unfold wplus, wordBin.
  rewrite NToWord_nat.
  match goal with
    | [ |- context[wordToN ?N] ] =>
      match N with
        | _~1 => change (wordToN N) with 1%N
      end
  end.
  rewrite nat_of_Nplus.
  change (nat_of_N 1) with 1.
  rewrite wordToN_nat.
  autorewrite with N.
  destruct (wordToNat_natToWord 32 (1 + wordToNat w')); intuition.
  rewrite H1; clear H1.
  destruct x.
  omega.
  elimtype False.
  eapply contra; [ | eassumption ].
  generalize H2; clear; intro.
  apply Nlt_out in H2.
  autorewrite with N in *.
  change (nat_of_N (Npos (P_of_succ_nat (length l0)))) with (nat_of_P (P_of_succ_nat (length l0))) in H2.
  rewrite Pnat.nat_of_P_o_P_of_succ_nat_eq_succ in H2.
  rewrite wordToN_nat in H2.
  autorewrite with N in *.
  rewrite Npow2_nat in *.
  generalize dependent (pow2 32).
  intros; omega.
Qed.

Theorem labelsOf_agree : forall M l pre bl, LabelMap.MapsTo l (pre, bl) M
  -> (N_of_nat (LabelMap.cardinal M) < Npow2 32)%N
  -> exists w, fst (labelsOf M) l = Some w
    /\ snd (labelsOf M) w = Some bl.
  intros; eapply labelsOf'_agree; intuition eauto; discriminate.
Qed.


(** * Some default word-size memory accessors *)


Theorem wlt_not_refl : forall n (w : word n), w < w -> False.
  unfold wlt; intros; nomega.
Qed.

Hint Immediate wlt_not_refl.

Lemma use_separated : forall (k : W) q,
  (forall n m, (n < 4)%nat -> (m < 4)%nat -> k ^+ $ q ^+ $ n = k ^+ $ m -> False)
  -> (q < 4)%nat
  -> False.
  intros.
  apply H with 0 q; auto.
  word_eq.
Qed.

Lemma use_separated' : forall (k : W) q,
  (forall n m, (n < 4)%nat -> (m < 4)%nat -> k ^+ $ n = k ^+ $ q ^+ $ m -> False)
  -> (q < 4)%nat
  -> False.
  intros.
  apply H with q 0; auto.
  word_eq.
Qed.

Local Hint Extern 1 False => eapply use_separated; [ eassumption | omega ].
Local Hint Extern 1 False => eapply use_separated'; [ eassumption | omega ].
Local Hint Extern 1 False => match goal with
                               | [ H : forall n m : nat, _ |- _ ] => eapply H; [ | | eassumption ]; omega
                             end.

(** * Finally, we can create settings for testing. *)

Section LittleEndianSettings.
  Variable memHigh : W.
  Variable m : module.

(** NOTE: this is little endian *)
  Definition explode_le (v : W) : B * B * B * B :=
    let dw1 := split1 16 16 v in
    let dw2 := split2 16 16 v in
    let b1 := split1 8 8 dw1 in
    let b2 := split2 8 8 dw1 in
    let b3 := split1 8 8 dw2 in
    let b4 := split2 8 8 dw2 in
    (b1,b2,b3,b4).

  Definition implode_le (bs : B * B * B * B) : W :=
    let '(b1,b2,b3,b4) := bs in
    combine (combine b1 b2) (combine b3 b4).

  Theorem implode_explode_le : forall w,
    implode_le (explode_le w) = w.
  Proof.
    unfold implode_le, explode_le.
    intros. repeat rewrite combine_split. reflexivity.
  Qed.

  Theorem explode_implode_le : forall b,
    explode_le (implode_le b) = b.
  Proof.
    unfold implode_le, explode_le.
    intros. destruct b. destruct p. destruct p.
    repeat (rewrite split1_combine || rewrite split2_combine).
    reflexivity.
  Qed.

  Definition leSettings := {|
    implode := implode_le ;
    explode := explode_le ;
    implode_explode := implode_explode_le ;
    explode_implode := explode_implode_le ;
    Labels := fst (labelsOf (Blocks m))
  |}.

  Hypothesis closed : LabelMap.cardinal (Imports m) = 0.
  Hypothesis notTooBig : (N_of_nat (LabelMap.cardinal (Blocks m)) < Npow2 32)%N.
  Hypothesis ok : moduleOk m.

  Theorem safety : forall mn g pre, LabelMap.find (mn, Global g) (Exports m) = Some pre
    -> forall w, Labels leSettings (mn, Global g) = Some w
      -> forall st, interp (specs m leSettings) (pre (leSettings, st))
        -> safe leSettings (snd (labelsOf (Blocks m))) (w, st).
    intros; eapply safety; intuition eauto.
    apply labelsOf_inj with (Blocks m) w0; auto.
    simpl; eapply labelsOf_agree; eauto.
    apply LabelMap.find_2; eauto.
  Qed.
End LittleEndianSettings.
