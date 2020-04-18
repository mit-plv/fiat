Require Import List.
Require Import Bedrock.Word Coq.micromega.Psatz.

Require Import NArith NArithRing.
Local Open Scope N_scope.

Lemma natToWordToN : (* FIXME this is a simplified copy of the same lemma in Bedrock.IL *)
  forall n m,
    (N_of_nat m < Npow2 n)%N ->
    wordToN (natToWord n m) = N_of_nat m.
  intros; rewrite wordToN_nat, wordToNat_natToWord_idempotent by assumption.
  reflexivity.
Qed.

Lemma wordToN_combine:
  forall sz1 sz2 (w1: word sz1) (w2: word sz2), wordToN (combine w1 w2) = wordToN w1 + Npow2 sz1 * wordToN w2.
Proof.
  induction w1; simpl; intros.
  - destruct (wordToN w2); reflexivity.
  - rewrite IHw1; destruct b, (wordToN w1), (Npow2 n), (wordToN w2); reflexivity.
Qed.

Lemma Npow2_gt_zero:
  forall sz : nat, 0 < Npow2 sz.
Proof.
  induction sz; try reflexivity.
  apply N.mul_pos_pos; auto || reflexivity.
Qed.

Lemma Npow2_ge_one:
  forall sz : nat, 1 <= Npow2 sz.
Proof.
  intros.
  apply N.lt_succ_r.
  rewrite <- N.add_1_l.
  apply N.lt_sub_lt_add_l.
  apply Npow2_gt_zero.
Qed.

Lemma wordToN_wzero {sz} :
  wordToN (wzero sz) = 0%N.
Proof.
  intros; unfold wzero; rewrite natToWordToN.
  - reflexivity.
  - apply Npow2_gt_zero.
Qed.

Lemma wordToN_extend sz sz' :
  forall (w: word sz), wordToN (combine w (wzero sz')) = wordToN w.
Proof.
  intros; rewrite (wordToN_combine sz sz').
  rewrite wordToN_wzero; ring.
Qed.

Lemma N_le_succ_plus_1 : forall n m : N, (n + 1 <= m)%N <-> (n < m)%N.
Proof.
  intros; rewrite N.add_1_r.
  apply N.le_succ_l.
Qed.

Lemma N_lt_double_lt:
  forall p p' : N,
    (p < p')%N ->
    (2 * p < 2 * p')%N.
Proof.
  intros; apply N.mul_lt_mono_pos_l; eauto; reflexivity.
Qed.

Lemma N_le_double:
  forall p : N,
    (p <= 2 * p)%N.
Proof.
  intros; replace (2 * p)%N with (p + p)%N by ring.
  replace p with (0 + p)%N at 1 by ring.
  rewrite <- N.add_le_mono_r.
  apply N.le_0_l.
Qed.

Lemma N_lt_double:
  forall p : N,
    (0 < p)%N ->
    (p < 2 * p)%N.
Proof.
  intros; replace (2 * p)%N with (p + p)%N by ring.
  replace p with (0 + p)%N at 1 by ring.
  rewrite <- N.add_lt_mono_r.
  assumption.
Qed.

Lemma wordToN_bound {size} (w: Word.word size):
  (wordToN w < Npow2 size)%N.
Proof.
  Opaque N.mul.
  induction size.
  - rewrite (shatter_word_0 w); reflexivity.
  - destruct (shatter_word_S w) as (b & [ w' ? ]); subst.
    destruct b; simpl.
    rewrite <- N.add_1_r.
    auto using N.double_above.
    auto using N_lt_double_lt, N.double_above.
Qed.

Lemma NToWord_wordToN {sz} :
  forall (w: word sz), NToWord _ (wordToN w) = w.
Proof.
  intros; rewrite NToWord_nat, wordToN_nat, Nat2N.id, natToWord_wordToNat;
    reflexivity.
Qed.

Lemma wordToN_wones :
  forall sz, wordToN (wones sz) = Npow2 sz - 1.
Proof.
  induction sz.
  - reflexivity.
  - simpl; rewrite IHsz.
    pose proof (Npow2_ge_one sz); lia.
Qed.

Lemma wordToN_wnot:
  forall (n : nat) (w : word n), wordToN (wnot w) = Npow2 n - 1 - wordToN w.
Proof.
  destruct n; intros.
  - shatter_word w; reflexivity.
  - destruct (shatter_word_S w) as (b & [ w' ? ]); subst.
    revert b; induction w'.
    + destruct b; reflexivity.
    + intros; simpl in *;
        rewrite IHw';
        destruct b0; simpl; [ lia | ];
          destruct b; pose proof (wordToN_bound w'); lia.
Qed.

Lemma wplus_wnot_1:
  forall (n : nat) (w : word n), wordToN w + (Npow2 n - 1 - wordToN w) = Npow2 n - 1.
Proof.
  intros; pose proof (wordToN_bound (size := n) w); lia.
Qed.

Lemma wplus_wnot {sz}:
  forall w, wplus w (wnot w) = wones sz.
Proof.
  unfold wplus, wordBin; intros.
  rewrite wordToN_wnot, wplus_wnot_1, <- wordToN_wones, NToWord_wordToN;
    reflexivity.
Qed.

Definition W16 := Word.word 16.
Definition lo8 (w: W16) : word 8 := @split1 8 8 w.
Definition hi8 (w: W16) : word 8 := @split2 8 8 w.

Lemma wnot_involutive {sz} :
  forall (w: word sz),
    wnot (wnot w) = w.
Proof.
  induction w.
  - reflexivity.
  - simpl.
    rewrite IHw, Bool.negb_involutive; reflexivity.
Qed.

Lemma wnot_inj {sz} :
  forall w1 w2: word sz,
    wnot w1 = wnot w2 ->
    w1 = w2.
Proof.
  intros w1 w2 H.
  apply (f_equal (@wnot _)) in H.
  rewrite !wnot_involutive in H; assumption.
Qed.

Lemma wmsb_wzero {sz} :
  wmsb (wzero (S sz)) true = false.
Proof.
  induction sz; eauto.
Qed.

Lemma wmsb_wones {sz} :
  wmsb (wones sz) true = true.
Proof.
  induction sz; eauto.
Qed.

Fixpoint waddmsb {sz} (w: word sz) msb : word (S sz) :=
  match w with
  | WO => WS msb WO
  | WS b sz w' => WS b (waddmsb w' msb)
  end.

Lemma wmsb_waddmsb:
  forall (sz : nat) (w : word sz) (b b' : bool), wmsb (waddmsb w b) b' = b.
Proof.
  induction w; simpl; intros; try rewrite IHw; reflexivity.
Qed.

Lemma wnot_waddmsb {sz} :
  forall b (w: word sz), (wnot (waddmsb w b)) = waddmsb (wnot w) (negb b).
Proof.
  induction w; simpl; congruence.
Qed.

Lemma wordToN_waddmsb:
  forall b (sz : nat) (w : word sz), wordToN (waddmsb w b) = wordToN w + (if b then Npow2 sz else 0).
Proof.
  induction w;
    repeat match goal with
           | _ => ring
           | _ => reflexivity
           | _ => progress simpl
           | _ => rewrite <- !N.add_1_r
           | [ H: bool |- _ ] => destruct H
           | [ H: _ |- _ ] => rewrite H
           end.
Qed.

Lemma wnot_wones_wzero :
  forall sz, wnot (wones sz) = wzero sz.
Proof.
  induction sz; simpl; try rewrite IHsz; reflexivity.
Qed.

Lemma wnot_wzero_wones :
  forall sz, wnot (wzero sz) = wones sz.
Proof.
  intros; rewrite <- wnot_wones_wzero.
  apply wnot_involutive.
Qed.

Lemma wmsb_wnot':
  forall (n : nat) (w : word n) (b : bool), wmsb (wnot w) (negb b) = negb (wmsb w b).
Proof.
  induction w; simpl; intros.
  * reflexivity.
  * rewrite IHw; reflexivity.
Qed.

Lemma wmsb_wnot:
  forall (n : nat) (w : word (S n)), wmsb (wnot w) true = negb (wmsb w true).
Proof.
  intros; destruct (shatter_word_S w) as (b & [ w' ? ]); subst.
  simpl; apply wmsb_wnot'.
Qed.

Lemma wordToN_NToWord_idempotent:
  forall (sz : nat) (p : N),
    p < Npow2 sz ->
    wordToN (NToWord sz p) = p.
Proof.
  intros; rewrite NToWord_nat.
  rewrite natToWordToN; rewrite N2Nat.id; auto.
Qed.

Lemma wordToN_posToWord :
  forall (sz : nat) (p : positive),
    Npos p < Npow2 sz ->
    wordToN (posToWord sz p) = Npos p.
Proof.
  intros; rewrite <- (wordToN_NToWord_idempotent sz (Npos p)); auto.
Qed.

Require Import ZArith ZArithRing.
Local Open Scope Z_scope.

Fixpoint count from n :=
  match n with
  | O => nil
  | S x => from :: (count (from + 1) x)
  end.

Infix "+^+" := combine (at level 50).

Definition OneCToZ {sz} (w : word sz) : Z :=
  if wmsb w true then
    (* Negative *)
    match wordToN (wnot w) with
      | N0 => 0%Z
      | Npos x => Zneg x
    end
  else
    (* Positive *)
    match wordToN w with
      | N0 => 0%Z
      | Npos x => Zpos x
    end.

Require Import Program.

Definition normalizeZ p z :=
  let offset := Z.of_N (Npow2 p - 1) in
  let modulus := Z.of_N (Npow2 (S p) - 1) in
  (Z.modulo (z + offset) modulus) - offset.

(*Compute (List.map (normalizeZ 3) (count (-40) 40)). *)

Definition ZToOneC {sz} (z: Z) : word sz :=
  match sz with
  | O => WO
  | S sz' => match (normalizeZ sz' z) with
            | Z0 => wones (S sz')
            | Zpos x => waddmsb (posToWord sz' x) false
            | Zneg x => wnot (waddmsb (posToWord sz' x) false)
            end
  end.

(* Compute (@ZToOneC 4 8). *)

Lemma gt_minus_one_ge_zero :
  forall z, -1 < z <-> 0 <= z.
Proof.
  intros; omega.
Qed.

Hint Rewrite Z.lt_sub_lt_add_l : normalizeZ.
Hint Rewrite Z.lt_sub_lt_add_r : normalizeZ.
Hint Rewrite <- Z.lt_add_lt_sub_l : normalizeZ.
Hint Rewrite <- Z.lt_add_lt_sub_r : normalizeZ.
Hint Rewrite @gt_minus_one_ge_zero : normalizeZ.

Require Import Coq.micromega.Psatz.

Notation OneC_InRange p z := ((- Z.of_N (Npow2 p)) < z < Z.of_N (Npow2 p)).

Lemma normalizeZ_range :
  forall p z, OneC_InRange p (normalizeZ p z).
Proof.
  split;
    repeat match goal with
           | _ => progress intros
           | _ => progress unfold normalizeZ
           | _ => progress ring_simplify
           | _ => progress autorewrite with normalizeZ
           | _ => progress rewrite ?N2Z.inj_mul, ?N2Z.inj_sub by eauto using Npow2_ge_one
           | _ => simpl (Z.of_N _)
           end.
  - apply Z_mod_lt.
    pose proof (Npow2_ge_one p); lia.
  - rewrite Z.lt_add_lt_sub_r.
    apply Z_mod_lt.
    pose proof (Npow2_ge_one p); lia.
Qed.

Lemma normalizeZ_rangeN :
  forall p z,
    match normalizeZ p z with
    | Z0 => True
    | Zpos x => (Npos x < Npow2 p)%N
    | Zneg x => (Npos x < Npow2 p)%N
    end.
Proof.
  intros; destruct (normalizeZ_range p z).
  destruct (normalizeZ _ _); lia.
Qed.

Lemma weqb_correct {sz} :
  forall w1 w2: word sz,
    Word.weqb w1 w2 = false -> w1 <> w2.
Proof.
  red; intros ??? Heq.
  rewrite <- weqb_true_iff in Heq.
  congruence.
Qed.

Definition weqdec {sz} :
  forall w1 w2: word sz,
    { w1 = w2 } + { w1 <> w2 }.
Proof.
  intros; destruct (Word.weqb w1 w2) eqn:?.
  apply weqb_sound in Heqb; auto.
  apply weqb_correct in Heqb; auto.
Defined.

Definition OneC_plus {sz} (w1 w2: word sz) :=
  if weqdec w1 (wzero sz) then
    w2
  else if weqdec w2 (wzero sz) then
         w1
       else
         @ZToOneC sz (OneCToZ w1 + OneCToZ w2).

Infix "^1+" := (OneC_plus) (at level 50, left associativity) : oneC_scope.
Local Open Scope oneC_scope.

Ltac destruct_eqdec :=
  repeat match goal with
         | [  |- context[if (weqdec ?a (wzero ?sz)) then _ else _] ] =>
           lazymatch a with
           | context[if _ then _ else _] => fail
           (* | context[Z.add] => fail *)
           | _ => destruct (weqdec a (wzero sz)); subst
           end
         end.

Lemma OneC_plus_comm {sz}:
  forall (w1 w2: word sz),
    w1 ^1+ w2 = w2 ^1+ w1.
Proof.
  unfold OneC_plus; intros; rewrite Z.add_comm.
  destruct_eqdec; congruence.
Qed.

Lemma OneCToZ_wzero:
  forall sz : nat, OneCToZ (wzero sz) = 0.
Proof.
  unfold OneCToZ.
  destruct sz; [reflexivity|].
  rewrite wmsb_wzero, wordToN_wzero.
  reflexivity.
Qed.

Lemma OneCToZ_wones:
  forall sz : nat, OneCToZ (wones sz) = 0.
Proof.
  unfold OneCToZ.
  destruct sz; [reflexivity|].
  rewrite wmsb_wones, wnot_wones_wzero, wordToN_wzero.
  reflexivity.
Qed.

Lemma OneCToZ_ZToOneC {sz}:
  forall z, OneCToZ (@ZToOneC sz z) = match sz with
                                 | O => 0
                                 | S sz => normalizeZ sz z
                                 end.
Proof.
  unfold ZToOneC; destruct sz; intros.
  - reflexivity.
  - pose proof (normalizeZ_rangeN sz z);
      destruct (normalizeZ _ _) eqn:? ;
      repeat match goal with
             | _ => solve [auto]
             | _ => solve [apply OneCToZ_wones]
             | _ => progress simpl
             | _ => progress unfold OneCToZ
             | _ => progress rewrite ?wmsb_waddmsb, ?wnot_waddmsb, ?wordToN_waddmsb
             | _ => progress rewrite ?N.add_0_r, ?wordToN_posToWord, ?wnot_involutive
             end.
Qed.

Lemma normalizeZ_add_1 :
  forall z z1 z2,
    (z1 + ((z2 + (z - 1)) mod (2 * z - 1) - (z - 1)) + (z - 1)) mod (2 * z - 1) =
    (z1 + z2 + (z - 1)) mod (2 * z - 1).
Proof.
  intros.
  replace (z1 + ((z2 + (z - 1)) mod (2 * z - 1) - (z - 1)) + (z - 1))
  with (z1 + (z2 + (z - 1)) mod (2 * z - 1)) by ring.
  rewrite Zplus_mod, Zmod_mod, <- Zplus_mod.
  f_equal; ring.
Qed.

Lemma normalizeZ_add_normalizeZ_r {sz} :
  forall z1 z2,
    normalizeZ sz (z1 + (normalizeZ sz z2)) =
    normalizeZ sz (z1 + z2).
Proof.
  unfold normalizeZ; intros;
    repeat match goal with
           | _ => progress rewrite ?N2Z.inj_mul, ?N2Z.inj_sub by eauto using Npow2_ge_one
           | _ => progress (simpl (Z.of_N _); simpl (Npow2 _))
           | _ => set (Z.of_N _)
           end.
  f_equal; apply normalizeZ_add_1.
Qed.

Lemma normalizeZ_add_normalizeZ_l {sz} :
  forall z1 z2,
    normalizeZ sz ((normalizeZ sz z2) + z1) =
    normalizeZ sz (z1 + z2).
Proof.
  intros; rewrite Z.add_comm; apply normalizeZ_add_normalizeZ_r.
Qed.

Lemma wzero_S {sz} :
  wzero (S sz) = (wzero sz)~0.
Proof.
  rewrite <- natToWord_wordToNat at 1.
  rewrite <- natToWord_wordToNat.
  f_equal.
Qed.

Lemma wones_not_wzero {sz}:
  wones (S sz) <> wzero (S sz).
Proof.
  rewrite <- wnot_wones_wzero; discriminate.
Qed.

Lemma whd_waddmsb {sz}:
  forall b (w: word (S sz)),
    whd (waddmsb w b) = whd w.
Proof.
  intros;
    destruct (shatter_word_S w) as (? & [ ? ? ]);
    subst; reflexivity.
Qed.

Fixpoint wcountones {sz} (w: word sz) : nat :=
  match w with
  | WO => 0
  | WS x n w' => (if Bool.eqb x true then 1 else 0) + wcountones w'
  end%nat.

Lemma wcountones_wzero {sz} :
  wcountones (wzero sz) = 0%nat.
Proof.
  rewrite <- wzero'_def.
  induction sz; simpl; congruence.
Qed.

Lemma wcountones_waddmsb {sz} :
  forall (w: word sz) b,
    wcountones (waddmsb w b) =
    wcountones (WS b w).
Proof.
  induction w; simpl in *; intros.
  - reflexivity.
  - specialize (IHw b0).
    destruct b; destruct b0; simpl in *; rewrite IHw; reflexivity.
Qed.

Lemma wcountones_zero {sz} :
  forall w: word sz,
    wcountones w = 0%nat ->
    w = wzero _.
Proof.
  induction w.
  - reflexivity.
  - destruct b; simpl; intros; try discriminate.
    rewrite IHw by assumption.
    apply wzero_S.
Qed.

Lemma ZToOneC_nonzero {sz} :
  forall z: Z,
    ZToOneC z <> wzero (S (S sz)).
Proof.
  red; intros.
  unfold ZToOneC in *.
  pose proof (normalizeZ_rangeN (S sz) z);
    destruct (normalizeZ _ _) in *;
    match goal with
    | _ => eapply wones_not_wzero; eassumption
    | [ H: _ = wzero _ |- _ ] =>
      rewrite ?wnot_waddmsb in H;
        apply (f_equal (@wcountones _)) in H;
        rewrite wcountones_wzero, wcountones_waddmsb in H;
        simpl in H
    end.
  - apply wcountones_zero in H;
      apply (f_equal (@wordToN _)) in H;
      rewrite wordToN_posToWord, wordToN_wzero in H by assumption;
      discriminate.
  - discriminate.
Qed.

Lemma OneC_plus_assoc {sz}:
  forall (w1 w2 w3: word sz),
    w1 ^1+ (w2 ^1+ w3) = (w1 ^1+ w2) ^1+ w3.
Proof.
  unfold OneC_plus; destruct sz; intros.
  - setoid_rewrite shatter_word_0; reflexivity.
  - destruct_eqdec; try congruence;
      try match goal with
          | [ H: ZToOneC _ = (wzero _) |- _ ] =>
            destruct sz; [ | exfalso; eapply ZToOneC_nonzero; eassumption]
          end;
      change (wzero 1) with (WO~0) in *;
      repeat match goal with
             | [ w: word 1 |- _ ] => shatter_word w
             | [ b: bool |- _ ] => destruct b; try congruence
             end.

    rewrite !OneCToZ_ZToOneC; unfold ZToOneC.
    rewrite ?normalizeZ_add_normalizeZ_l, ?normalizeZ_add_normalizeZ_r.
    replace (OneCToZ w3 + (OneCToZ w1 + OneCToZ w2)) with (OneCToZ w1 + (OneCToZ w2 + OneCToZ w3)) by ring.
    reflexivity.
Qed.

Lemma OneCToZ_wnot_neg:
  forall (sz : nat) (w : word sz), OneCToZ (wnot w) = - OneCToZ w.
Proof.
  destruct w.
  + reflexivity.
  + unfold OneCToZ.
    rewrite wmsb_wnot.
    destruct (wmsb _ _);
      repeat match goal with
             | _ => reflexivity
             | _ => progress simpl
             | _ => progress rewrite ?Bool.negb_involutive, ?wnot_involutive
             | [  |- context[if ?t then ?a else ?b] ] =>
               destruct (if t then a else b)
             end.
Qed.

Lemma normalizeZ_zero:
  forall sz : nat, normalizeZ sz 0 = 0.
Proof.
  unfold normalizeZ; intros; simpl.
  rewrite Z.mod_small.
  - ring.
  - pose proof (Npow2_ge_one sz); lia.
Qed.

Lemma ZToOneC_zero:
  forall sz : nat, ZToOneC 0 = wones sz.
Proof.
  destruct sz.
  - reflexivity.
  - unfold ZToOneC.
    rewrite normalizeZ_zero; reflexivity.
Qed.

Lemma OneC_plus_wnot {sz}:
  forall w, w ^1+ (wnot w) = wones sz.
Proof.
  unfold OneC_plus; intros.
  rewrite OneCToZ_wnot_neg.
  replace (_ + _) with 0 by ring.
  destruct_eqdec; try congruence.
  - apply wnot_wzero_wones.
  - apply wnot_inj. rewrite wnot_wones_wzero; assumption.
  - apply ZToOneC_zero.
Qed.

Definition add_bytes_into_checksum (b_hi b_lo: word 8) (checksum: W16) :=
  let w16 := combine b_lo b_hi in
  checksum ^1+ w16.

Fixpoint checksum bytes : W16 :=
  match bytes with
  | nil => wzero _
  | x :: nil => add_bytes_into_checksum x (wzero _) (wzero _)
  | x :: y :: t => add_bytes_into_checksum x y (checksum t)
  end.

Fixpoint make_pairs {A} (ls: list A) zero :=
  match ls with
  | nil => nil
  | x :: nil => [(x, zero)]
  | x :: y :: t => (x, y) :: (make_pairs t zero)
  end.

Definition checksum' byte_pairs : W16 :=
  fold_right (fun p chk => add_bytes_into_checksum (fst p) (snd p) chk) (wzero _) byte_pairs.

Lemma checksum_checksum' :
  forall bytes,
    checksum bytes = checksum' (make_pairs bytes (wzero _)).
Proof.
  fix IH 1.
  destruct bytes.
  - reflexivity.
  - destruct bytes.
    + reflexivity.
    + simpl; rewrite IH; reflexivity.
Qed.

Require Import Permutation.

Lemma add_bytes_into_checksum_swap:
  forall (chk : W16) (b11 b12 b21 b22 : word 8),
    add_bytes_into_checksum b22 b21 (add_bytes_into_checksum b12 b11 chk) =
    add_bytes_into_checksum b12 b11 (add_bytes_into_checksum b22 b21 chk).
Proof.
  unfold add_bytes_into_checksum.
  intros; rewrite <- !OneC_plus_assoc.
  rewrite (OneC_plus_comm (combine b11 b12)).
  reflexivity.
Qed.

Lemma checksum'_permutation :
  forall bs1 bs2,
    Permutation bs1 bs2 ->
    checksum' bs1 = checksum' bs2.
Proof.
  induction 1.
  - reflexivity.
  - simpl; rewrite IHPermutation; reflexivity.
  - simpl. rewrite add_bytes_into_checksum_swap; reflexivity.
  - etransitivity; eauto.
Qed.

Lemma checksum'_app :
  forall bs1 bs2,
    checksum' (bs1 ++ bs2) = checksum' (bs2 ++ bs1).
Proof.
  intros; apply checksum'_permutation, Permutation_app_comm.
Qed.

Lemma make_pairs_app {A} :
  forall bs1,
    (exists x, length bs1 = 2 * x)%nat ->
    (forall bs2 z, @make_pairs A (bs1 ++ bs2) z = make_pairs bs1 z ++ make_pairs bs2 z).
Proof.
  fix IH 1.
  destruct bs1; simpl.
  - reflexivity.
  - destruct bs1; simpl; intros Hex *; destruct Hex as [x ?].
    + (* Absurd case *) omega.
    + f_equal; rewrite IH.
      * reflexivity.
      * exists (pred x); omega.
Qed.

Lemma checksum_app :
  forall bs1 bs2,
    (exists x, length bs1 = 2 * x)%nat ->
    (exists x, length bs2 = 2 * x)%nat ->
    checksum (bs1 ++ bs2) = checksum (bs2 ++ bs1).
Proof.
  intros; rewrite !checksum_checksum'.
  rewrite !make_pairs_app by assumption.
  apply checksum'_app.
Qed.

Lemma checksum_correct :
  forall bytes,
    let chk := checksum bytes in
    let neg := wnot chk in
    checksum ((hi8 neg) :: (lo8 neg) :: bytes) = wones _.
Proof.
  repeat match goal with
         | _ => progress intros
         | _ => progress unfold lo8, hi8, add_bytes_into_checksum
         | _ => progress (unfold checksum; fold checksum)
         | _ => rewrite combine_split
         | [ H := _ |- _ ] => unfold H in *; clear H
         | _ => eauto using OneC_plus_wnot
         end.
Qed.

Lemma normalizeZ_noop :
  forall p z, OneC_InRange p z -> normalizeZ p z = z.
Proof.
  intros * (? & ?).
  unfold normalizeZ; intros;
    repeat match goal with
           | _ => progress rewrite ?N2Z.inj_mul, ?N2Z.inj_sub by eauto using Npow2_ge_one
           | _ => progress (simpl (Z.of_N _); simpl (Npow2 _))
           end; set (Z.of_N _) in *.
  rewrite Z.mod_small by lia.
  ring.
Qed.

Lemma WS_match_eq_refl {sz sz'} :
  forall b (w: word sz) (w': word sz') (eql: sz = sz') (eqlS: S sz = S sz'),
    w = match eql in _ = y return (word y -> word sz) with
        | eq_refl => fun x: word sz => x
        end w' ->
    WS b w = match eqlS in _ = y return (word y -> word (S sz)) with
             | eq_refl => fun x: word (S sz) => x
             end (WS b w').
Proof.
  intros.
  destruct eql; subst.
  rewrite (UIP_nat _ _ eqlS eq_refl).
  reflexivity.
Qed.

Lemma wmsb_combine {sz} :
  forall (w : word (S sz)) b,
  exists w' : word sz,
    w = match eq_sym (NPeano.Nat.add_1_r sz) in (_ = y) return (word y -> word (S sz)) with
        | eq_refl => fun w' => w'
        end (w' +^+ WS (wmsb w b) WO).
Proof.
  induction sz; intros;
    destruct (shatter_word_S w) as (b' & [ w' ? ]); subst.
  - exists WO; pose proof (shatter_word_0 w'); subst; simpl.
    rewrite (UIP_nat _ _ (NPeano.Nat.add_1_r 0) eq_refl); reflexivity.
  - specialize (IHsz w' b'); destruct IHsz as (w'' & Heq).
    simpl.
    exists (WS b' w'').
    change (WS b' w'' +^+ WS (wmsb w' b') WO) with (WS b' (w'' +^+ WS (wmsb w' b') WO)).
    eapply WS_match_eq_refl.
    rewrite Heq at 1.
    reflexivity.
Qed.

Lemma normalizeZ_OneCToZ {sz} :
  forall w: word (S sz), normalizeZ sz (OneCToZ w) = (OneCToZ w).
Proof.
  intros.
  apply normalizeZ_noop.
  unfold OneCToZ.
  pose proof (Npow2_ge_one sz).
  destruct (wmsb _ _) eqn:Heqb; destruct (wordToN _) eqn:Heqn;
    repeat match goal with
           | _ => lia
           | [ H: wordToN (wnot ?w) = _, Heqb: wmsb ?w _ = _ |- _ ] =>
             apply (f_equal negb) in Heqb; rewrite <- (wmsb_wnot' (S sz) w true) in Heqb; simpl in Heqb
           | [ H: wmsb ?w ?b = _ |- _ ] =>
             let w' := fresh in
             let Heqw := fresh in
             destruct (wmsb_combine w b) as (w' & Heqw);
               rewrite Heqw in Heqn;
               rewrite <- (NPeano.Nat.add_1_r sz) in *;
               simpl in Heqn;
               clear Heqw;
               rewrite wordToN_combine in Heqn;
               pose proof (wordToN_bound w');
               simpl in Heqn; rewrite Heqb in Heqn; simpl in Heqn
           end.
Qed.

Lemma NToWord_zero {sz} :
  NToWord sz 0 = wzero sz.
Proof.
  rewrite NToWord_nat; simpl; reflexivity.
Qed.

Lemma wordToN_wzero' {sz} :
  forall w: word sz,
    wordToN w = 0%N ->
    w = wzero _.
Proof.
  intros.
  apply (f_equal (@NToWord sz)) in H.
  rewrite NToWord_wordToN, NToWord_zero in H.
  assumption.
Qed.

Lemma wordToN_NToWord :
  forall sz w, exists k, (wordToN (NToWord sz w) = w - k * Npow2 sz /\ k * Npow2 sz <= w)%N.
Proof.
  intros.
  destruct (wordToNat_natToWord sz (N.to_nat w)) as [ w' (Heq & side_condition) ].
  exists (N.of_nat w').
  rewrite NToWord_nat.
  rewrite wordToN_nat.
  split.
  - apply N2Nat.inj.
    rewrite Nat2N.id, N2Nat.inj_sub, N2Nat.inj_mul, Nat2N.id, Npow2_nat.
    assumption.
  - unfold N.le. rewrite N2Nat.inj_compare.
    rewrite <- nat_compare_le.
    rewrite N2Nat.inj_mul, Nat2N.id, Npow2_nat.
    assumption.
Qed.

Lemma waddmsb_NToWord {sz} :
  forall n,
    (n < Npow2 sz)%N ->
    waddmsb (NToWord sz n) false = (NToWord (S sz) n).
Proof.
  intros.
  apply wordToN_inj.
  rewrite wordToN_waddmsb; ring_simplify.
  rewrite !wordToN_NToWord_idempotent; simpl; lia.
Qed.

Lemma wordToN_bound_wmsb_false:
  forall (sz : nat) (w : word (S sz)) b,
    wmsb w b = false ->
    (wordToN w < Npow2 sz)%N.
Proof.
  induction sz.
  - intros; shatter_word w; simpl in *; subst; reflexivity.
  - intros * Heq; destruct (shatter_word_S w) as (b' & [ w' ? ]); subst; simpl in *.
    specialize (IHsz w' b' Heq).
    destruct b'; lia.
Qed.

Lemma ZToOneC_OneCToZ:
  forall (sz : nat) (w : word sz),
    w <> wzero _ ->
    ZToOneC (OneCToZ w) = w.
Proof.
  unfold ZToOneC.
  destruct sz; intros.
  - rewrite shatter_word_0; reflexivity.
  - rewrite normalizeZ_OneCToZ.
    unfold OneCToZ.
    destruct (wmsb _ _) eqn:Heqb; destruct (wordToN _) eqn:Heqn.
    + apply wordToN_wzero' in Heqn.
      apply wnot_inj.
      rewrite wnot_wones_wzero.
      auto.
    + apply wnot_inj; rewrite wnot_involutive.
      change (posToWord sz p) with (NToWord sz (N.pos p)).
      rewrite <- Heqn, waddmsb_NToWord, NToWord_wordToN.
      * reflexivity.
      * eapply wordToN_bound_wmsb_false.
        rewrite wmsb_wnot, Heqb; reflexivity.
    + apply wordToN_wzero' in Heqn.
      congruence.
    + change (posToWord sz p) with (NToWord sz (N.pos p)).
      rewrite <- Heqn.
      rewrite waddmsb_NToWord, NToWord_wordToN.
      * reflexivity.
      * eapply wordToN_bound_wmsb_false; eassumption.
Qed.

Lemma OneC_plus_wones {sz} :
  forall w,
    w <> (wzero sz) ->
    OneC_plus (wones sz) w = w.
Proof.
  unfold OneC_plus; intros.
  pose proof (@wones_not_wzero sz).
  destruct (weqdec (wones _) _), (weqdec w (wzero sz));
    try congruence.
  rewrite OneCToZ_wones; simpl.
  rewrite ZToOneC_OneCToZ; auto.
Qed.

Lemma split1_wzero:
  forall sz sz' : nat, split1 sz sz' (wzero (sz + sz')) = wzero sz.
Proof.
  intros; rewrite <- !wzero'_def.
  induction sz.
  - reflexivity.
  - simpl; f_equal; congruence.
Qed.

Lemma split2_wzero:
  forall sz sz' : nat, split2 sz sz' (wzero (sz + sz')) = wzero sz'.
Proof.
  intros; rewrite <- !wzero'_def.
  induction sz.
  - reflexivity.
  - simpl; f_equal; congruence.
Qed.

Lemma wzero_combine {sz sz'} :
  forall (w0: word sz) (w1: word sz'),
    combine w0 w1 = wzero _ ->
    w0 = wzero _ /\ w1 = wzero _.
Proof.
  intros * H.
  pose proof (f_equal (@split1 sz sz') H).
  pose proof (f_equal (@split2 sz sz') H).
  rewrite split1_combine, split1_wzero in H0.
  rewrite split2_combine, split2_wzero in H1.
  intuition.
Qed.

Lemma OneC_plus_wones_wzero {sz} :
  wones sz ^1+ wzero sz = wones sz.
Proof.
  unfold OneC_plus.
  pose proof (@wones_not_wzero sz);
    repeat match goal with
           | [  |- context[weqdec ?a ?b] ] => destruct (weqdec a b)
           end; congruence.
Qed.

Lemma combine_inj {sz sz'}:
  forall w00 w01 w10 w11,
    @combine sz w01 sz' w00 = combine w11 w10 ->
    w00 = w10 /\ w01 = w11.
Proof.
  intros * Heq; split;
    [ apply (f_equal (@split2 sz sz')) in Heq
    | apply (f_equal (@split1 sz sz')) in Heq];
    rewrite ?split1_combine, ?split2_combine in *;
    assumption.
Qed.

Lemma add_bytes_into_checksum_inj_l:
  forall (y00 y01 y10 y11 : word 8) chk,
    (y00 <> wzero _ \/ y01 <> wzero _) ->
    (y10 <> wzero _ \/ y11 <> wzero _) ->
    add_bytes_into_checksum y00 y01 chk =
    add_bytes_into_checksum y10 y11 chk ->
    y00 = y10 /\ y01 = y11.
Proof.
  unfold add_bytes_into_checksum; intros * nonz0 nonz1 H.
  apply (f_equal (fun x => (wnot chk) ^1+ x)) in H.
  rewrite !(OneC_plus_assoc (wnot chk)), !(OneC_plus_comm (wnot chk)), !OneC_plus_wnot in H.
  repeat lazymatch goal with
         | [ H: context[wones _ ^1+ ?w] |- _ ] =>
           let heq := fresh "heq" in
           let hneq := fresh "hneq" in
           destruct (weqdec w (wzero _)) as [ heq | hneq ];
             [ rewrite heq in H; setoid_rewrite OneC_plus_wones_wzero in H |
               setoid_rewrite (OneC_plus_wones w hneq) in H ]
         | [ H: _ +^+ _ = wzero _ |- _ ] => apply wzero_combine in H; destruct H; subst
         end;
    try solve [split; reflexivity];
    try solve [match goal with
               | [ H: _ \/ _ |- _ ] => destruct H; try congruence
               end].
  apply combine_inj. eassumption.
Qed.

Lemma checksum'_somewhat_injective :
  forall x y0 y1 z,
    fst y0 <> wzero 8 \/ snd y0 <> wzero 8 ->
    fst y1 <> wzero 8 \/ snd y1 <> wzero 8 ->
    checksum' (x ++ y0 :: z) = checksum' (x ++ y1 :: z) ->
    y0 = y1.
Proof.
  intros * ? ? H.
  rewrite !(checksum'_app _ (_ :: _)), <- !app_comm_cons in H.
  simpl in H; apply add_bytes_into_checksum_inj_l in H; try assumption.
  destruct y0, y1, H; simpl in *; congruence.
Qed.

Lemma wplus_three {sz} :
  forall w1 w2 w3: word sz,
    w1 ^+ w2 ^+ w3 =
    NToWord sz (wordToN w1 + wordToN w2 + wordToN w3)%N.
Proof.
  intros.
  rewrite !wordToN_nat, !NToWord_nat, !N2Nat.inj_add, !Nat2N.id.
  repeat rewrite wplus_alt; unfold wplusN, wordBinN.
  repeat match goal with
         | [ H: _ = _ |- _ ] => rewrite H; clear H
         | [ |- context[wordToNat (natToWord ?sz ?w)] ] =>
           destruct (wordToNat_natToWord sz w) as [? [? ?]]
         end.
  replace (wordToNat w1 + wordToNat w2 - x * pow2 sz + wordToNat w3)%nat
  with (wordToNat w1 + wordToNat w2 + wordToNat w3 - x * pow2 sz)%nat by omega.
  apply drop_sub; omega.
Qed.

Definition OneC_plus_wplus sz :=
  forall w1 w2: word sz,
    OneC_plus w1 w2 =
    w1 ^+ w2 ^+ split2 _ _ (zext w1 sz ^+ zext w2 sz).

Fixpoint EnumerateWords sz : list (word sz) :=
  match sz with
  | O => [WO]
  | S sz' =>
    let wds := EnumerateWords sz' in
    map (@WS true sz') wds ++ map (@WS false sz') wds
  end.

Lemma Enumerate_exhaustive {sz} :
  forall w: word sz, In w (EnumerateWords sz).
Proof.
  induction w.
  - simpl; tauto.
  - simpl; rewrite in_app_iff.
    destruct b; [left|right];
      rewrite in_map_iff;
      exists w; tauto.
Qed.

Lemma brute_force_works {sz} :
  forall (P: word sz -> bool),
    (forallb P (EnumerateWords sz) = true) ->
    (forall w, P w = true).
Proof.
  intros * H w.
  rewrite forallb_forall in H.
  pose proof (@Enumerate_exhaustive sz).
  eauto.
Qed.

Lemma brute_force_works' {sz} :
  forall (P: word sz -> Prop)
    (P': word sz -> bool),
    (forall w, P' w = true -> P w) ->
    (forallb P' (EnumerateWords sz) = true) ->
    (forall w, P w).
Proof.
  intros * correctB forallB w.
  apply correctB; revert w.
  apply brute_force_works; assumption.
Qed.

Ltac OneC_plus_wplus_t :=
  red; intros; rewrite <- weqb_true_iff;
  repeat lazymatch goal with
         | [ w: word _ |- _ ] => revert w; apply brute_force_works
         end.

(*Lemma brute_force8 :
  OneC_plus_wplus 8.
Proof.
  OneC_plus_wplus_t.
  Time vm_compute.
  reflexivity.
Time Qed. *)
