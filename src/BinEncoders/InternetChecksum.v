Require Import List.
Require Import Bedrock.Word Coq.micromega.Psatz.

Require Import NArith NArithRing.
Open Scope N_scope.

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

Lemma wordToN_zero :
  forall sz, wordToN (wzero sz) = 0.
Proof.
  intros; unfold wzero; rewrite natToWordToN.
  - reflexivity.
  - apply Npow2_gt_zero.
Qed.

Lemma wordToN_extend sz sz' :
  forall (w: word sz), wordToN (combine w (wzero sz')) = wordToN w.
Proof.
  intros; rewrite (wordToN_combine sz sz').
  rewrite wordToN_zero; ring.
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

Ltac N_cleanup :=
  rewrite <- ?N.add_1_l, ?N.mul_add_distr_l, ?N.mul_sub_distr_l,
  ?N.mul_add_distr_l, <- ?N.sub_add_distr, ?N.add_assoc, ?N.mul_assoc,
  ?N.mul_1_l, ?N.mul_1_r; change (2*2) with 4; repeat simpl (_ (N.pos _) (N.pos _)).

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
    rewrite <- N.add_1_r, N.mul_sub_distr_l.
    symmetry; apply N.add_sub_eq_r.
    N_cleanup; ring_simplify.
    rewrite N.sub_add.
    + reflexivity.
    + change 2 with (2 * 1); apply N.mul_le_mono_l.
      apply Npow2_ge_one.
Qed.

Lemma wordToN_wnot:
  forall (n : nat) (w : word n), wordToN (wnot w) = Npow2 n - 1 - wordToN w.
Proof.
  destruct n; intros.
  - shatter_word w; reflexivity.
  - destruct (shatter_word_S w) as (b & [ w' ? ]); subst.
    revert b; induction w'.
    + destruct b; reflexivity.
    + intros; simpl in *; rewrite IHw'.
      destruct b0; simpl; N_cleanup.
      * reflexivity.
      * set (4 * Npow2 _) as m.
        set (if b then _ else _) as t.
        replace (2 + 2 * t) with (1 + 2 * t + 1) by ring.
        rewrite ?N.sub_add_distr, N.add_comm, N.sub_add; try reflexivity.
        repeat apply N.le_add_le_sub_r.
        destruct b;
          unfold t, m; clear t; clear m;
            ring_simplify;
            pose proof (wordToN_bound w') as H;
            rewrite <- N.le_succ_l, <- N.add_1_r in H;
            apply (N.mul_le_mono_nonneg_l _ _ 4) in H; auto using N.le_0_l;
              etransitivity; try apply H; ring_simplify.
        reflexivity.
        rewrite <- N.add_le_mono_l; intro; discriminate.
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

Lemma wordToN_wzero {sz} :
  wordToN (wzero sz) = 0%N.
Proof.
  unfold wzero; induction sz.
  - reflexivity.
  - simpl; rewrite IHsz; reflexivity.
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

Lemma wordToN_NToWord:
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
  intros; rewrite <- (wordToN_NToWord sz (Npos p)); auto.
Qed.

Require Import ZArith ZArithRing.
Open Scope Z_scope.

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

Compute (List.map (normalizeZ 3) (count (-40) 40)).

Definition ZToOneC {sz} (z: Z) : word sz :=
  match sz with
  | O => WO
  | S sz' => match (normalizeZ sz' z) with
            | Z0 => wones (S sz')
            | Zpos x => waddmsb (posToWord sz' x) false
            | Zneg x => wnot (waddmsb (posToWord sz' x) false)
            end
  end.

Compute (@ZToOneC 4 8).

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

Lemma normalizeZ_range :
  forall p z, (- Z.of_N (Npow2 p)) < normalizeZ p z < Z.of_N (Npow2 p).
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
  red; intros ** Heq.
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
Open Scope oneC_scope.

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

(* Fixpoint wdropmsb {sz} (w: word sz) : word (pred sz) := *)
(*   match w with *)
(*     | WO => WO: word (pred 0) *)
(*     | WS x O WO => WO *)
(*     | WS x n w' => WS x (wdropmsb w') *)
(*   end. *)

(* Lemma wtail_waddmsb {sz} : *)
(*   forall (w: word sz) b, *)
(*     wtl (waddmsb w b) = w. *)
(* Proof. *)
(*   induction w; intros. *)
(*   - reflexivity. *)
(*   - simpl. *)

(*   destruct (shatter_word_S w) as (? & [ ? ? ]); *)
(*     subst; reflexivity. *)

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

(* Lemma zext_plus_hi_bits: *)
(*   forall (sz : nat) (w1 w2 : word sz), *)
(*     split2 sz sz (zext w1 sz ^+ zext w2 sz) = *)
(*     (if (Npow2 sz <=? wordToN w1 + wordToN w2)%N *)
(*      then NToWord sz 1%N else NToWord sz 0%N). *)
(* Proof. *)
(*   unfold wplus, wordBin. *)
(* Admitted. *)

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

(* Lemma app_as_let A B : *)
(*   forall (f: A -> B) a, *)
(*     f a = let aa := a in f aa. *)
(*   intros; reflexivity. *)
(* Qed. *)

Lemma brute_force8 :
  OneC_plus_wplus 8.
Proof.
  OneC_plus_wplus_t.
  Time vm_compute.
  reflexivity.
Time Qed.