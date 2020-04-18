Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Bedrock.Expr Bedrock.Env.
Require Import Coq.Classes.EquivDec Bedrock.EqdepClass.
Require Import Bedrock.DepList.
Require Import Bedrock.Word Bedrock.Prover.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(** * The Word Prover **)

Require Import Coq.Arith.Arith Bedrock.ILEnv Bedrock.Memory.

Section WordProver.
  Variable types' : list type.
  Definition types := repr bedrock_types_r types'.
  Variable funcs' : functions types.
  Definition funcs := repr (bedrock_funcs_r _) funcs'.

  Record equality := {
    Source : expr types;
    Destination : expr types;
    Difference : W
  }.

  Record word_summary := {
    Equalities : list equality;
    LessThans : list (expr types * expr types);
    NotEquals : list (expr types * expr types)
  }.

  Require Import Coq.Arith.Div2.

  Fixpoint natToWord' (sz n : nat) : word sz :=
    match sz with
      | O => WO
      | S sz' => WS (mod2 n) (natToWord' sz' (div2 n))
    end.

  Theorem natToWord'_def : natToWord' = natToWord.
    reflexivity.
  Qed.

  Definition zero := Eval compute in wzero 32.
  Definition pow32 := Eval compute in Npow2 32.

  Require Import Coq.NArith.NArith.

  Definition wplus' := @wordBin Nplus 32.
  Definition wneg' (w : W) := NToWord 32 (pow32 - wordToN w).
  Definition wminus' (x y : W) : W := wplus' x (wneg' y).

  Theorem wplus'_def : wplus' = @wplus _.
    reflexivity.
  Qed.

  Theorem wneg'_def : wneg' = @wneg _.
    reflexivity.
  Qed.

  Theorem wminus'_def : wminus' = @wminus _.
    reflexivity.
  Qed.

  Fixpoint decompose (e : expr types) : expr types * W :=
    match e with
      | Func 0%nat [e1, Func 5%nat (Const (tvType 4%nat) k :: nil)] =>
        let (e1', d) := decompose e1 in
          (e1', wplus' d (natToWord' _ k))
      | Func 1%nat [e1, Func 5%nat (Const (tvType 4%nat) k :: nil)] =>
        let (e1', d) := decompose e1 in
          (e1', wminus' d (natToWord' _ k))
      | _ => (e, zero)
    end.

  Definition combine (f1 f2 : equality) : list equality :=
    if expr_seq_dec (Destination f1) (Source f2)
      then {| Source := Source f1;
        Destination := Destination f2;
        Difference := wplus' (Difference f1) (Difference f2) |} :: nil
      else nil.

  Fixpoint combineAll (f : equality) (fs : list equality) : list equality :=
    match fs with
      | nil => fs
      | f' :: fs => combine f f' ++ combine f' f ++ combineAll f fs
    end.

  Fixpoint alreadyCovered' (f : equality) (fs : list equality) : bool :=
    match fs with
      | nil => false
      | f' :: fs' => (expr_seq_dec (Source f) (Source f')
        && expr_seq_dec (Destination f) (Destination f'))
      || alreadyCovered' f fs'
    end.

  Definition alreadyCovered (f : equality) (fs : list equality) : bool :=
    expr_seq_dec (Source f) (Destination f) || alreadyCovered' f fs.

  Fixpoint merge (fs1 fs2 : list equality) : list equality :=
    match fs1 with
      | nil => fs2
      | f :: fs1' => merge fs1' (if alreadyCovered f fs2 then fs2 else (f :: fs2))
    end.

  Definition wordLearn1 (sum : word_summary) (e : expr types) : word_summary :=
    match e with
      | Equal (tvType 0) e1 e2 =>
        let (b1, n1) := decompose e1 in
        let (b2, n2) := decompose e2 in
        let f1 := {| Source := b1;
          Destination := b2;
          Difference := wminus' n1 n2 |} in
        let f2 := {| Source := b2;
          Destination := b1;
          Difference := wminus' n2 n1 |} in
        let equalities := merge (f1 :: combineAll f1 sum.(Equalities)) sum.(Equalities) in
        let equalities := merge (f2 :: combineAll f2 equalities) equalities in
          {| Equalities := equalities;
            LessThans := sum.(LessThans);
            NotEquals := sum.(NotEquals) |}
      | Func 4 (e1 :: e2 :: nil) =>
        {| Equalities := sum.(Equalities);
          LessThans := (e1, e2) :: sum.(LessThans);
          NotEquals := sum.(NotEquals) |}
      | Not (Equal (tvType 0) e1 e2) =>
        {| Equalities := sum.(Equalities);
          LessThans := sum.(LessThans);
          NotEquals := (e1, e2) :: sum.(NotEquals) |}
      | _ => sum
    end.

  Fixpoint wordLearn (sum : word_summary) (hyps : list (expr types)) : word_summary :=
    match hyps with
      | nil => sum
      | h :: hyps' => wordLearn (wordLearn1 sum h) hyps'
    end.

  Definition equalitysEq (f1 f2 : equality) :=
    expr_seq_dec (Source f1) (Source f2)
    && expr_seq_dec (Destination f1) (Destination f2)
    && W_seq (Difference f1) (Difference f2).

  Fixpoint equalityMatches (f : equality) (fs : list equality) : bool :=
    match fs with
      | nil => false
      | f' :: fs' => equalitysEq f f' || equalityMatches f fs'
    end.

  Fixpoint lessThanMatches (e1 e2 : expr types) (lts : list (expr types * expr types)) (eqs : list equality) : bool :=
    match lts with
      | nil => false
      | (e1', e2') :: lts' => ((expr_seq_dec e1 e1'
        || equalityMatches {| Source := e1;
          Destination := e1';
          Difference := zero |} eqs)
      && (expr_seq_dec e2 e2'
        || equalityMatches {| Source := e2;
          Destination := e2';
          Difference := zero |} eqs)) || lessThanMatches e1 e2 lts' eqs
    end.

  Definition wordProve (sum : word_summary) (e : expr types) :=
    match e with
      | Equal (tvType 0) e1 e2 =>
        let (b1, n1) := decompose e1 in
        let (b2, n2) := decompose e2 in
          if expr_seq_dec b1 b2
            then W_seq n1 n2
            else equalityMatches {| Source := b1;
              Destination := b2;
              Difference := wminus' n1 n2 |} sum.(Equalities)
      | Func 4 (e1 :: e2 :: nil) =>
        lessThanMatches e1 e2 sum.(LessThans) sum.(Equalities)
      | Not (Equal (tvType 0) e1 e2) =>
        lessThanMatches e1 e2 sum.(NotEquals) sum.(Equalities)
      | _ => false
    end.

  Definition wordSummarize := wordLearn {| Equalities := nil;
    LessThans := nil;
    NotEquals := nil|}.

  Section vars.
    Variables uvars vars : env types.

    Definition equalityValid (f : equality) := exists v1, exprD funcs uvars vars (Source f) (tvType 0%nat) = Some v1
      /\ exists v2, exprD funcs uvars vars (Destination f) (tvType 0%nat) = Some v2
        /\ v2 = v1 ^+ Difference f.

    Definition lessThanValid (p : expr types * expr types) := exists v1, exprD funcs uvars vars (fst p) (tvType 0%nat) = Some v1
      /\ exists v2, exprD funcs uvars vars (snd p) (tvType 0%nat) = Some v2
        /\ v1 < v2.

    Definition notEqualValid (p : expr types * expr types) := exists v1, exprD funcs uvars vars (fst p) (tvType 0%nat) = Some v1
      /\ exists v2, exprD funcs uvars vars (snd p) (tvType 0%nat) = Some v2
        /\ v1 <> v2.

    Definition wordValid (sum : word_summary) :=
      Forall equalityValid sum.(Equalities)
      /\ Forall lessThanValid sum.(LessThans)
      /\ Forall notEqualValid sum.(NotEquals).

    Lemma addZ_0 : forall w : W, w = w ^+ zero.
      intros.
      rewrite wplus_comm.
      symmetry.
      apply wplus_unit.
    Qed.

    Hint Immediate addZ_0.

    Lemma decompose_correct : forall e, let (b, n) := decompose e in
      forall v, exprD funcs uvars vars e (tvType 0) = Some v
        -> exists v', exprD funcs uvars vars b (tvType 0) = Some v'
          /\ v = v' ^+ n.
    Proof.
      Opaque natToWord'.
      induction e; simpl; intuition.

      t; eauto.

      eauto.

      eauto.

      destruct f.
      destruct l; try discriminate.
      destruct l; try discriminate.
      eauto.

      destruct e0; eauto.
      do 6(destruct f; eauto).
      destruct l0; eauto.
      destruct e0; eauto.
      destruct t; eauto.
      do 5(destruct n; eauto).
      destruct l0; eauto.
      destruct l; eauto.
      simpl.
      inversion H; clear H; subst.
      inversion H3; clear H3; subst.
      clear H4.
      simpl in *.
      specialize (H1 _ (refl_equal _)); destruct H1; intuition; subst.
      clear H0.
      destruct (decompose e).
      intro.
      match goal with
        | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E
      end.
      specialize (H2 _ (refl_equal _)); destruct H2; intuition; subst.
      injection H0; clear H0; intros; subst.
      repeat esplit; eauto.
      rewrite natToWord'_def.
      rewrite wplus'_def.
      repeat rewrite wplus_assoc; reflexivity.
      discriminate.

      destruct f.
      destruct l; try discriminate.
      destruct l; try discriminate.
      eauto.

      destruct e0; eauto.
      do 6 (destruct f; eauto).
      destruct l0; eauto.
      destruct e0; eauto.
      destruct t; eauto.
      do 5 (destruct n; eauto).
      destruct l0; eauto.
      destruct l; eauto.
      simpl.
      inversion H; clear H; subst.
      inversion H3; clear H3; subst.
      clear H4.
      simpl in *.
      specialize (H1 _ (refl_equal _)); destruct H1; intuition; subst.
      clear H0.
      destruct (decompose e).
      intro.
      match goal with
        | [ |- context[match ?E with Some _ => _ | None => _ end] ] => destruct E
      end.
      specialize (H2 _ (refl_equal _)); destruct H2; intuition; subst.
      injection H0; clear H0; intros; subst.
      repeat esplit; eauto.
      rewrite wminus'_def.
      repeat rewrite wplus_assoc.
      repeat rewrite wminus_def.
      repeat rewrite wplus_assoc.
      reflexivity.
      discriminate.
      eauto.

      discriminate.
      discriminate.
    Qed.

    Lemma mergeCorrect : forall fs1,
      Forall equalityValid fs1
      -> forall fs2, Forall equalityValid fs2
        -> Forall equalityValid (merge fs1 fs2).
      induction 1; simpl; intuition.
      destruct (alreadyCovered x fs2); auto.
    Qed.

    Lemma combineCorrect : forall f1 f2,
      equalityValid f1
      -> equalityValid f2
      -> Forall equalityValid (combine f1 f2).
    Proof.
      unfold combine; intros.
      generalize (expr_seq_dec_correct (Destination f1) (Source f2)).
      destruct (expr_seq_dec (Destination f1) (Source f2)); intuition.
      repeat constructor.
      unfold equalityValid in *; simpl in *; intros.

      destruct H; intuition.
      destruct H3; intuition.
      destruct H0; intuition.
      destruct H5; intuition.
      rewrite H1.
      rewrite H5.
      repeat esplit.
      subst.
      rewrite H2 in H3.
      rewrite H0 in H3.
      injection H3; clear H3; intros; subst.
      symmetry; apply wplus_assoc.
    Qed.

    Hint Resolve combineCorrect Folds.Forall_app.

    Lemma combineAllCorrect : forall f fs,
      equalityValid f
      -> Forall equalityValid fs
      -> Forall equalityValid (combineAll f fs).
    Proof.
      induction 2; simpl; intuition.
    Qed.

    Lemma equalityValid_basic : forall hyp1 hyp2 e e0 w w0,
      Provable funcs uvars vars (Equal (tvType 0) hyp1 hyp2)
      -> (forall v : tvarD (repr bedrock_types_r types') (tvType 0),
        exprD funcs uvars vars hyp1 (tvType 0) = Some v ->
        exists v' : tvarD (repr bedrock_types_r types') (tvType 0),
          exprD funcs uvars vars e (tvType 0) = Some v' /\ v = v' ^+ w)
      -> (forall v : tvarD (repr bedrock_types_r types') (tvType 0),
        exprD funcs uvars vars hyp2 (tvType 0) = Some v ->
        exists v' : tvarD (repr bedrock_types_r types') (tvType 0),
          exprD funcs uvars vars e0 (tvType 0) = Some v' /\ v = v' ^+ w0)
      -> equalityValid {| Source := e0; Destination := e; Difference := wminus' w0 w |}.
    Proof.
      intros.
      hnf in H.
      simpl in *.
      case_eq (exprD funcs uvars vars hyp1 (tvType 0)); intros.
      simpl in *.
      rewrite H2 in *.
      case_eq (exprD funcs uvars vars hyp2 (tvType 0)); intros.
      simpl in *.
      rewrite H3 in *.
      subst.
      specialize (H1 _ (refl_equal _)).
      specialize (H0 _ (refl_equal _)).
      destruct H1; destruct H0; intuition.
      subst.
      hnf.
      repeat (esplit; simpl).
      eauto.
      rewrite H.
      f_equal.
      rewrite wminus'_def.
      apply (f_equal (fun z => z ^- w)) in H5.
      repeat rewrite wminus_def in *.
      repeat rewrite wplus_assoc in *.
      rewrite H5.
      rewrite <- wplus_assoc.
      rewrite wminus_inv.
      rewrite wplus_comm.
      symmetry; apply wplus_unit.

      simpl in *.
      rewrite H3 in *.
      tauto.

      simpl in *.
      rewrite H2 in *.
      tauto.
    Qed.

    Lemma Provable_swap : forall hyp1 hyp2,
      Provable funcs uvars vars (Equal (tvType 0) hyp1 hyp2)
      -> Provable funcs uvars vars (Equal (tvType 0) hyp2 hyp1).
    Proof.
      unfold Provable; simpl; intros.
      case_eq (exprD funcs uvars vars hyp2 (tvType 0)); intros.
      simpl in *; rewrite H0 in *.
      case_eq (exprD funcs uvars vars hyp1 (tvType 0)); intros.
      simpl in *; rewrite H1 in *.
      auto.
      simpl in *; rewrite H1 in *; auto.
      simpl in *; rewrite H0 in *; auto.
      case_eq (exprD funcs uvars vars hyp1 (tvType 0)); intros; simpl in *.
      rewrite H1 in *; auto.
      rewrite H1 in *; auto.
    Qed.

    Hint Immediate Provable_swap.
    Hint Resolve equalityValid_basic mergeCorrect combineAllCorrect.

    Lemma Forall_if : forall (b : bool) ls1 ls2,
      Forall equalityValid ls1
      -> Forall equalityValid ls2
      -> Forall equalityValid (if b then ls1 else ls2).
    Proof.
      destruct b; auto.
    Qed.

    Hint Resolve Forall_if.

    Lemma wordLearn1Correct : forall sum,
      wordValid sum -> forall hyp,
        Provable funcs uvars vars hyp ->
        wordValid (wordLearn1 sum hyp).
    Proof.
      destruct hyp; simpl; intuition.

      do 5 (destruct f; auto).
      do 3 (destruct l; auto).
      destruct H; split; simpl; auto.
      split.
      constructor; auto.
      hnf; simpl.
      red in H0; simpl in H0.
      simpl in *.
      do 2 (match type of H0 with
              | match match ?E with Some _ => _ | _ => _ end _ _ with Some _ => _ | _ => _ end => destruct E
            end; try tauto).
      eauto.
      tauto.
      tauto.

      destruct t; auto.
      destruct n; auto.
      specialize (decompose_correct hyp1); intro Hy1.
      specialize (decompose_correct hyp2); intro Hy2.
      destruct (decompose hyp1); destruct (decompose hyp2).

      destruct H.
      split; simpl; auto.
      apply mergeCorrect; try apply Forall_if; eauto 15.

      destruct hyp; auto.
      destruct t; auto.
      destruct n; auto.
      destruct H.
      destruct H1.
      repeat split; simpl; auto.
      constructor; auto.
      hnf; simpl.
      red in H0; simpl in H0.
      simpl in *.
      match goal with
        | [ |- exists v1, ?E = _ /\ (exists v2, ?F = _ /\ _) ] => destruct E; try tauto;
          destruct F; try tauto
      end.
      eauto.
    Qed.

    Hint Resolve wordLearn1Correct.

    Theorem wordLearnCorrect : forall sum,
      wordValid sum
      -> forall hyps, AllProvable funcs uvars vars hyps
        -> wordValid (wordLearn sum hyps).
    Proof.
      intros; generalize dependent sum; induction hyps; simpl in *; intuition.
    Qed.

    Hint Unfold wordValid.

    Theorem wordSummarizeCorrect : forall hyps,
      AllProvable funcs uvars vars hyps
      -> wordValid (wordSummarize hyps).
    Proof.
      intros; apply wordLearnCorrect; auto.
      repeat split; constructor.
    Qed.

    Lemma equalitysEq_correct : forall f1 f2,
      equalitysEq f1 f2 = true
      -> f1 = f2.
    Proof.
      unfold equalitysEq; intros.
      apply andb_prop in H; intuition.
      apply andb_prop in H0; intuition.
      destruct f1; destruct f2; simpl in *.
      f_equal; auto.
      apply expr_seq_dec_correct; auto.
      apply expr_seq_dec_correct; auto.
      apply (Eqb_correct bedrock_type_W); auto.
    Qed.

    Lemma equalityMatches_correct : forall f eqs,
      Forall equalityValid eqs
      -> equalityMatches f eqs = true
      -> equalityValid f.
    Proof.
      induction 1; simpl; intuition.
      apply orb_prop in H1; intuition.
      apply equalitysEq_correct in H2; congruence.
    Qed.

    Lemma lessThanMatches_correct : forall e1 e2 eqs,
      Forall equalityValid eqs
      -> forall lts, Forall lessThanValid lts
        -> lessThanMatches e1 e2 lts eqs = true
        -> lessThanValid (e1, e2).
    Proof.
      induction 2; simpl; intuition.
      destruct x.
      apply orb_prop in H2; intuition.
      apply andb_prop in H3; intuition.
      apply orb_prop in H2; intuition;
        apply orb_prop in H4; intuition.
      apply expr_seq_dec_correct in H3.
      apply expr_seq_dec_correct in H2.
      congruence.

      apply equalityMatches_correct in H2; auto.
      destruct H2; intuition.
      destruct H5; intuition.
      subst.
      simpl in *.
      apply expr_seq_dec_correct in H3; subst.
      destruct H0; intuition.
      destruct H3; intuition.
      simpl in *.
      hnf.
      simpl.
      repeat esplit.
      eauto.
      eauto.
      rewrite wplus_comm in H5.
      rewrite wplus_unit in H5.
      congruence.

      apply equalityMatches_correct in H3; auto.
      destruct H3; intuition.
      destruct H5; intuition.
      subst.
      simpl in *.
      apply expr_seq_dec_correct in H2; subst.
      destruct H0; intuition.
      destruct H3; intuition.
      simpl in *.
      hnf.
      simpl.
      repeat esplit.
      eauto.
      eauto.
      rewrite wplus_comm in H5.
      rewrite wplus_unit in H5.
      congruence.

      apply equalityMatches_correct in H3; auto.
      apply equalityMatches_correct in H2; auto.
      destruct H3; intuition.
      destruct H5; intuition.
      subst.
      destruct H2; intuition.
      destruct H6; intuition.
      subst.
      simpl in *.
      rewrite wplus_comm in H5.
      rewrite wplus_unit in H5.
      rewrite wplus_comm in H6.
      rewrite wplus_unit in H6.
      destruct H0; intuition.
      destruct H7; intuition.
      simpl in *.
      hnf.
      repeat esplit.
      eauto.
      eauto.
      congruence.
    Qed.

    Lemma lessThanMatches_notEqual_correct : forall e1 e2 eqs,
      Forall equalityValid eqs
      -> forall lts, Forall notEqualValid lts
        -> lessThanMatches e1 e2 lts eqs = true
        -> notEqualValid (e1, e2).
    Proof.
      induction 2; simpl; intuition.
      destruct x.
      apply orb_prop in H2; intuition.
      apply andb_prop in H3; intuition.
      apply orb_prop in H2; intuition;
        apply orb_prop in H4; intuition.
      apply expr_seq_dec_correct in H3.
      apply expr_seq_dec_correct in H2.
      congruence.

      apply equalityMatches_correct in H2; auto.
      destruct H2; intuition.
      destruct H5; intuition.
      subst.
      simpl in *.
      apply expr_seq_dec_correct in H3; subst.
      destruct H0; intuition.
      destruct H3; intuition.
      simpl in *.
      hnf.
      simpl.
      repeat esplit.
      eauto.
      eauto.
      rewrite wplus_comm in H5.
      rewrite wplus_unit in H5.
      congruence.

      apply equalityMatches_correct in H3; auto.
      destruct H3; intuition.
      destruct H5; intuition.
      subst.
      simpl in *.
      apply expr_seq_dec_correct in H2; subst.
      destruct H0; intuition.
      destruct H3; intuition.
      simpl in *.
      hnf.
      simpl.
      repeat esplit.
      eauto.
      eauto.
      rewrite wplus_comm in H5.
      rewrite wplus_unit in H5.
      congruence.

      apply equalityMatches_correct in H3; auto.
      apply equalityMatches_correct in H2; auto.
      destruct H3; intuition.
      destruct H5; intuition.
      subst.
      destruct H2; intuition.
      destruct H6; intuition.
      subst.
      simpl in *.
      rewrite wplus_comm in H5.
      rewrite wplus_unit in H5.
      rewrite wplus_comm in H6.
      rewrite wplus_unit in H6.
      destruct H0; intuition.
      destruct H7; intuition.
      simpl in *.
      hnf.
      repeat esplit.
      eauto.
      eauto.
      congruence.
    Qed.
  End vars.

  Hint Resolve equalityMatches_correct.

  Theorem wordProverCorrect : ProverCorrect funcs wordValid wordProve.
  Proof.
    hnf; intros.
    destruct H.
    destruct goal; simpl in *; try discriminate.

    do 5 (destruct f; try discriminate).
    do 3 (destruct l; try discriminate).
    apply (@lessThanMatches_correct uvars vars) in H0; auto.
    destruct H0; intuition.
    destruct H5; intuition.
    hnf.
    simpl in *.
    rewrite H2.
    rewrite H5.
    assumption.
    tauto.

    destruct t; try discriminate.
    destruct n; try discriminate.
    specialize (decompose_correct uvars vars goal1); intro Hy1.
    specialize (decompose_correct uvars vars goal2); intro Hy2.
    destruct (decompose goal1); destruct (decompose goal2).
    simpl in *.

    hnf in H1; simpl in H1.
    destruct H1.
    case_eq (exprD funcs uvars vars goal1 (tvType 0)); simpl; intros.
    rewrite H3 in *.
    case_eq (exprD funcs uvars vars goal2 (tvType 0)); simpl; intros.
    rewrite H4 in *.
    injection H1; clear H1; intros; subst.
    specialize (Hy1 _ (refl_equal _)); destruct Hy1.
    specialize (Hy2 _ (refl_equal _)); destruct Hy2.
    intuition; subst.
    hnf; simpl.
    rewrite H3.
    rewrite H4.

    generalize (expr_seq_dec_correct e e0).
    destruct (expr_seq_dec e e0); intuition; subst.

    apply (Expr.Eqb_correct bedrock_type_W) in H0.
    congruence.

    clear H5.
    eapply equalityMatches_correct in H0; eauto.
    destruct H0; simpl in *; intuition.
    destruct H8; intuition.
    subst.
    rewrite H5 in H2; injection H2; clear H2; intros; subst.
    rewrite H8 in H1; injection H1; clear H1; intros; subst.
    rewrite wminus'_def.
    rewrite wminus_def.
    repeat rewrite <- wplus_assoc.
    rewrite (wplus_comm (^~ w0) w0).
    rewrite wminus_inv.
    rewrite (wplus_comm w (wzero 32)).
    rewrite wplus_unit.
    reflexivity.

    rewrite H4 in *; discriminate.
    rewrite H3 in *; discriminate.

    destruct goal; try discriminate.
    destruct t; try discriminate.
    destruct n; try discriminate.
    apply (@lessThanMatches_notEqual_correct uvars vars) in H0; auto.
    destruct H0; intuition.
    destruct H5; intuition.
    hnf.
    simpl in *.
    rewrite H2.
    rewrite H5.
    assumption.
    tauto.
  Qed.

  Lemma wordValid_weaken : forall (u g : env types) (f : word_summary)
    (ue ge : list (sigT (tvarD types))),
    wordValid u g f -> wordValid (u ++ ue) (g ++ ge) f.
  Proof.
    unfold wordValid; intuition.
    induction H0; eauto.
    econstructor; eauto. unfold equalityValid in *.
    repeat match goal with
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- _ ] => erewrite exprD_weaken by eauto
             | [ |- exists x, _ ] => eexists; split; [ reflexivity | ]
           end; auto.
    induction H; eauto.
    econstructor; eauto. clear IHForall. unfold lessThanValid in *.
    repeat match goal with
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- _ ] => erewrite exprD_weaken by eauto
             | [ |- exists x, _ ] => eexists; split; [ reflexivity | ]
           end; auto.
    induction H2; eauto.
    econstructor; eauto. clear IHForall. unfold notEqualValid in *.
    repeat match goal with
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- _ ] => erewrite exprD_weaken by eauto
             | [ |- exists x, _ ] => eexists; split; [ reflexivity | ]
           end; auto.
  Qed.

  Definition wordProver : ProverT types :=
  {| Facts := word_summary
   ; Summarize := wordSummarize
   ; Learn := wordLearn
   ; Prove := wordProve
   |}.

  Definition wordProver_correct : ProverT_correct wordProver funcs.
    eapply Build_ProverT_correct with (Valid := wordValid);
      eauto using wordValid_weaken, wordSummarizeCorrect, wordLearnCorrect, wordProverCorrect.
  Qed.

End WordProver.

Definition WordProver : ProverPackage :=
{| ProverTypes := bedrock_types_r
 ; ProverFuncs := bedrock_funcs_r
 ; Prover_correct := wordProver_correct
|}.
