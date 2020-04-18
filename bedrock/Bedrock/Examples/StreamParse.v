Require Import Coq.omega.Omega.
Require Import Bedrock.Examples.PreAutoSep Bedrock.Examples.Wrap Bedrock.Examples.Conditional.

Import DefineStructured.

Set Implicit Arguments.


(** Simple notation for parsing streams of machine words *)

Inductive pattern0 :=
| Const_ (_ : W)
(* Match this exact word. *)
| Var_ (_ : string)
(* Match anything and stash it in this local variable. *).

Definition pattern := list pattern0.
(* Match a prefix of the stream against these individual word patterns. *)

Definition Const w : pattern := Const_ w :: nil.
Definition Var x : pattern := Var_ x :: nil.

Coercion Const : W >-> pattern.
Coercion Var : string >-> pattern.

Fixpoint matches (p : pattern) (ws : list W) : Prop :=
  match p, ws with
    | nil, _ => True
    | Const_ w :: p', w' :: ws' => w = w' /\ matches p' ws'
    | Var_ _ :: p', _ :: ws' => matches p' ws'
    | _, _ => False
  end.

Fixpoint binds (p : pattern) (ws : list W) : list (string * W) :=
  match p, ws with
    | Const_ _ :: p', _ :: ws' => binds p' ws'
    | Var_ s :: p', w :: ws' => (s, w) :: binds p' ws'
    | _, _ => nil
  end.

Section Parse.
  Hint Extern 1 (Mem _ = Mem _) =>
    eapply scratchOnlyMem; [ | eassumption ];
      simpl; intuition congruence.
  Hint Extern 1 (Mem _ = Mem _) =>
    symmetry; eapply scratchOnlyMem; [ | eassumption ];
      simpl; intuition congruence.

  Hint Resolve evalInstrs_app sepFormula_Mem.

  Hint Extern 2 (interp ?specs2 (![ _ ] (?stn2, ?st2))) =>
    match goal with
      | [ _ : interp ?specs1 (![ _ ] (?stn1, ?st1)) |- _ ] =>
        solve [ equate specs1 specs2; equate stn1 stn2; equate st1 st2; step auto_ext ]
    end.

  Variable stream : string.
  (* Name of local variable containing an array to treat as the stream of words *)
  Variable size : string.
  (* Name of local variable containing the stream length in words *)
  Variable pos : string.
  (* Name of local variable containing the current stream position in words *)

  Variable p : pattern.
  (* We will try to match a prefix of the stream against this pattern. *)

  Variable imports : LabelMap.t assert.
  Hypothesis H : importsGlobal imports.
  Variable modName : string.

  Variables Then Else : cmd imports modName.
  (* Code to run when a single pattern matches or fails, respectively. *)

  Variable ns : list string.
  (* Local variable names *)

  (* Does the pattern match? *)
  Fixpoint guard (p : pattern) (offset : nat) : bexp :=
    match p with
      | nil =>
        Test Rv Le (variableSlot size ns)
        (* Is there enough space left in the stream? *)
      | Const_ w :: p' =>
        And (guard p' (S offset))
        (Test (LvMem (Indir Rp (4 * offset))) IL.Eq w)
      | Var_ _ :: p' => guard p' (S offset)
    end.

  (* Once we know that the pattern matches, we set the appropriate pattern variables with this function. *)
  Fixpoint reads (p : pattern) (offset : nat) : list instr :=
    match p with
      | nil => nil
      | Const_ _ :: p' => reads p' (S offset)
      | Var_ x :: p' => Assign (variableSlot x ns) (LvMem (Indir Rp (4 * offset))) :: reads p' (S offset)
    end.

  Fixpoint suffix (n : nat) (ws : list W) : list W :=
    match n with
      | O => ws
      | S n' => match ws with
                  | nil => nil
                  | w :: ws' => suffix n' ws'
                end
    end.

  Lemma suffix_remains : forall n ws,
    (n < length ws)%nat
    -> suffix n ws = selN ws n :: suffix (S n) ws.
    induction n; destruct ws; simpl; intuition.
    rewrite IHn; auto.
  Qed.

  Fixpoint patternBound (p : pattern) : Prop :=
    match p with
      | nil => True
      | Const_ _ :: p' => patternBound p'
      | Var_ x :: p' => In x ns /\ patternBound p'
    end.

  Fixpoint okVarName (x : string) (p : pattern) : Prop :=
    match p with
      | nil => True
      | Const_ _ :: p' => okVarName x p'
      | Var_ x' :: p' => if string_dec x x' then False else okVarName x p'
    end.

  Definition ThenPre (pre : assert) : assert :=
    (fun stn_st => let (stn, st) := stn_st in
      Ex st', pre (stn, st')
      /\ (AlX, Al V, Al ws, Al r,
        ![ ^[array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st' Sp)] * #0] (stn, st')
        /\ [| sel V size = length ws |]
        ---> [| matches p (suffix (wordToNat (sel V pos)) ws)
          /\ exists st'', Mem st'' = Mem st'
            /\ Regs st'' Sp = Regs st' Sp
            /\ evalInstrs stn st'' (map (fun p => Assign (variableSlot (fst p) ns) (RvImm (snd p)))
              (binds p (suffix (wordToNat (sel V pos)) ws))
              ++ Binop (variableSlot pos ns) (variableSlot pos ns) Plus (length p)
              :: nil) = Some st |]))%PropX.

  Definition ElsePre (pre : assert) : assert :=
    (fun stn_st => let (stn, st) := stn_st in
      Ex st', pre (stn, st')
      /\ (AlX, Al V, Al ws, Al r,
        ![ ^[array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp)] * #0] (stn, st')
        /\ [| sel V size = length ws |]
        ---> [| ~matches p (suffix (wordToNat (sel V pos)) ws) |])
      /\ [| Regs st Sp = Regs st' Sp /\ Mem st = Mem st' |])%PropX.

  (* Here's the raw parsing command, which we will later wrap with nicer VCs. *)
  Definition Parse1_ : cmd imports modName := fun pre =>
    Seq_ H (Straightline_ _ _ (Binop Rv (variableSlot pos ns) Plus (length p)
      :: Binop Rp 4 Times (variableSlot pos ns)
      :: Binop Rp (variableSlot stream ns) Plus Rp
      :: nil))
    (Cond_ _ H _ (guard p O)
      (Seq_ H
        (Straightline_ _ _ (reads p O
          ++ Binop (variableSlot pos ns) (variableSlot pos ns) Plus (length p)
          :: nil))
        (Seq_ H
          (Structured.Assert_ _ _ (ThenPre pre))
          Then))
      (Seq_ H
        (Structured.Assert_ _ _ (ElsePre pre))
        Else))
    pre.

  Hint Rewrite wordToN_nat wordToNat_natToWord_idempotent using assumption : N.
  Require Import Coq.Arith.Arith.

  Hint Resolve goodSize_weaken.

  Opaque mult.

  Lemma bexpTrue_bound : forall specs stn st ws V r fr,
    interp specs
    (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> In size ns
    -> ~In "rp" ns
    -> forall p' offset, bexpTrue (guard p' offset) stn st
      -> Regs st Rv <= sel V size.
    clear H; induction p' as [ | [ ] ]; simpl; intuition eauto.

    prep_locals; evaluate auto_ext; tauto.
  Qed.

  Lemma bexpSafe_guard : forall specs stn st ws V r fr,
    interp specs
    (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> In size ns
    -> ~In "rp" ns
    -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
    -> sel V size = $ (length ws)
    -> forall p' offset,
      Regs st Rv = $ (offset + wordToNat (sel V pos) + length p')
      -> goodSize (offset + wordToNat (sel V pos) + Datatypes.length p')
      -> bexpSafe (guard p' offset) stn st.
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    prep_locals; evaluate auto_ext.

    apply IHp'.
    rewrite H4; f_equal; omega.
    eauto.

    replace (evalCond (LvMem (Rp + 4 * offset)%loc) IL.Eq w stn st)
      with (evalCond (LvMem (Imm (sel V stream ^+ $4 ^* $ (offset + wordToNat (sel V pos))))) IL.Eq w stn st)
        in *.
    assert (goodSize (length ws)) by eauto.
    assert (natToW (offset + wordToNat (sel V pos)) < $ (length ws)).
    specialize (bexpTrue_bound _ H H0 H1 _ _ H6).
    rewrite H3, H4.
    intros.
    apply wle_goodSize in H9; auto; eauto.

    prep_locals; evaluate auto_ext.

    unfold evalCond; simpl.
    rewrite H2.
    match goal with
      | [ |- match ReadWord _ _ ?X with None => _ | _ => _ end
        = match ReadWord _ _ ?Y with None => _ | _ => _ end ] => replace Y with X; auto
    end.
    rewrite mult_comm; rewrite natToW_times4.
    rewrite natToW_plus.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    apply IHp'; eauto.
    rewrite H4; f_equal; omega.
  Qed.

  Lemma bexpTrue_matches : forall specs stn st ws V r fr,
    interp specs
    (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> In size ns
    -> ~In "rp" ns
    -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
    -> forall p' offset, bexpTrue (guard p' offset) stn st
      -> Regs st Rv = $ (offset + wordToNat (sel V pos) + length p')
      -> (offset + wordToNat (sel V pos) <= length ws)%nat
      -> sel V size = $ (length ws)
      -> goodSize (offset + wordToNat (sel V pos) + length p')
      -> matches p' (suffix (offset + wordToNat (sel V pos)) ws).
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    specialize (bexpTrue_bound _ H H0 H1 _ _ H8).
    rewrite H4; intros.
    replace (evalCond (LvMem (Rp + 4 * offset)%loc) IL.Eq w stn st)
      with (evalCond (LvMem (Imm (sel V stream ^+ $4 ^* $ (offset + wordToNat (sel V pos))))) IL.Eq w stn st)
        in *.
    rewrite H6 in H3.
    eapply wle_goodSize in H3.
    rewrite suffix_remains in * by auto.
    assert (natToW (offset + wordToNat (sel V pos)) < natToW (length ws))
      by (apply lt_goodSize; eauto).
    prep_locals; evaluate auto_ext.

    split.
    subst.
    unfold Array.sel.
    rewrite wordToNat_natToWord_idempotent; auto.
    change (goodSize (offset + wordToNat (sel V pos))); eauto.
    change (S (offset + wordToNat (sel V pos))) with (S offset + wordToNat (sel V pos)).
    apply IHp'; auto.
    rewrite H4; f_equal; omega.
    eauto.
    eauto.
    eauto.

    unfold evalCond; simpl.
    rewrite H2.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.


    specialize (bexpTrue_bound _ H H0 H1 _ _ H3).
    rewrite H4; intros.
    rewrite H6 in H8.
    eapply wle_goodSize in H8.
    rewrite suffix_remains in * by auto.
    change (S (offset + wordToNat (sel V pos))) with (S offset + wordToNat (sel V pos)).
    apply IHp'; auto.
    rewrite H4; f_equal; omega.
    eauto.
    eauto.
    eauto.
  Qed.

  Lemma suffix_none : forall n ls,
    (n >= length ls)%nat
    -> suffix n ls = nil.
    induction n; destruct ls; simpl; intuition.
  Qed.

  Lemma bexpFalse_not_matches : forall specs stn st ws V r fr,
    interp specs
    (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> In size ns
    -> ~In "rp" ns
    -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
    -> sel V size = $ (length ws)
    -> forall p' offset, bexpFalse (guard p' offset) stn st
      -> Regs st Rv = $ (offset + wordToNat (sel V pos) + length p')
      -> (offset + wordToNat (sel V pos) <= length ws)%nat
      -> goodSize (offset + wordToNat (sel V pos) + length p')
      -> ~matches p' (suffix (offset + wordToNat (sel V pos)) ws).
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    prep_locals; evaluate auto_ext.
    rewrite H3 in *.
    apply lt_goodSize' in H13.
    omega.
    eauto.
    eauto.


    destruct (le_lt_dec (length ws) (offset + wordToNat (sel V pos))).
    rewrite suffix_none in *; auto.
    rewrite suffix_remains in * by auto.
    assert (natToW (offset + wordToNat (sel V pos)) < natToW (length ws))
      by (apply lt_goodSize; eauto).
    prep_locals; evaluate auto_ext.
    eapply IHp'; eauto.
    rewrite H5; f_equal; omega.

    specialize (bexpTrue_bound _ H H0 H1 _ _ H4).
    rewrite H5; intros.
    destruct (le_lt_dec (length ws) (offset + wordToNat (sel V pos))).
    rewrite suffix_none in *; auto.
    rewrite suffix_remains in * by auto.
    replace (evalCond (LvMem (Rp + 4 * offset)%loc) IL.Eq w stn st)
      with (evalCond (LvMem (Imm (sel V stream ^+ $4 ^* $ (offset + wordToNat (sel V pos))))) IL.Eq w stn st)
        in *.
    assert (natToW (offset + wordToNat (sel V pos)) < natToW (length ws))
      by (apply lt_goodSize; eauto).
    prep_locals; evaluate auto_ext.
    subst.
    apply H16.
    unfold Array.sel.
    rewrite wordToNat_natToWord_idempotent; auto.
    change (goodSize (offset + wordToNat (sel V pos))); eauto.

    unfold evalCond; simpl.
    rewrite H2.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    destruct (le_lt_dec (length ws) (offset + wordToNat (sel V pos))).
    rewrite suffix_none in *; auto.
    rewrite suffix_remains in * by auto.
    intuition; subst.
    eapply IHp'; eauto.
    rewrite H5; f_equal; omega.
  Qed.

  Transparent evalInstrs.
  Opaque evalInstr.

  Lemma reads_nocrash : forall specs stn ws r fr,
    ~In "rp" ns
    -> forall p' offset st V, patternBound p'
      -> interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
      -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
      -> (offset + wordToNat (sel V pos) + length p' <= length ws)%nat
      -> okVarName stream p'
      -> okVarName pos p'
      -> evalInstrs stn st (reads p' offset) = None
      -> False.
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    eapply IHp'; eauto.
    match goal with
      | [ H : (?U <= ?X)%nat |- (?V <= ?X)%nat ] => replace V with U; auto; omega
    end.

    destruct (string_dec stream s); try tauto.
    destruct (string_dec pos s); try tauto.

    case_eq (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc))); intros;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *
      end.

    replace (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc)))
      with (evalInstr stn st (Assign (variableSlot s ns)
        (LvMem (Imm (sel V stream ^+ $4 ^* $ (offset + wordToNat (sel V pos))))))) in *.
    generalize dependent H6; prep_locals.
    assert (natToW (offset + wordToNat (sel V pos)) < $ (length ws)).
    apply lt_goodSize; eauto.
    prep_locals.
    rewrite evalInstr_evalInstrs in H0.
    evaluate auto_ext.
    intros.
    eapply IHp'.
    eauto.
    instantiate (1 := s0).
    step auto_ext.
    reflexivity.
    repeat rewrite sel_upd_ne by congruence.
    assumption.
    instantiate (1 := S offset).
    repeat rewrite sel_upd_ne by congruence.
    match goal with
      | [ H : (?U <= ?X)%nat |- (?V <= ?X)%nat ] => replace V with U; auto; omega
    end.
    assumption.
    assumption.
    assumption.
    Transparent evalInstr.
    simpl.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite H2.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    replace (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc)))
      with (evalInstr stn st (Assign (variableSlot s ns)
        (LvMem (Imm (sel V stream ^+ $4 ^* $ (offset + wordToNat (sel V pos))))))) in *.
    generalize dependent H6; prep_locals.
    assert (natToW (offset + wordToNat (sel V pos)) < $ (length ws)).
    apply lt_goodSize; eauto.
    prep_locals.
    rewrite evalInstr_evalInstrs in H0.
    evaluate auto_ext.

    simpl.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite H2.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.
  Qed.

  Opaque evalInstr.

  Lemma reads_exec' : forall specs stn ws r fr,
    ~In "rp" ns
    -> forall p' offset st st' V, patternBound p'
      -> interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
      -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
      -> (offset + wordToNat (sel V pos) + length p' <= length ws)%nat
      -> okVarName stream p'
      -> okVarName pos p'
      -> evalInstrs stn st (reads p' offset) = Some st'
      -> exists V',
        interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V' r (Regs st Sp) * fr] (stn, st'))
        /\ Regs st' Sp = Regs st Sp.
    clear H; induction p' as [ | [ ] ]; simpl; intuition.

    injection H6; intros; subst.
    eauto.

    eapply IHp'; eauto.
    match goal with
      | [ H : (?U <= ?X)%nat |- (?V <= ?X)%nat ] => replace V with U; auto; omega
    end.

    destruct (string_dec stream s); try tauto.
    destruct (string_dec pos s); try tauto.

    case_eq (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc))); intros;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *
      end.

    replace (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc)))
      with (evalInstr stn st (Assign (variableSlot s ns)
        (LvMem (Imm (sel V stream ^+ $4 ^* $ (offset + wordToNat (sel V pos))))))) in *.
    generalize dependent H6; prep_locals.
    assert (natToW (offset + wordToNat (sel V pos)) < $ (length ws)).
    apply lt_goodSize; eauto.
    prep_locals.
    rewrite evalInstr_evalInstrs in H0.
    evaluate auto_ext.
    intros.
    eapply (IHp' _ _ _ (upd V s (Array.sel ws (offset + wordToNat (sel V pos))))) in H13.
    rewrite <- H1.
    rewrite sel_upd_ne in H13 by congruence.
    assumption.
    eauto.
    step auto_ext.
    reflexivity.
    rewrite H10.
    repeat rewrite sel_upd_ne by congruence.
    W_eq.
    repeat rewrite sel_upd_ne by congruence.
    match goal with
      | [ H : (?U <= ?X)%nat |- (?V <= ?X)%nat ] => replace V with U; auto; omega
    end.
    assumption.
    assumption.
    Transparent evalInstr.
    simpl.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite H2.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    replace (evalInstr stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc)))
      with (evalInstr stn st (Assign (variableSlot s ns)
        (LvMem (Imm (sel V stream ^+ $4 ^* $ (offset + wordToNat (sel V pos))))))) in *.
    generalize dependent H6; prep_locals.
    assert (natToW (offset + wordToNat (sel V pos)) < $ (length ws)).
    apply lt_goodSize; eauto.
    prep_locals.
    rewrite evalInstr_evalInstrs in H0.
    evaluate auto_ext.

    simpl.
    match goal with
      | [ |- match ?E with None => _ | _ => _ end = match ?E' with None => _ | _ => _ end ] =>
        replace E with E'; auto
    end.
    f_equal.
    rewrite H2.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.
  Qed.

  Lemma reads_exec : forall stn st p' offset st',
    evalInstrs stn st (reads p' offset) = Some st'
    -> ~In "rp" ns
    -> forall specs ws r fr V, patternBound p'
      -> interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
      -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
      -> (offset + wordToNat (sel V pos) + length p' <= length ws)%nat
      -> okVarName stream p'
      -> okVarName pos p'

      -> exists V',
        interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V' r (Regs st Sp) * fr] (stn, st'))
        /\ Regs st' Sp = Regs st Sp.
    eauto using reads_exec'.
  Qed.

  Opaque evalInstrs.

  Lemma unify_V : forall specs stn st ws V r sp fr ws' V' r' fr',
    interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V r sp * fr] (stn, st))
    -> sel V size = length ws
    -> sel V' size = length ws'
    -> interp specs (![array ws' (sel V' stream) * locals ("rp" :: ns) V' r' sp * fr'] (stn, st)
       ---> [| forall x, In x ns -> sel V' x = sel V x |])%PropX.
    clear H; intros.
    assert (Hlocals : exists FR, interp specs (![array (toArray ("rp" :: ns) V) sp * FR] (stn, st)))
      by (eexists; unfold locals in H; step auto_ext); destruct Hlocals as [ FR Hlocals ].
    assert (Hlocals' : exists FR', himp specs
      (array ws' (sel V' stream) * locals ("rp" :: ns) V' r' sp * fr')%Sep
      (array (toArray ("rp" :: ns) V') sp * FR')%Sep)
      by (eexists; unfold locals; step auto_ext); destruct Hlocals' as [ FR' Hlocals' ].
    eapply Imply_trans; try (rewrite sepFormula_eq; apply Hlocals').
    simpl.
    replace ((array (V' "rp" :: toArray ns V') sp * FR')%Sep stn (memoryIn (Mem st)))
      with (![array (V' "rp" :: toArray ns V') sp * FR'] (stn, st))%PropX
        by (rewrite sepFormula_eq; reflexivity).
    eapply Imply_trans.
    eapply array_equals; eauto.
    simpl; repeat rewrite length_toArray in *; apply inj_imply; intuition.
    injection H3; clear H3; intros.
    eauto using toArray_sel.
  Qed.

  Lemma unify_ws : forall specs stn st ws V r sp fr ws' V' r' fr' streamV,
    interp specs (![array ws streamV * locals ("rp" :: ns) V r sp * fr] (stn, st))
    -> length ws' = length ws
    -> interp specs (![array ws' streamV * locals ("rp" :: ns) V' r' sp * fr'] (stn, st)
       ---> [| ws' = ws |])%PropX.
    clear H; intros.
    assert (Hlocals : interp specs (![array ws streamV * (locals ("rp" :: ns) V r sp * fr)] (stn, st)))
       by step auto_ext.
    assert (Hlocals' : himp specs
      (array ws' streamV * locals ("rp" :: ns) V' r' sp * fr')%Sep
      (array ws' streamV * (locals ("rp" :: ns) V' r' sp * fr'))%Sep)
      by step auto_ext.
    eapply Imply_trans; try (rewrite sepFormula_eq; apply Hlocals').
    simpl.
    replace ((array ws' streamV * (locals ("rp" :: ns) V' r' sp * fr'))%Sep stn
      (memoryIn (Mem st)))
      with (![array ws' streamV * (locals ("rp" :: ns) V' r' sp * fr')] (stn, st))%PropX
        by (rewrite sepFormula_eq; reflexivity).
    eapply Imply_trans.
    eapply array_equals; eauto.
    apply inj_imply; intuition.
  Qed.

  Transparent mult.

  Theorem unify : forall specs stn st ws V r sp fr ws' V' r' fr',
    interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V r sp * fr] (stn, st))
    -> sel V size = length ws
    -> In stream ns
    -> In size ns
    -> In pos ns
    -> interp specs (![array ws' (sel V' stream) * locals ("rp" :: ns) V' r' sp * fr'] (stn, st)
       /\ [| sel V' size = length ws' |]
       ---> [| ws' = ws /\ sel V' stream = sel V stream /\ sel V' size = sel V size /\ sel V' pos = sel V pos |])%PropX.
    intros.
    apply Imply_I.
    eapply Inj_E; [ eapply And_E2; apply Env; simpl; eauto | ]; intro.
    eapply Inj_E.
    eapply Imply_E.
    apply interp_weaken; eapply unify_V; eauto.
    eapply And_E1; apply Env; simpl; eauto.
    intro.
    apply Inj_E with (goodSize (length ws')).
    rewrite sepFormula_eq; unfold sepFormula_def, starB, star.
    eapply Exists_E; [ eapply And_E1; apply Env; simpl; eauto | cbv beta; intro ].
    eapply Exists_E; [ apply Env; simpl; left; eauto | cbv beta; intro ].
    eapply Exists_E; [ eapply And_E1; eapply And_E2; apply Env; simpl; left; eauto | cbv beta; intro ].
    eapply Exists_E; [ apply Env; simpl; left; eauto | cbv beta; intro ].
    eapply Imply_E.
    apply interp_weaken; apply containsArray_goodSizex'.
    Focus 2.
    eapply And_E1; eapply And_E2; apply Env; simpl; eauto.
    eauto.
    intro.
    repeat rewrite H6 in * by assumption.
    eapply Inj_E.
    eapply Imply_E.
    apply interp_weaken; eapply unify_ws.
    eassumption.
    2: eapply And_E1; apply Env; simpl; eauto.
    apply natToW_inj; congruence || eauto.
    intro.
    apply Inj_I; intuition.
  Qed.

  Theorem splessReads : forall p' offset,
    spless (reads p' offset).
    induction p' as [ | [ ] ]; simpl; intuition.
  Qed.

  Hint Resolve splessReads.

  Opaque evalInstr mult.
  Transparent evalInstrs.

  Lemma simplify_reads : forall st' ws r fr stn specs p' offset st V,
    interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> evalInstrs stn st (reads p' offset) = Some st'
    -> (offset + wordToNat (sel V pos) + length p' <= length ws)%nat
    -> patternBound p'
    -> ~In "rp" ns
    -> Regs st Rp = sel V stream ^+ $4 ^* sel V pos
    -> okVarName stream p'
    -> okVarName pos p'
    -> goodSize (offset + wordToNat (sel V pos) + length p')
    -> evalInstrs stn st (map (fun p0 =>
      Assign
      (LvMem (Sp + S (S (S (S (variablePosition ns (fst p0))))))%loc)
      (RvImm (snd p0))) (binds p' (suffix (offset + wordToNat (sel V pos)) ws))) = Some st'.
    clear H; induction p' as [ | [ ] ]; simpl; intuition;
      rewrite suffix_remains by auto;
        change (S (offset + wordToNat (sel V pos))) with (S offset + wordToNat (sel V pos)); eauto; simpl.

    match goal with
      | [ _ : match ?E with None => _ | _ => _ end = _ |- _ ] => case_eq E; intros
    end; match goal with
           | [ H : _ = _ |- _ ] => rewrite H in *
         end; try discriminate.

    destruct (string_dec stream s); try tauto.
    destruct (string_dec pos s); try tauto.
    assert (evalInstrs stn st (Assign (variableSlot s ns) (LvMem (Rp + 4 * offset)%loc) :: nil) = Some s0)
      by (simpl; rewrite H2; reflexivity).
    clear H2.
    replace (evalInstrs stn st
      (Assign (variableSlot s ns)
        (LvMem (Rp + 4 * offset)%loc) :: nil))
      with (evalInstrs stn st
         (Assign (variableSlot s ns)
            (LvMem (Imm (sel V stream ^+ $4 ^* $ (offset + wordToNat (sel V pos))))) :: nil)) in H10.
    assert (natToW (offset + wordToNat (sel V pos)) < $ (length ws)) by (apply lt_goodSize; eauto).
    prep_locals.
    generalize dependent H0; evaluate auto_ext; intro.
    case_eq (evalInstrs stn s0 (Assign Rv (variableSlot s ns) :: nil)); intros; prep_locals; evaluate auto_ext.
    rewrite sel_upd_eq in H17 by auto.
    unfold evalInstrs in H10, H15.
    repeat (match goal with
              | [ _ : match ?E with None => _ | _ => _ end = _ |- _ ] => case_eq E; intros
            end; match goal with
                   | [ H : _ = _ |- _ ] => rewrite H in *
                 end; try discriminate).
    unfold variablePosition in H19, H20; fold variablePosition in H19, H20.
    destruct (string_dec "rp" s); try congruence.
    simpl in *.
    replace (evalInstr stn st
      (Assign (LvMem (Sp + S (S (S (S (variablePosition ns s)))))%loc)
        (selN ws (offset + wordToNat (sel V pos))))) with (Some s3).
    change (match ws with
              | nil => nil
              | _ :: ws' => suffix (offset + wordToNat (sel V pos)) ws'
            end) with (suffix (S offset + wordToNat (sel V pos)) ws).
    replace (sel V pos) with (sel (upd V s (Array.sel ws (offset + wordToNat (sel V pos)))) pos).
    injection H10; clear H10; intros; subst.
    injection H15; clear H15; intros; subst.
    eapply IHp'.
    rewrite sel_upd_ne by auto.
    apply sepFormula_Mem with s1.
    step auto_ext.
    assert (evalInstrs stn s0
      (Assign Rv (LvMem (Sp + S (S (S (S (variablePosition ns s)))))%loc) :: nil) =
      Some s1).
    simpl; rewrite H19; reflexivity.
    symmetry; eapply scratchOnlyMem; [ | eassumption ].
    simpl; intuition congruence.
    assumption.
    rewrite sel_upd_ne; auto.
    assumption.
    assumption.
    repeat rewrite sel_upd_ne by auto; assumption.
    assumption.
    assumption.
    repeat rewrite sel_upd_ne by auto; eauto.
    repeat rewrite sel_upd_ne by auto; reflexivity.
    rewrite <- H20.

    injection H15; clear H15; intros; subst.
    injection H10; clear H10; intros; subst.
    assert (evalInstrs stn s0
      (Assign Rv (LvMem (Sp + S (S (S (S (variablePosition ns s)))))%loc) :: nil) =
      Some s1) by (simpl; rewrite H19; reflexivity).
    eapply sepFormula_Mem in H18.
    2: symmetry; eapply scratchOnlyMem; eauto; simpl; intuition.
    change (S (S (S (S (variablePosition ns s))))) with (4 + variablePosition ns s) in *.
    prep_locals.
    evaluate auto_ext.
    rewrite sel_upd_eq in H22 by auto.
    unfold Array.sel in H22.
    unfold natToW in H22; rewrite wordToNat_natToWord_idempotent in H22.
    generalize H19 H20 H22; clear; intros.
    Transparent evalInstr.

    apply evalAssign_rhs.
    simpl.
    unfold evalInstr, evalRvalue, evalLvalue, evalLoc in *.

    match goal with
      | [ _ : context[match ?E with None => _ | _ => _ end] |- _ ] =>
        match E with
          | context[match _ with None => _ | _ => _ end] => fail 1
          | _ => destruct E; try discriminate
        end
    end.
    match goal with
      | [ _ : context[match ?E with None => _ | _ => _ end] |- _ ] =>
        match E with
          | context[match _ with None => _ | _ => _ end] => fail 1
          | _ => case_eq E; intros; match goal with
                                      | [ H : _ = _ |- _ ] => rewrite H in *
                                    end; try discriminate
        end
    end.
    injection H20; clear H20; intros; subst; simpl Regs in *; simpl Mem in *.
    match goal with
      | [ _ : context[match ?E with None => _ | _ => _ end] |- _ ] =>
        match E with
          | context[match _ with None => _ | _ => _ end] => fail 1
          | _ => case_eq E; intros; match goal with
                                      | [ H : _ = _ |- _ ] => rewrite H in *
                                    end; try discriminate
        end
    end.
    injection H19; clear H19; intros; subst; simpl Mem in *; simpl Regs in *.
    eapply ReadWriteEq in H.
    rewrite H in H0.
    rewrite <- H22.
    unfold rupd; simpl.
    assumption.

    change (goodSize (offset + wordToNat (sel V pos))); eauto.

    generalize H4; clear; intros.
    simpl.
    rewrite H4.
    match goal with
      | [ |- match match ?E1 with None => _ | _ => _ end with None => _ | _ => _ end
        = match match ?E2 with None => _ | _ => _ end with None => _ | _ => _ end ] =>
      replace E2 with E1; auto
    end.
    f_equal.
    rewrite natToW_plus.
    rewrite mult_comm; rewrite natToW_times4.
    unfold natToW; rewrite natToWord_wordToNat.
    W_eq.
  Qed.

  Opaque evalInstrs.

  Lemma Rv_preserve : forall rv posV len,
    rv = posV ^+ $ (len)
    -> rv = natToW (0 + wordToNat posV + len).
    simpl; intros; subst.
    rewrite natToW_plus.
    f_equal.
    symmetry; apply natToWord_wordToNat.
  Qed.

  Lemma guard_says_safe : forall stn st specs V ws r fr,
    bexpTrue (guard p 0) stn st
    -> Regs st Rv = sel V pos ^+ $ (length p)
    -> interp specs (![array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp) * fr] (stn, st))
    -> In size ns
    -> ~In "rp" ns
    -> sel V size = $ (length ws)
    -> goodSize (wordToNat (sel V pos) + Datatypes.length p)
    -> (0 + wordToNat (sel V pos) + length p <= length ws)%nat.
    simpl; intros.
    apply wle_goodSize.
    rewrite natToW_plus.
    unfold natToW; rewrite natToWord_wordToNat.
    rewrite <- H1.
    rewrite <- H5.
    eapply bexpTrue_bound; eauto.
    eauto.
    eauto.
  Qed.

  Opaque variablePosition.

  Hint Resolve Rv_preserve bexpSafe_guard guard_says_safe bexpFalse_not_matches simplify_reads.
  Hint Immediate sym_eq.

  Ltac wrap := wrap0; post; wrap1.

  Definition Parse1 : cmd imports modName.
    refine (Wrap _ H _ Parse1_
      (fun pre x => Postcondition (Then (ThenPre pre)) x
        \/ Postcondition (Else (ElsePre pre)) x)%PropX
      (fun pre =>
        In stream ns
        :: In size ns
        :: In pos ns
        :: (~In "rp" ns)
        :: patternBound p
        :: okVarName stream p
        :: okVarName pos p
        :: (forall stn st specs,
          interp specs (pre (stn, st))
          -> interp specs (ExX, Ex V, Ex ws, Ex r,
            ![ ^[array ws (sel V stream) * locals ("rp" :: ns) V r (Regs st Sp)] * #0] (stn, st)
            /\ [| sel V size = length ws
              /\ goodSize (wordToNat (sel V pos) + length p)
              /\ (wordToNat (sel V pos) <= length ws)%nat |]))%PropX
        :: VerifCond (Then (ThenPre pre))
        ++ VerifCond (Else (ElsePre pre)))
      _ _); abstract (wrap;
        try match goal with
              | [ H : context[reads] |- _ ] => generalize dependent H
            end; evaluate auto_ext; intros; eauto;
        repeat match goal with
                 | [ H : evalInstrs _ _ (_ ++ _) = None |- _ ] =>
                   apply evalInstrs_app_fwd_None in H; destruct H as [ | [ ? [ ? ] ] ]; intuition
                 | [ H : evalInstrs _ _ (_ ++ _) = Some _ |- _ ] =>
                   apply evalInstrs_app_fwd in H; destruct H as [ ? [ ] ]
                 | [ H : evalInstrs _ _ (reads _ _) = Some _ |- _ ] =>
                   edestruct (reads_exec _ _ H) as [V' [ ] ]; eauto; evaluate auto_ext
               end;
        try match goal with
              | [ |- exists x, _ /\ _ ] => eexists; split; [ solve [ eauto ] | try split; intros ];
                try (autorewrite with sepFormula; simpl; eapply Imply_trans; [
                  eapply unify; eauto
                  | apply inj_imply; intuition; subst; simpl in * ] )
              | _ => solve [ eapply reads_nocrash; eauto ]
            end;
        repeat match goal with
                 | _ => solve [ eauto ]
                 | [ H : _ = _ |- _ ] => rewrite H in *
                 | [ |- context[suffix ?N _] ] =>
                   match N with
                     | 0 + _ => fail 1
                     | _ =>
                       change N with (0 + N)
                   end
                 | [ H : matches ?a (suffix ?b ?c) |- False ] =>
                   assert (~matches a (suffix (0 + b) c)); try tauto; clear H
                 | [ _ : evalInstrs _ ?x (reads _ _) = Some _ |- _ ] => exists x; split; eauto
                 | _ => solve [ eapply bexpTrue_matches; eauto ]
               end).
  Defined.

End Parse.

Definition ParseOne (stream size pos : string) (p : pattern) (Then Else : chunk) : chunk := fun ns res =>
  Structured nil (fun _ _ H => Parse1 stream size pos p H (toCmd Then _ H ns res) (toCmd Else _ H ns res) ns).

Infix "++" := (fun p1 p2 : pattern => app p1 p2) : pattern_scope.
Delimit Scope pattern_scope with pattern.

Notation "'Match1' stream 'Size' size 'Position' pos 'Pattern' p { c1 } 'else' { c2 }" :=
  (ParseOne stream size pos p%pattern c1 c2)
  (no associativity, at level 95, stream at level 0, size at level 0, pos at level 0, p at level 0) : SP_scope.

Ltac parse0 := try solve [ intuition congruence ].

Ltac especialize H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             let v := fresh in evar (v : T); let v' := eval unfold v in v in clear v; specialize (H v')
         end.

Ltac parse1 solver :=
  match goal with
    | [ H : forall (a : _ -> _), _ |- _ ] =>
      especialize H; post;
      match goal with
        | [ H : interp ?specs (?P ---> ?Q)%PropX |- _ ] =>
          let H' := fresh in assert (H' : interp specs P) by (propxFo; step auto_ext || solver);
            specialize (Imply_sound H H'); clear H H'; intro H
      end; propxFo; autorewrite with StreamParse in *; simpl in *

    | [ H : interp _ (![ _ ] _) |- _ ] => eapply Wrap.sepFormula_Mem in H; [ | eassumption ]
  end.

Ltac reveal_slots :=
  repeat match goal with
           | [ H : evalInstrs _ _ _ = _ |- _ ] =>
             progress unfold variableSlot in H; simpl in H
         end.

Hint Rewrite roundTrip_0 sel_upd_eq sel_upd_ne using congruence : StreamParse.

Hint Extern 1 (_ <= _)%nat => omega : StreamParse.

Ltac parse2 := autorewrite with StreamParse; auto with StreamParse.

Definition ParseOne' stream size pos (pr : pattern * chunk) :=
  ParseOne stream size pos (fst pr) (snd pr).

Notation "'Case' p c 'end'" := (p%pattern, c)
  (no associativity, at level 0, p at level 0, c at level 95, only parsing) : Case_scope.
Delimit Scope Case_scope with Case_.

Notation "'Match' stream 'Size' size 'Position' pos { case1 ;; .. ;; caseN }" :=
  (fun c : chunk => ParseOne' stream size pos case1%Case_ (..
    (ParseOne' stream size pos caseN%Case_
      c) ..))
  (no associativity, at level 95, stream at level 0, size at level 0, pos at level 0,
    case1 at next level, caseN at next level) : SP_scope.

Notation "'Default' { c }" := c (at level 0, c at level 95, no associativity, only parsing) : SP_scope.
