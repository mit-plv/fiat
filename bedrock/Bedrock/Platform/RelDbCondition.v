Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Wrap Bedrock.Platform.StringOps Bedrock.Platform.Malloc Bedrock.Platform.ArrayOps Bedrock.Platform.Buffers Bedrock.Platform.Bags.
Require Import Bedrock.Platform.RelDb.

Set Implicit Arguments.

Local Hint Extern 1 (@eq W _ _) => words.


(** * Iterating over matching rows of a table *)

Opaque mult.
Local Infix ";;" := SimpleSeq : SP_scope.

Section Condition.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.

  Variable tptr : W.
  Variable sch : schema.

  (* Store a pointer to the current row data in this variable.
   * in these variables. *)
  Variables data : string.

  (* Test to use in filtering rows *)
  Variable cond : condition.

  (* One field test, storing Boolean result in "matched" *)
  Definition compileEquality (e : equality) : chunk :=
    match resolve sch (fst e) with
      | None => Fail
      | Some offset =>
        "tmp" <- data;;
        "ibuf" <-* "tmp";;
        "ilen" <-* "tmp" + 4;;

        Assert [Al bs, Al a : A, Al rcols, Al rbs,
          PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
            * [| inputOk V (exps cond) |] * invPre a V
            * (V data ==*> V "ibuf", V "ilen") * array (posl rcols) (V data ^+ $8)
            * array (lenl rcols) (V data ^+ $8 ^+ $ (length sch * 4)) * array8 rbs (V "ibuf")
            * [| length rbs = wordToNat (V "ilen") |] * [| length rcols = length sch |]
            * [| inBounds (V "ilen") rcols |] * [| V data <> 0 |]
            * [| freeable (V data) (2 + length sch + length sch) |]
            * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (length rbs) |]
            * [| natToW offset < natToW (length (posl rcols)) |]%word
          POST[R] array8 bs (V "buf") * invPost a V R];;

        "tmp" <- data + 8;;
        "ipos" <-* "tmp" + (4 * offset)%nat;;

        Assert [Al bs, Al a : A, Al rcols, Al rbs,
          PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
            * [| inputOk V (exps cond) |] * invPre a V
            * (V data ==*> V "ibuf", V "ilen") * array (posl rcols) (V data ^+ $8)
            * array (lenl rcols) (V data ^+ $8 ^+ $ (length sch * 4)) * array8 rbs (V "ibuf")
            * [| length rbs = wordToNat (V "ilen") |] * [| length rcols = length sch |]
            * [| inBounds (V "ilen") rcols |] * [| V data <> 0 |]
            * [| freeable (V data) (2 + length sch + length sch) |]
            * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (length rbs) |]
            * [| V "ipos" = Array.selN (posl rcols) offset |]
            * [| natToW offset < natToW (length (lenl rcols)) |]%word
          POST[R] array8 bs (V "buf") * invPost a V R];;

        "tmp" <- data + 8;;
        "tmp" <- "tmp" + (length sch * 4)%nat;;
        "tmp" <-* "tmp" + (4 * offset)%nat;;

        Assert [Al bs, Al a : A, Al rcols, Al rbs,
          PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
            * [| inputOk V (exps cond) |] * invPre a V
            * (V data ==*> V "ibuf", V "ilen") * array (posl rcols) (V data ^+ $8)
            * array (lenl rcols) (V data ^+ $8 ^+ $ (length sch * 4)) * array8 rbs (V "ibuf")
            * [| length rbs = wordToNat (V "ilen") |] * [| length rcols = length sch |]
            * [| inBounds (V "ilen") rcols |] * [| V data <> 0 |]
            * [| freeable (V data) (2 + length sch + length sch) |]
            * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (length rbs) |]
            * [| V "ipos" = Array.selN (posl rcols) offset |]
            * [| V "tmp" = Array.selN (lenl rcols) offset |]
          POST[R] array8 bs (V "buf") * invPost a V R];;

        match snd e with
          | Const s =>
            If ("tmp" <> String.length s) {
              (* Field value has wrong length to match. *)
              "matched" <- 0
            } else {
              StringEq "ibuf" "ilen" "ipos" "matched" s
              (fun (a_bs : A * list B) V => array8 (snd a_bs) (V "buf")
                * [| length (snd a_bs) = wordToNat (V "len") |]
                * [| inputOk V (exps cond) |] * invPre (fst a_bs) V
                * Ex rcols,
                  (V data ==*> V "ibuf", V "ilen") * array (posl rcols) (V data ^+ $8)
                  * array (lenl rcols) (V data ^+ $8 ^+ $ (length sch * 4))
                  * [| length rcols = length sch |]
                  * [| inBounds (V "ilen") rcols |] * [| V data <> 0 |]
                  * [| freeable (V data) (2 + length sch + length sch) |]
                  * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (wordToNat (V "ilen")) |]
                  * [| V "ipos" = Array.selN (posl rcols) offset |])%Sep
              (fun _ a_bs V R => array8 (snd a_bs) (V "buf") * invPost (fst a_bs) V R)%Sep
            }
          | Input pos len =>
            If ("tmp" <> len) {
              "matched" <- 0
            } else {
              "matched" <-- Call "array8"!"equal"("ibuf", "ipos", "buf", pos, len)
              [Al bs, Al a : A,
                PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
                  * [| inputOk V (exps cond) |] * row sch (V data) * invPre a V
                POST[R] array8 bs (V "buf") * invPost a V R]
            }
        end
    end%SP.

  Variable mn : string.
  Variable im : LabelMap.t assert.
  Variable H : importsGlobal im.
  Variable ns : list string.
  Variable res : nat.

  Definition eqinv' := Al bs, Al a : A,
    PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |]
      * [| inputOk V (exps cond) |]
      * row sch (V data) * invPre a V
    POST[R] array8 bs (V "buf") * invPost a V R.

  Definition eqinv := eqinv' true (fun w => w).

  Hypothesis not_rp : ~In "rp" ns.
  Hypothesis included : incl baseVars ns.
  Hypothesis reserved : (res >= 10)%nat.
  Hypothesis wellFormed : wfEqualities ns sch cond.

  Hypothesis weakenPre : (forall a V V', (forall x, x <> "ibuf" -> x <> "ilen" -> x <> "tmp"
    -> x <> "ipos" -> x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x)
  -> invPre a V ===> invPre a V').

  Hypothesis weakenPost : (forall a V V' R, (forall x, x <> "ibuf" -> x <> "ilen" -> x <> "tmp"
    -> x <> "ipos" -> x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x)
  -> invPost a V R = invPost a V' R).

  Lemma resolve_ok : forall e s,
    wfEquality ns s e
    -> exists offset, resolve s (fst e) = Some offset
      /\ (offset < length s)%nat.
    unfold wfEquality; induction s; simpl; intuition subst;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; intuition eauto.
    destruct H1; intuition idtac.
    rewrite H3; eauto.
  Qed.

  Hypothesis matched_data : "matched" <> data.

  Lemma compileEquality_post : forall e pre,
    wfEquality ns sch e
    -> (forall specs st,
      interp specs (pre st)
      -> interp specs (eqinv ns res st))
    -> forall specs st,
      interp specs (Postcondition (toCmd (compileEquality e) mn (im := im) H ns res pre) st)
      -> interp specs (eqinv ns res st).
    unfold compileEquality; intros.
    match goal with
      | [ H : _ |- _ ] => destruct (resolve_ok H); intuition idtac; destruct H
    end.
    match goal with
      | [ H : resolve _ _ = _ |- _ ] => rewrite H in *
    end.
    destruct e as [ ? [ ] ]; simpl in *; intuition idtac.

    v.
    v.
  Qed.

  Hypothesis equal : "array8"!"equal" ~~ im ~~> ArrayOps.equalS.

  Hypothesis data_rp : data <> "rp".
  Hypothesis data_ibuf : data <> "ibuf".
  Hypothesis data_ipos : data <> "ipos".
  Hypothesis data_ilen : data <> "ilen".
  Hypothesis data_tmp : data <> "tmp".
  Hypothesis data_ns : In data ns.

  Hypothesis goodSize_sch : goodSize (length sch).

  Lemma length_posl : forall ls, length (posl ls) = length ls.
    clear; induction ls; simpl; intuition.
  Qed.

  Lemma length_lenl : forall ls, length (lenl ls) = length ls.
    clear; induction ls; simpl; intuition.
  Qed.

  Lemma length_match : forall x (ls : list (W * W)),
    (x < length sch)%nat
    -> length ls = length sch
    -> natToW x < natToW (Datatypes.length ls).
    generalize goodSize_sch; clear; intros.
    pre_nomega.
    rewrite wordToNat_natToWord_idempotent.
    rewrite wordToNat_natToWord_idempotent.
    congruence.
    rewrite H0; assumption.
    change (goodSize x); eapply goodSize_weaken; eauto.
  Qed.

  Lemma length_match_posl : forall x ls,
    (x < length sch)%nat
    -> length ls = length sch
    -> natToW x < natToW (Datatypes.length (posl ls)).
    intros; rewrite length_posl; auto using length_match.
  Qed.

  Lemma length_match_lenl : forall x ls,
    (x < length sch)%nat
    -> length ls = length sch
    -> natToW x < natToW (Datatypes.length (lenl ls)).
    intros; rewrite length_lenl; auto using length_match.
  Qed.

  Hint Immediate length_match_posl length_match_lenl.

  Lemma selN_col : forall x ls,
    (x < length sch)%nat
    -> Array.sel ls (natToW x) = selN ls x.
    generalize goodSize_sch; clear; unfold Array.sel; intros; f_equal.
    apply wordToNat_natToWord_idempotent.
    change (goodSize x).
    eapply goodSize_weaken; eauto.
  Qed.

  Hint Immediate selN_col.

  Lemma inBounds_selN' : forall len cols,
    inBounds len cols
    -> forall col, (col < length cols)%nat
      -> (wordToNat (selN (posl cols) col) + wordToNat (selN (lenl cols) col) <= wordToNat len)%nat.
    clear; induction cols; inversion 1; simpl; intuition; destruct col; intuition.
  Qed.

  Lemma inBounds_selN : forall len cols,
    inBounds len cols
    -> forall col a b c, a = selN (posl cols) col
      -> b = selN (lenl cols) col
      -> c = wordToNat len
      -> (col < length cols)%nat
      -> (wordToNat a + wordToNat b <= c)%nat.
    intros; subst; eauto using inBounds_selN'.
  Qed.

  Hint Extern 1 (_ + _ <= _)%nat =>
    eapply inBounds_selN; try eassumption; (cbv beta; congruence).

  Lemma weakened_bound : forall pos cols x len,
    inBounds len cols
    -> pos = selN (posl cols) x
    -> (x < length cols)%nat
    -> pos <= len.
    clear; intros; subst.
    eapply inBounds_selN in H; try (reflexivity || eassumption).
    nomega.
  Qed.

  Hint Extern 1 (_ <= _) => eapply weakened_bound; try eassumption; (cbv beta; congruence).

  Hint Resolve use_inputOk.

  Lemma In_exps : forall s e c,
    In (s, e) c
    -> In e (exps c).
    clear; induction c; simpl; intuition (subst; auto).
  Qed.

  Hint Immediate In_exps.

  Lemma compileEquality_vcs : forall e pre,
    wfEquality ns sch e
    -> In e cond
    -> (forall specs st,
      interp specs (pre st)
      -> interp specs (eqinv ns res st))
    -> vcs (VerifCond (toCmd (compileEquality e) mn (im := im) H ns res pre)).
      unfold compileEquality; intros.
      match goal with
        | [ H : _ |- _ ] => destruct (resolve_ok H); intuition idtac; destruct H
      end.
      match goal with
        | [ H : resolve _ _ = _ |- _ ] => rewrite H in *
      end.
      wrap0.

      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.

      destruct e as [ ? [ ] ]; simpl in *; intuition idtac.

      repeat match goal with
               | [ |- vcs _ ] => constructor
             end; intros.

      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.
      v.

      repeat match goal with
               | [ |- vcs _ ] => constructor
             end; intros.

      (* Something bizarre is happening here, with [destruct] not clearing a hypothesis
       * within [propxFo]. *)
      apply simplify_fwd in H25.
      repeat match goal with
               | [ H : simplify _ (Ex x, _) _ |- _ ] => destruct H
             end.
      apply simplify_bwd in H25.
      v.

      v.
      v.
      v.
      v.
  Qed.

  Fixpoint compileEqualities (es : condition) : chunk :=
    match es with
      | nil => "matched" <- 1
      | e :: es' =>
        compileEquality e;;
        If ("matched" = 0) {
          Skip
        } else {
          compileEqualities es'
        }
    end%SP.

  Lemma wfEqualities_inv1 : forall ns sch e es,
    wfEqualities ns sch (e :: es)
    -> wfEquality ns sch e.
    inversion 1; auto.
  Qed.

  Lemma wfEqualities_inv2 : forall ns sch e es,
    wfEqualities ns sch (e :: es)
    -> wfEqualities ns sch es.
    inversion 1; auto.
  Qed.

  Hint Immediate wfEqualities_inv1 wfEqualities_inv2.

  Lemma compileEqualities_post : forall es pre,
    wfEqualities ns sch es
    -> (forall specs st,
      interp specs (pre st)
      -> interp specs (eqinv ns res st))
    -> forall specs st,
      interp specs (Postcondition (toCmd (compileEqualities es) mn (im := im) H ns res pre) st)
      -> interp specs (eqinv ns res st).
    induction es; simpl; intuition idtac;
      (pre;
        repeat (match goal with
                  | [ H : interp _ (Postcondition (toCmd (compileEquality _) _ _ _ _ _) _) |- _ ] =>
                    apply compileEquality_post in H
                  | [ IH : forall pre : _ -> _, _, H : interp _ (Postcondition _ _) |- _ ] =>
                    apply IH in H
                end; eauto; pre); t).
  Qed.

  Lemma compileEqualities_vcs : forall es pre,
    wfEqualities ns sch es
    -> incl es cond
    -> (forall specs st,
      interp specs (pre st)
      -> interp specs (eqinv ns res st))
    -> vcs (VerifCond (toCmd (compileEqualities es) mn (im := im) H ns res pre)).
    induction es; intros; try match goal with
                                | [ H : incl _ cond |- _ ] => apply incl_peel in H
                              end; wrap0;
    (repeat (match goal with
               | _ => apply compileEquality_vcs
               | [ H : interp _ (Postcondition (toCmd (compileEquality _) _ _ _ _ _) _) |- _ ] =>
                 apply compileEquality_post in H
               | [ IH : forall pre : _ -> _, _ |- vcs _ ] =>
                 apply IH
             end; eauto; pre); t).
  Qed.
End Condition.
