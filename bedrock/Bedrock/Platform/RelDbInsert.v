Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Wrap Bedrock.Platform.StringOps Bedrock.Platform.Malloc Bedrock.Platform.ArrayOps Bedrock.Platform.Buffers Bedrock.Platform.Bags.
Require Import Bedrock.Platform.SinglyLinkedList Bedrock.Platform.ListSegment Bedrock.Platform.RelDb.

Set Implicit Arguments.

Local Hint Extern 1 (@eq W _ _) => words.


(** * Inserting into a table *)

Opaque mult.
Local Infix ";;" := SimpleSeq : SP_scope.

Section Insert.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.

  Variable tptr : W.
  Variable sch : schema.
  Variable bufSize : W.

  (* "WHERE" clause *)
  Variable es : list exp.

  (* Precondition and postcondition *)
  Definition invar :=
    Al a : A, Al bs,
    PRE[V] array8 bs (V "buf") * table sch tptr * mallocHeap 0
      * [| length bs = wordToNat (V "len") |] * [| inputOk V es |] * invPre a V
    POST[R] array8 bs (V "buf") * invPost a V R.

  (* Write the value of an expression into a new row's buffer. *)
  Definition writeExp (col : nat) (e : exp) : chunk :=
    match e with
      | Const s => StringWrite "ibuf" "ilen" "ipos" "overflowed" s
        (fun (p : list B * A) V => array8 (fst p) (V "buf") * mallocHeap 0 * table sch tptr
          * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
          * array (lenl cols) (V "row" ^+ $8 ^+ $ (length sch * 4))
          * [| length (fst p) = wordToNat (V "len") |] * [| length cols = length sch |]
          * [| V "row" <> 0 |] * [| freeable (V "row") (2 + length sch + length sch) |]
          * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (wordToNat (V "ilen")) |]
          * [| inBounds (V "ilen") (firstn col cols) |] * [| inputOk V es |] * invPre (snd p) V)%Sep
        (fun _ (p : list B * A) V R => array8 (fst p) (V "buf") * invPost (snd p) V R)%Sep
      | Input start len =>
        "tmp" <- "ilen" - "ipos";;
        If ("tmp" < len) {
        "overflowed" <- 1
        } else {
          Call "array8"!"copy"("ibuf", "ipos", "buf", start, len)
          [Al a : A, Al bs, Al bsI,
            PRE[V] array8 bs (V "buf") * table sch tptr
              * [| V "ipos" <= V "ilen" |]%word
              * array8 bsI (V "ibuf") * [| length bsI = wordToNat (V "ilen") |] * [| V "ibuf" <> 0 |]
              * [| freeable8 (V "ibuf") (wordToNat (V "ilen")) |]
              * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
              * array (lenl cols) (V "row" ^+ $8 ^+ $ (length sch * 4))
              * [| length bs = wordToNat (V "len") |] * [| length cols = length sch |]
              * [| V "row" <> 0 |] * [| freeable (V "row") (2 + length sch + length sch) |]
              * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (wordToNat (V "ilen")) |]
              * [| inBounds (V "ilen") (firstn col cols) |] * [| inputOk V es |]
              * [| V len <= V "ilen" ^- V "ipos" |]%word
              * invPre a V * mallocHeap 0
            POST[R] array8 bs (V "buf") * invPost a V R];;
          "ipos" <- "ipos" + len
        }
    end%SP.

  Definition winv' (col : nat) :=
    Al a : A, Al bs, Al bsI,
      PRE[V] array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * array8 bsI (V "ibuf") * [| length bsI = wordToNat (V "ilen") |]
        * [| V "ipos" <= V "ilen" |]
        * Ex cols, (V "row" ==*> V "ibuf", V "ilen") * array (posl cols) (V "row" ^+ $8)
        * array (lenl cols) (V "row" ^+ $8 ^+ $ (length sch * 4))
        * [| length bs = wordToNat (V "len") |] * [| length cols = length sch |]
        * [| V "row" <> 0 |] * [| freeable (V "row") (2 + length sch + length sch) |]
        * [| V "ibuf" <> 0 |] * [| freeable8 (V "ibuf") (wordToNat (V "ilen")) |]
        * [| inBounds (V "ilen") (firstn col cols) |] * [| inputOk V es |] * invPre a V
      POST[R] array8 bs (V "buf") * invPost a V R.

  Definition winv (col : nat) := winv' col true (fun w => w).

  Fixpoint writeExps (col : nat) (es : list exp) {struct es} : chunk :=
    match es with
      | nil => Skip
      | e :: es' =>
        (* Save the current position as the start of the current column. *)
        "tmp" <- "row" + 8;;
        "tmp" + (4 * col)%nat *<- "ipos";;

        (* Check if the current item is small enough to fit in the buffer. *)
        "tmp" <- "ilen" - "ipos";;
        If ("tmp" < lengthOf e) {
          (* It doesn't fit.  Save the "safe" length 0.  [writeExp] will set "overflowed" later. *)
          "tmp" <- "row" + 8;;
          "tmp" <- "tmp" + (length sch * 4)%nat;;
          "tmp" + (4 * col)%nat *<- 0
        } else {
          (* Good, it fits.  Save the proper length. *)
          "tmp" <- "row" + 8;;
          "tmp" <- "tmp" + (length sch * 4)%nat;;
          "tmp" + (4 * col)%nat *<- lengthOf e
        };;
        Assert [winv' (S col)];;
        writeExp (S col) e;;
        writeExps (S col) es'
    end%SP.

  Definition Insert' : chunk := (
    "ibuf" <-- Call "buffers"!"bmalloc"(bufSize)
    [Al a : A, Al bs,
      PRE[V, R] R =?>8 (wordToNat bufSize * 4) * [| R <> 0 |] * [| freeable R (wordToNat bufSize) |]
        * array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * [| length bs = wordToNat (V "len") |] * [| inputOk V es |] * invPre a V
      POST[R'] array8 bs (V "buf") * invPost a V R'];;

    "row" <-- Call "malloc"!"malloc"(0, (2 + length sch + length sch)%nat)
    [Al a : A, Al bs, Al bsI,
      PRE[V, R] array8 bsI (V "ibuf") * [| length bsI = (wordToNat bufSize * 4)%nat |] * [| V "ibuf" <> 0 |]
        * [| freeable (V "ibuf") (wordToNat bufSize) |]
        * R =?> (2 + length sch + length sch)%nat * [| R <> 0 |]
        * [| freeable R (2 + length sch + length sch)%nat |]
        * array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * [| length bs = wordToNat (V "len") |] * [| inputOk V es |] * invPre a V
      POST[R'] array8 bs (V "buf") * invPost a V R'];;

    "row" *<- "ibuf";;
    "ipos" <- 0;;
    "ilen" <- (4 * bufSize)%word;;
    "row"+4 *<- "ilen";;

    Note [expand_allocated 8];;

    writeExps O es;;

    "tmp" <-- Call "malloc"!"malloc"(0, 2)
    [Al a : A, Al bs,
      PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
        * row sch (V "row") * array8 bs (V "buf") * table sch tptr * mallocHeap 0
        * [| length bs = wordToNat (V "len") |] * [| inputOk V es |] * invPre a V
      POST[R'] array8 bs (V "buf") * invPost a V R'];;

    "tmp" *<- "row";;
    "tmp"+4 *<- $[tptr];;
    tptr *<- "tmp"
  )%SP.

  Section writeExps_correct.
    Variable mn : string.
    Variable im : LabelMap.t assert.
    Variable H : importsGlobal im.
    Variable ns : list string.
    Variable res : nat.

    Hypothesis not_rp : ~In "rp" ns.
    Hypothesis included : incl baseVars ns.
    Hypothesis reserved : (res >= 10)%nat.
    Hypothesis wellFormed : wfExps ns es.

    Hypothesis weakenPre : (forall a V V', (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
    -> invPre a V ===> invPre a V').

    Hypothesis weakenPost : (forall a V V' R, (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
    -> invPost a V R = invPost a V' R).

    Hypothesis copy : "array8"!"copy" ~~ im ~~> ArrayOps.copyS.

    Lemma writeExp_correct_vcs : forall e col pre,
      wfExp ns e
      -> In e es
      -> (forall specs st,
        interp specs (pre st)
        -> interp specs (winv col ns res st))
      -> vcs (VerifCond (toCmd (writeExp col e) mn (im := im) H ns res pre)).
      destruct e; wrap0.

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
      v.
      v.
      v.
    Qed.

    Lemma writeExp_correct_post : forall e col pre,
      wfExp ns e
      -> In e es
      -> (forall specs st,
        interp specs (pre st)
        -> interp specs (winv col ns res st))
      -> forall specs st,
        interp specs (Postcondition (toCmd (writeExp col e) mn (im := im) H ns res pre) st)
        -> interp specs (winv col ns res st).
      destruct e; wrap0.

      v.
      v.
      v.
    Qed.

    Hypothesis length_es : length es = length sch.
    Hypothesis goodSize_sch : goodSize (length sch).

    Ltac split_IH := intros;
      match goal with
        | [ IH : forall pre : settings * state -> PropX _ _, _ |- _ ] =>
          generalize (fun a b c d e => proj1 (IH a b c d e));
            generalize (fun a b c d e => proj2 (IH a b c d e));
              clear IH; intros
      end;
      match goal with
        | [ H : incl (_ :: _) _ |- _ ] => apply incl_peel in H; destruct H
      end.

    Ltac basic_eauto :=
      match goal with
        | [ |- forall x, _ ] => idtac
        | [ |- Logic.ex _ ] => idtac
        | _ => simpl in *; eauto
      end.

    Lemma inBounds_move : forall ilen n m ls,
      inBounds ilen (firstn (S (n - S m)) ls)
      -> (S m <= n)%nat
      -> inBounds ilen (firstn (n - m) ls).
      intros; replace (n - m) with (S (n - S m)) by omega; auto.
    Qed.

    Hint Immediate inBounds_move.

    Lemma inBounds_wiggle : forall ilen n m col ls,
      inBounds ilen (firstn m ls)
      -> col = m - S n
      -> (S n <= m)%nat
      -> inBounds ilen (match ls with nil => nil | x :: ls' => x :: firstn (n + col) ls' end).
      intros; subst; replace m with (S (n + (m - S n))) in * |- by omega; auto.
    Qed.

    Hint Immediate inBounds_wiggle.

    Hint Rewrite Minus.le_plus_minus_r using (simpl in *; omega) : sepFormula.

    Ltac use_IH :=
      match goal with
        | [ col := ?E |- _ ] =>
          match goal with
            | [ |- appcontext[writeExps (S col)] ] =>
              change (writeExps (S col)) with (writeExps (S E))
          end; rewrite moveS by assumption;
          match goal with
            | [ H : forall x : settings * state -> PropX _ _, _ |- _ ] =>
              apply H; basic_eauto
          end

        | [ H : interp _ (Postcondition (toCmd (writeExps (S ?col) _) _ _ _ _ _) _),
            H' : forall a, wfExps _ _ -> _ |- _ ] =>
          unfold col in H; rewrite moveS in H by (simpl in *; omega);
            eapply H' in H; basic_eauto

        | _ => eapply writeExp_correct_vcs; basic_eauto
        | [ H : interp _ (Postcondition _ _) |- _ ] => eapply writeExp_correct_post in H; basic_eauto
      end; pre.

    Ltac we := repeat use_IH; t; my_descend.
    Ltac swe := solve [ we ].
    Ltac awe := abstract we.

    Lemma writeExps_correct : forall es0 pre,
      wfExps ns es0
      -> incl es0 es
      -> (length es0 <= length es)%nat
      -> let col := length es - length es0 in
        (forall specs st,
          interp specs (pre st)
          -> interp specs (winv col ns res st))
        -> vcs (VerifCond (toCmd (writeExps col es0) mn (im := im) H ns res pre))
        /\ (forall specs st,
          interp specs (Postcondition (toCmd (writeExps col es0) mn (im := im) H ns res pre) st)
          -> interp specs (winv (length es0 + col) ns res st)).
      induction es0.

      wrap0.

      split_IH.
      wrap0.
      wrap0.

      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
      awe.
    Qed.
  End writeExps_correct.

  Notation InsertVcs := (fun im ns res =>
    (~In "rp" ns) :: incl baseVars ns
    :: (forall a V V', (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
      -> invPre a V ===> invPre a V')
    :: (forall a V V' R, (forall x, x <> "ibuf" -> x <> "row" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> sel V x = sel V' x)
      -> invPost a V R = invPost a V' R)
    :: (res >= 10)%nat
    :: (bufSize >= natToW 2)
    :: goodSize (2 + length sch + length sch)
    :: goodSize (4 * wordToNat bufSize)
    :: wfExps ns es
    :: "buffers"!"bmalloc" ~~ im ~~> bmallocS
    :: "malloc"!"malloc" ~~ im ~~> mallocS
    :: "array8"!"copy" ~~ im ~~> ArrayOps.copyS
    :: (length es = length sch)
    :: goodSize (length sch)
    :: nil).

  Hint Immediate incl_refl.

  Require Import Coq.Arith.Div2.

  Lemma div2_double : forall n, div2 (n + n) = n.
    apply div2_double'.
  Qed.

  Hint Rewrite div2_double : sepFormula.

  Lemma four_duh : forall n,
    goodSize (4 * wordToNat bufSize)
    -> n = wordToNat bufSize * 4
    -> n = wordToNat (natToW 4 ^* bufSize).
    intros; subst.
    rewrite wordToNat_wmult.
    change (wordToNat (natToW 4)) with 4; omega.
    auto.
  Qed.

  Hint Immediate four_duh.

  Lemma inBounds_nil : forall n, inBounds n nil.
    intros; hnf; auto.
  Qed.

  Hint Immediate inBounds_nil.

  Lemma firstn_all : forall A (ls : list A) n,
    n = length ls
    -> firstn n ls = ls.
    intros; subst; induction ls; simpl; intuition.
  Qed.

  Hint Rewrite firstn_all using congruence : sepFormula.

  Ltac writeExps' :=
    try match goal with
          | [ H : ?E = _ |- match ?E with None => _ | _ => _ end ] =>
            rewrite H; post
        end;
    edestruct writeExps_correct; repeat rewrite Minus.minus_diag, Plus.plus_0_r in *;
      try match goal with
            | [ |- vcs _ ] => eauto
            | [ H : interp _ (Postcondition _ _), H' : _ |- _ ] => apply H' in H
          end; eauto; try rewrite Minus.minus_diag in *.

  Ltac writeExps :=
    match goal with
      | [ |- context[writeExps] ] => writeExps'
      | [ _ : context[writeExps] |- _ ] => writeExps'
    end.

  Lemma prove_freeable8 : forall p size,
    freeable p (wordToNat size)
    -> goodSize (4 * wordToNat size)
    -> freeable8 p (wordToNat (natToW 4 ^* size)).
    intros; rewrite wordToNat_wmult; change (wordToNat (natToW 4)) with 4; hnf; eauto.
  Qed.

  Hint Immediate prove_freeable8.

  Ltac i := abstract (try writeExps; t).

  Definition Insert : chunk.
    refine (WrapC Insert'
      invar
      invar
      InsertVcs
      _ _); abstract (wrap0; i).
  Defined.

End Insert.
