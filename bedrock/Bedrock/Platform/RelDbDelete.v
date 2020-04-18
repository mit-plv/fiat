Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Wrap Bedrock.Platform.StringOps Bedrock.Platform.Malloc Bedrock.Platform.ArrayOps Bedrock.Platform.Buffers Bedrock.Platform.Bags.
Require Import Bedrock.Platform.SinglyLinkedList Bedrock.Platform.Buffers Bedrock.Platform.NumOps Bedrock.Platform.RelDb Bedrock.Platform.RelDbCondition.

Set Implicit Arguments.

Local Hint Extern 1 (@eq W _ _) => words.


(** * Iterating over matching rows of a table *)

Local Infix ";;" := SimpleSeq : SP_scope.
Opaque mult.

Section CompileEqualities.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.
  Variable tptr : W.
  Variable sch : schema.
  Variable data : string.
  Variable cond : condition.

  Notation EqVcs := (fun im ns res =>
    (~In "rp" ns)
    :: incl baseVars ns
    :: (res >= 10)%nat
    :: wfEqualities ns sch cond
    :: (forall a V V',
        (forall x, x <> "ibuf" ->
          x <> "ilen" ->
          x <> "tmp" ->
          x <> "ipos" ->
          x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x) ->
        invPre a V ===> invPre a V')
    :: (forall a V V' R,
        (forall x, x <> "ibuf" ->
          x <> "ilen" ->
          x <> "tmp" ->
          x <> "ipos" ->
          x <> "overflowed" -> x <> "matched" -> sel V x = sel V' x) ->
        invPost a V R = invPost a V' R)
    :: ("matched" <> data)%type
    :: (labl "array8" "equal") ~~ im ~~> (equalS)
    :: (data <> "rp")%type
    :: (data <> "ibuf")%type
    :: (data <> "ipos")%type
    :: (data <> "ilen")%type
    :: (data <> "tmp")%type
    :: In data ns
    :: goodSize (Datatypes.length sch)
    :: nil).

  Hint Immediate incl_refl.

  Definition CompileEqualities : chunk.
    refine (WrapC
      (compileEqualities invPre invPost sch data cond cond)
      (eqinv' invPre invPost sch data cond)
      (eqinv' invPre invPost sch data cond)
      EqVcs
      _ _); [ abstract (intros;
        repeat match goal with
                 | [ H : vcs (_ :: _) |- _ ] => inversion_clear H; subst
               end; eapply compileEqualities_post; try eassumption)
        | abstract (intros;
          repeat match goal with
                   | [ H : vcs (_ :: _) |- _ ] => inversion_clear H; subst
                 end; eapply compileEqualities_vcs; try eassumption; eauto) ].
  Defined.
End CompileEqualities.

Section Delete.
  Variable A : Type.
  Variable invPre : A -> vals -> HProp.
  Variable invPost : A -> vals -> W -> HProp.

  Variable tptr : W.
  Variable sch : schema.

  (* Store a pointer to the current linked list node and actual row data, respectively,
   * in these variables. *)
  Variables rw data : string.

  (* Test to use in filtering rows *)
  Variable cond : condition.

  Definition Delete' : chunk := (
    rw <-* tptr;;
    "res" <- 0;;

    [Al bs, Al a : A, Al done, Al remaining, Al head,
      PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
        * tptr =*> head * sll done (V "res") * sll remaining (V rw)
        * rows sch head done * rows sch head remaining * invPre a V * mallocHeap 0
      POST[R] array8 bs (V "buf") * invPost a V R]
    While (rw <> 0) {
      data <-* rw;;

      Assert [Al bs, Al a : A, Al done, Al remaining, Al head,
        PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
          * [| V rw <> 0 |] * tptr =*> head * sll done (V "res") * sll (V data :: remaining) (V rw)
          * rows sch head remaining * rows sch head done * row sch (V data) * invPre a V * mallocHeap 0
        POST[R] array8 bs (V "buf") * invPost a V R];;

      CompileEqualities
      (fun a V => invPre a V
        * Ex head, Ex done, Ex remaining,
          [| V rw <> 0 |] * tptr =*> head * sll done (V "res") * sll (V data :: remaining) (V rw)
          * rows sch head remaining * rows sch head done * mallocHeap 0)%Sep
      invPost
      sch data cond;;

      If ("matched" = 0) {
        (* No match.  This row survives. *)
        "matched" <- rw;;
        "tmp" <-* "matched" + 4;;
        "matched" + 4 *<- "res";;
        "res" <- "matched";;
        rw <- "tmp"
      } else {
        (* Match.  Delete this row. *)
        "tmp" <- rw;;
        rw <-* "tmp" + 4;;
        Call "malloc"!"free"(0, "tmp", 2)
        [Al bs, Al a : A, Al done, Al remaining, Al head,
          PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
            * tptr =*> head * sll done (V "res") * sll remaining (V rw)
            * rows sch head remaining * rows sch head done * row sch (V data) * invPre a V * mallocHeap 0
          POST[R] array8 bs (V "buf") * invPost a V R];;

        "matched" <- data;;
        "tmp" <-* "matched";;
        "matched" <-* "matched"+4;;

        "matched" <-- Call "numops"!"div4"("matched")
        [Al bs, Al a : A, Al done, Al remaining, Al head,
          PRE[V, R'] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
            * tptr =*> head * sll done (V "res") * sll remaining (V rw)
            * rows sch head remaining * rows sch head done * invPre a V * mallocHeap 0
            * Ex cols, Ex rbs,
            (V data ==*> V "tmp", R' ^* $4)
            * array (posl cols) (V data ^+ $8) * array (lenl cols) (V data ^+ $8 ^+ $ (length sch * 4))
            * array8 rbs (V "tmp")
            * [| length rbs = wordToNat R' * 4 |]%nat
            * [| length cols = length sch |] * [| inBounds (wordToNat R' * 4) cols |]%nat
            * [| V data <> 0 |] * [| freeable (V data) (2 + length sch + length sch) |]
            * [| V "tmp" <> 0 |] * [| freeable (V "tmp") (wordToNat R') |]
          POST[R] array8 bs (V "buf") * invPost a V R];;

        Call "buffers"!"bfree"("tmp", "matched")
        [Al bs, Al a : A, Al done, Al remaining, Al head,
          PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
            * tptr =*> head * sll done (V "res") * sll remaining (V rw)
            * rows sch head remaining * rows sch head done * invPre a V * mallocHeap 0
            * Ex cols,
            (V data ==*> V "tmp", V "matched" ^* $4)
            * array (posl cols) (V data ^+ $8) * array (lenl cols) (V data ^+ $8 ^+ $ (length sch * 4))
            * [| length cols = length sch |] * [| inBounds (wordToNat (V "matched") * 4) cols |]%nat
            * [| V data <> 0 |] * [| freeable (V data) (2 + length sch + length sch) |]
          POST[R] array8 bs (V "buf") * invPost a V R];;

        Call "malloc"!"free"(0, data, (2 + length sch + length sch)%nat)
        [Al bs, Al a : A, Al done, Al remaining, Al head,
          PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
            * tptr =*> head * sll done (V "res") * sll remaining (V rw)
            * rows sch head remaining * rows sch head done * invPre a V * mallocHeap 0
          POST[R] array8 bs (V "buf") * invPost a V R]
      }
    };;

    tptr *<- "res"
  )%SP.

  (* This is a clone of the normal 'platform' VC simplifier, but without the [delta]
   * rules for label map operations, which we can't resolve concretely when the imports
   * are a variable. *)
  Ltac vcgen_simp :=
    cbv beta iota zeta
      delta [map app imps Entry Blocks Postcondition VerifCond
        Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_ Structured.If_
        Structured.While_ Goto_ Structured.Call_ IGoto setArgs Reserved
        Formals Precondition importsMap fullImports buildLocals blocks union
        N.add N.succ Datatypes.length N.of_nat fold_left ascii_lt string_lt
        label'_lt LabelKey.compare' LabelKey.compare LabelKey.eq_dec
        toCmd Seq Instr Diverge Fail Skip Assert_ If_ While_
        Goto Call_ RvImm' Assign' localsInvariant localsInvariantCont regInL
        lvalIn immInR labelIn string_eq ascii_eq andb Bool.eqb
        qspecOut ICall_ Structured.ICall_ Assert_ Structured.Assert_
        string_dec Ascii.ascii_dec string_rec string_rect
        sumbool_rec sumbool_rect Ascii.ascii_rec Ascii.ascii_rect
        Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym fst
        snd labl Ascii.N_of_ascii Ascii.N_of_digits N.compare N.mul
        Pos.compare Pos.compare_cont Pos.mul Pos.add
        Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec
        ZArith_dec.Z_gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.max
        ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add
        Int.Z_as_Int._0 Int.Z_as_Int._2 BinInt.Z.max ZArith_dec.Zcompare_rec
        ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
        ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect COperand1 CTest
        COperand2 Pos.succ makeVcs Note_ Note__ IGotoStar_ IGotoStar
        AssertStar_ AssertStar Cond_ Cond
        Wrap WrapC CompileEqualities SimpleSeq].

  Definition dinvar :=
    Al bs, Al a : A,
    PRE[V] array8 bs (V "buf") * [| length bs = wordToNat (V "len") |] * [| inputOk V (exps cond) |]
      * table sch tptr * mallocHeap 0 * invPre a V
    POST[R] array8 bs (V "buf") * invPost a V R.

  Notation svars := (rw :: data :: nil).

  Definition noOverlapExp (e : exp) :=
    match e with
      | Const _ => True
      | Input pos len => pos <> rw /\ pos <> data /\ len <> rw /\ len <> data
        /\ pos <> "res" /\ len <> "res"
    end.

  Definition noOverlapExps := List.Forall noOverlapExp.

  Notation DeleteVcs := (fun im ns res =>
    (~In "rp" ns) :: incl svars ns :: (rw <> "rp")%type :: (data <> "rp")%type
    :: incl baseVars ns :: In "res" ns
    :: (rw <> data)%type
    :: (forall a V V', (forall x, x <> rw -> x <> data
      -> x <> "ibuf" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> x <> "matched"
      -> x <> "res" -> sel V x = sel V' x)
      -> invPre a V ===> invPre a V')
    :: (forall a V V' R, (forall x, x <> rw -> x <> data
      -> x <> "ibuf" -> x <> "ilen" -> x <> "tmp"
      -> x <> "ipos" -> x <> "overflowed" -> x <> "matched"
      -> x <> "res" -> sel V x = sel V' x)
      -> invPost a V R = invPost a V' R)
    :: "array8"!"equal" ~~ im ~~> ArrayOps.equalS
    :: "numops"!"div4" ~~ im ~~> div4S
    :: "malloc"!"free" ~~ im ~~> freeS
    :: "buffers"!"bfree" ~~ im ~~> bfreeS
    :: (res >= 10)%nat
    :: wfEqualities ns sch cond
    :: ("matched" <> rw)%type
    :: ("matched" <> data)%type
    :: (data <> "ibuf")%type
    :: (data <> "overflowed")%type
    :: (data <> "ipos")%type
    :: (data <> "ilen")%type
    :: (data <> "tmp")%type
    :: (data <> "len")%type
    :: (data <> "buf")%type
    :: (data <> "res")%type
    :: In data ns
    :: (rw <> "rp")%type
    :: (rw <> "ibuf")%type
    :: (rw <> "ipos")%type
    :: (rw <> "ilen")%type
    :: (rw <> "tmp")%type
    :: (rw <> "len")%type
    :: (rw <> "buf")%type
    :: (rw <> "overflowed")%type
    :: (rw <> "res")%type
    :: goodSize (length sch)
    :: goodSize (2 + length sch + length sch)
    :: noOverlapExps (exps cond)
    :: nil).

  Hint Immediate incl_refl.

  Theorem Forall_impl3 : forall A (P Q R S : A -> Prop) ls,
    List.Forall P ls
    -> List.Forall Q ls
    -> List.Forall R ls
    -> (forall x : A, P x -> Q x -> R x -> S x)
    -> List.Forall S ls.
    induction 1; inversion 1; inversion 1; auto.
  Qed.

  Theorem inputOk_weaken_params : forall ns V V' es,
    inputOk V es
    -> noOverlapExps es
    -> wfExps ns es
    -> (forall x, x <> rw -> x <> data -> sel V x = sel V' x)
    -> rw <> "len"
    -> data <> "len"
    -> inputOk V' es.
    intros; eapply Forall_impl3; [ apply H | apply H0 | apply H1 | ].
    intro e; destruct e; simpl; intuition idtac.
    repeat rewrite <- H2 by (simpl; congruence); assumption.
  Qed.

  Hint Extern 2 (inputOk _ _) => eapply inputOk_weaken_params; try eassumption;
    try (eapply wfEqualities_wfExps; eassumption); [ descend ].

  Lemma finish_rows : forall P sch head ls head',
    P * (rows sch head ls * rows sch head nil) ===> P * rows sch head' ls.
    sepLemma.
  Qed.

  Hint Extern 1 (himp _ _ _) => apply finish_rows.

  Lemma inputOk_weaken_delete : forall V V' es ns,
    inputOk V es
    -> wfExps ns es
    -> noOverlapExps es
    -> (forall x, x <> rw -> x <> "res" -> x <> "matched" -> x <> "tmp" -> sel V x = sel V' x)
    -> rw <> "len"
    -> inputOk V' es.
    induction 1; do 2 inversion_clear 1; subst; simpl; intuition; constructor; auto.
    destruct x; simpl in *; intuition idtac.
    repeat rewrite <- H1 by congruence; assumption.
  Qed.

  Hint Extern 1 (inputOk _ _) => eapply inputOk_weaken_delete; try eassumption;
    [ solve [ eauto 1 ] | solve [ descend ] ].

  Lemma four_shimmy : forall a b c,
    c = a
    -> c = 4 * b
    -> a = b * 4.
    intros; omega.
  Qed.

  Hint Immediate four_shimmy.

  Lemma derows : forall P Q P' sch head,
    P ===> P'
    -> P * Q ===> Q * (P' * rows sch head nil).
    sepLemma.
  Qed.
  Require Import Coq.Arith.Arith.

  Lemma row_free' : forall p n m,
    (p ^+ natToW 8) =?> n * (p ^+ natToW 8 ^+ natToW (n * 4)) =?> m
    ===> allocated p 8 (n + m).
    sepLemma.
    eapply Himp_trans; [ | apply allocated_join ].
    apply Himp_star_frame; apply allocated_shift_base; eauto.
    words.
    rewrite natToW_plus.
    rewrite (mult_comm 4).
    rewrite natToW_times4.
    rewrite natToW_times4.
    rewrite plus_0_r.
    words.
    omega.
    omega.
  Qed.

  Lemma row_free : forall p n m,
    (Ex ls1, Ex ls2, array ls1 (p ^+ natToW 8) * [| length ls1 = n |]
      * array ls2 (p ^+ natToW 8 ^+ natToW (n * 4)) * [| length ls2 = m |])
    ===> allocated p 8 (n + m).
    intros; eapply Himp_trans; [ | apply row_free' ].
    sepLemma; apply Himp_star_frame;
      (eapply Himp_trans; [ | apply MoreArrays.free_array' ]; sepLemma).
  Qed.

  Lemma rhints : TacPackage.
    prepare tt row_free.
  Defined.

  Hint Rewrite length_posl length_lenl : sepFormula.

  Hint Extern 1 (@eq nat _ _) => omega.

  Lemma inBounds_times4 : forall m w ls r,
    inBounds w ls
    -> m = wordToNat w
    -> m = 4 * r
    -> inBounds (natToW (r * 4)) ls.
    intros; subst.
    rewrite mult_comm in H1.
    apply (f_equal natToW) in H1.
    rewrite natToW_wordToNat in *; subst.
    auto.
  Qed.

  Hint Immediate inBounds_times4.

  Lemma div4_out : forall n w r,
    n = wordToNat w
    -> n = 4 * wordToNat r
    -> w = r ^* natToW 4.
    intros; subst.
    match goal with
      | [ |- ?x = ?y ] => assert (wordToNat x = wordToNat y)
    end.
    rewrite H0.
    rewrite wordToNat_wmult.
    apply mult_comm.
    apply goodSize_weaken with (wordToNat w).
    eauto.
    change (wordToNat (natToW 4)) with 4.
    omega.
    apply (f_equal natToW) in H.
    repeat rewrite natToW_wordToNat in H; assumption.
  Qed.

  Hint Immediate div4_out.

  Theorem Delete_post : forall im mn (H : importsGlobal im) ns res pre specs st,
    (forall (specs0 : codeSpec W (settings * state)) (st0 : settings * state),
      interp specs0 (pre st0)
      -> interp specs0 (dinvar true (fun x : W => x) ns res st0))
    -> vcs (DeleteVcs im ns res)
    -> interp specs (Postcondition (toCmd Delete' mn H ns res pre) st)
    -> interp specs (dinvar true (fun x : W => x) ns res st).
    simpl; wrap0; t.
  Qed.

  Theorem Delete_vcs : forall im mn (H : importsGlobal im) ns res pre,
    (forall (specs : codeSpec W (settings * state)) (st : settings * state),
      interp specs (pre st)
      -> interp specs (dinvar true (fun x : W => x) ns res st))
    -> vcs (DeleteVcs im ns res)
    -> vcs (VerifCond (toCmd Delete' mn H ns res pre)).
    intros.
    cbv beta in H1.
    repeat match goal with
             | [ H : vcs (_ :: _) |- _ ] => inversion H; clear H; subst
             | [ H : vcs nil |- _ ] => clear H
           end.
    unfold Delete'; vcgen_simp.
    match goal with
      | |- vcs ?Ps => apply (vcsImp_correct Ps)
    end; fold (@length B); fold (@length string); fold (@length (W * W)); intros; auto 1.

    v.
    v.

    pre.
    prep.
    evalu.
    my_descend.
    my_step.
    apply derows.
    weaken_invPre'.
    my_descend; my_step.
    repeat (my_descend; my_step).

    v.

    pre.

    prep.
    evalu.
    do 2 eexists; eexists (_ :: _).
    my_descend; repeat (my_descend; my_step).

    t.

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

    unfold labl in *.
    pre; prep; evalu; my_descend.
    my_descend; repeat (my_step; my_descend).
    my_descend; repeat (my_step; my_descend).
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.

    v.
    v.
    v.
    v.
    v.

    unfold labl in *.
    pre.
    prep.
    evalu.
    match goal with
      | [ H : freeable8 _ _ |- _ ] => destruct H; intuition idtac
    end.
    my_descend.
    my_step.
    eauto.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    auto.
    eauto.
    my_descend; my_step.
    replace (Regs x18 Rv ^* natToW 4) with x15.
    my_descend; my_step.
    my_descend; my_step.
    eauto.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.

    v.
    v.

    unfold labl in *.
    pre; prep; evalu; my_descend.
    my_step.
    eauto.
    my_step.
    my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.

    v.
    v.

    unfold labl in *.
    pre.
    prep.
    evalu.
    my_descend.
    my_step.
    auto.
    descend; step rhints.
    auto.
    auto.
    my_step.
    my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.
    my_descend; my_step.

    v.
    v.
  Qed.

  Hint Immediate Delete_post Delete_vcs.

  Definition Delete : chunk.
    refine (WrapC Delete'
      dinvar
      dinvar
      DeleteVcs
      _ _); abstract eauto.
  Defined.
End Delete.
