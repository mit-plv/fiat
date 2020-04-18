Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Bootstrap Bedrock.Platform.Malloc Bedrock.Platform.Buffers Bedrock.Platform.XmlLex Bedrock.Platform.XmlLang Bedrock.Platform.Arrays8 Bedrock.Platform.ArrayOps.
Require Import Bedrock.Platform.RelDb Bedrock.Platform.XmlOutput Bedrock.Platform.Bags Bedrock.Platform.Io Bedrock.Platform.Http Bedrock.Platform.HttpQ Bedrock.Platform.Thread.


Module Type HIDE.
  Parameter heapSize4 : N -> N.
  Axiom heapSize4_eq : forall n, heapSize4 n = (n * 4)%N.

  Parameter to_nat : N -> nat.
  Axiom to_nat_eq : to_nat = N.to_nat.
End HIDE.

Module Hide : HIDE.
  Definition heapSize4 n := (n * 4)%N.
  Theorem heapSize4_eq : forall n, heapSize4 n = (n * 4)%N.
    auto.
  Qed.

  Definition to_nat := N.to_nat.
  Theorem to_nat_eq : to_nat = N.to_nat.
    auto.
  Qed.
End Hide.

Record wf (ts : tables) (pr : program) (buf_size outbuf_size : N) : Prop := {
  WellFormed : XmlLang.wf ts pr;
  NotTooGreedy : (reserved pr <= 86)%nat;

  Buf_size_lower : (buf_size >= 2)%N;
  Buf_size_upper : (buf_size * 4 < Npow2 32)%N;

  Outbuf_size_lower : (outbuf_size >= 2)%N;
  Outbuf_size_upper : (outbuf_size * 4 < Npow2 32)%N;

  ND : NoDup (Names ts);
  GoodSchema : twfs ts;
  UF : uf ts
}.

Module Type S.
  Parameter ts : tables.
  Parameter pr : program.
  Parameters buf_size outbuf_size heapSize : N.

  Axiom Wf : wf ts pr buf_size outbuf_size.

  Parameters port numWorkers : W.
End S.

Module Make(M : S).
Import M.

Module Locations.
  Definition globalSched : W := ((heapSize + 50) * 4)%N.
  Definition globalSock : W := globalSched ^+ $4.
End Locations.

Import Locations.

Module M'''.
  Definition globalSched := globalSched.

  Local Open Scope Sep_scope.

  Definition globalInv (fs : files) : HProp :=
    db ts * Ex fr, globalSock =*> fr * [| fr %in fs |].
End M'''.

Module T := Thread.Make(M''').

Import T M'''.
Export T M'''.

Module MyM.
  Definition sched := sched.
  Definition globalInv := globalInv.

  Definition buf_size := outbuf_size.

  Theorem buf_size_lower : (nat_of_N buf_size >= 2)%nat.
    generalize (Outbuf_size_lower _ _ _ _ M.Wf).
    unfold buf_size; intros; nomega.
  Qed.

  Theorem buf_size_upper : goodSize (4 * nat_of_N buf_size).
    Transparent goodSize.
    unfold goodSize.
    rewrite Nat2N.inj_mul.
    rewrite Nmult_comm.
    rewrite N2Nat.id.
    eapply Outbuf_size_upper; apply M.Wf.
    Opaque goodSize.
  Qed.

  Theorem globalInv_monotone : forall fs fs', fs %<= fs'
    -> globalInv fs ===> globalInv fs'.
    unfold globalInv, M'''.globalInv; sepLemma.
  Qed.
End MyM.

Ltac unf := unfold MyM.sched, MyM.globalInv, M'''.globalSched, M'''.globalInv in *.

Module MyIo := Io.Make(MyM).
Module MyHttpQ := HttpQ.Make(MyM).
Module MyHttp := MyHttpQ.H.

Definition mainS := SPEC reserving 49
  PREmain[_] globalSched =?> 1 * globalSock =?> 1 * db ts * mallocHeap 0.

Definition handlerS := SPEC reserving 99
  Al fs,
  PREmain[_] sched fs * globalInv fs * mallocHeap 0.

Definition bsize := nat_of_N (buf_size * 4)%N.

Inductive unfold_here := UnfoldHere.
Local Hint Constructors unfold_here.

Import MyHttpQ.Httpq.

Theorem httpq_nil : Emp ===> httpq 0.
  eapply Himp_trans; [ | apply httpq_bwd ].
  apply Himp_ex_c; exists nil.
  sepLemma; step SinglyLinkedList.hints.
Qed.

Definition hints : TacPackage.
  prepare buffer_split_tagged (buffer_join_tagged, httpq_nil).
Defined.

Definition m0 := bimport [[ "buffers"!"bmalloc" @ [bmallocS], "sys"!"abort" @ [abortS],
                            "xml_prog"!"main" @ [XmlLang.mainS pr httpq ts],
                            "malloc"!"malloc" @ [mallocS],
                            "http"!"readRequest" @ [MyHttp.readRequestS],
                            "http"!"writeResponse" @ [MyHttp.writeResponseS],
                            "scheduler"!"init" @ [T.Q''.initS], "scheduler"!"listen" @ [T.Q''.listenS],
                            "scheduler"!"accept" @ [T.Q''.acceptS], "scheduler"!"close" @ [T.Q''.closeS],
                            "scheduler"!"spawn" @ [T.Q''.spawnS], "scheduler"!"exit" @ [T.Q''.exitS],
                            "httpq"!"send" @ [MyHttpQ.sendS] ]]
  bmodule "xml_driver" {{
    bfunctionNoRet "handler"("fr", "inbuf", "len", "outbuf", "q", "tmp", "tmp2") [handlerS]
      "inbuf" <-- Call "buffers"!"bmalloc"(buf_size)
      [Al fs, PREmain[_, R] sched fs * globalInv fs * R =?>8 bsize * mallocHeap 0];;

      "outbuf" <-- Call "buffers"!"bmalloc"(buf_size)
      [Al fs, PREmain[V, R] sched fs * globalInv fs * V "inbuf" =?>8 bsize * R =?>8 bsize * mallocHeap 0];;

      "q" <-- Call "malloc"!"malloc"(0, 2)
      [Al fs, PREmain[V, R] sched fs * globalInv fs * R =?> 2
        * V "inbuf" =?>8 bsize * V "outbuf" =?>8 bsize * mallocHeap 0];;

      [Al fs, PREmain[V] sched fs * globalInv fs * V "q" =?> 2
        * V "inbuf" =?>8 bsize * V "outbuf" =?>8 bsize * mallocHeap 0]
      While (1 = 1) {
        "fr" <-- Call "scheduler"!"accept"($[globalSock])
        [Al fs, PREmain[V, R] [| R %in fs |] * sched fs * globalInv fs * V "q" =?> 2
          * V "inbuf" =?>8 bsize * V "outbuf" =?>8 bsize * mallocHeap 0];;

        "len" <-- Call "http"!"readRequest"("fr", "inbuf", bsize)
        [Al fs, PREmain[V, R] [| V "fr" %in fs |] * sched fs * globalInv fs * V "q" =?> 2
          * V "inbuf" =?>8 bsize * V "outbuf" =?>8 bsize * mallocHeap 0];;

        If ("len" > bsize) {
          Call "sys"!"abort"()
          [PREonly[_] [| False |] ];;
          Fail
        } else {
          Assert [Al fs, PREmain[V] [| V "fr" %in fs |] * sched fs * globalInv fs * V "q" =?> 2
            * buffer_splitAt (wordToNat (V "len")) (V "inbuf") bsize
            * V "outbuf" =?>8 bsize * mallocHeap 0
            * [| wordToNat (V "len") <= bsize |]%nat ];;

          Assert [Al fs, PREmain[V] [| V "fr" %in fs |] * sched fs * globalInv fs * V "q" =?> 2
            * V "inbuf" =?>8 wordToNat (V "len")
            * (V "inbuf" ^+ natToW (wordToNat (V "len"))) =?>8 (bsize - wordToNat (V "len"))
            * V "outbuf" =?>8 bsize * mallocHeap 0 * [| wordToNat (V "len") <= bsize |]%nat ];;

          Note [unfold_here];;

          "q" *<- 0;;
          "tmp" <- "inbuf" + "len";;
          "tmp2" <- bsize - "len";;
          "tmp" <-- Call "xml_prog"!"main"("tmp", "tmp2", "outbuf", bsize, "q")
          [Al fs, Al q, PREmain[V, R] [| V "fr" %in fs |] * sched fs * globalInv fs
            * V "q" =*> q * (V "q" ^+ $4) =?> 1 * httpq q
            * V "inbuf" =?>8 wordToNat (V "len")
            * (V "inbuf" ^+ natToW (wordToNat (V "len"))) =?>8 (bsize - wordToNat (V "len"))
            * V "outbuf" =?>8 bsize
            * mallocHeap 0 * [| wordToNat (V "len") <= bsize |]%nat ];;

          Assert [Al fs, Al q, PREmain[V] [| V "fr" %in fs |] * sched fs * globalInv fs
            * V "q" =*> q * (V "q" ^+ $4) =?> 1 * httpq q
            * buffer_joinAt (wordToNat (V "len")) (V "inbuf") bsize
            * V "outbuf" =?>8 bsize * mallocHeap 0 ];;

          Assert [Al fs, Al q, PREmain[V] [| V "fr" %in fs |] * sched fs * globalInv fs
            * V "q" =*> q * (V "q" ^+ $4) =?> 1 * httpq q
            * V "inbuf" =?>8 bsize
            * V "outbuf" =?>8 bsize * mallocHeap 0 ];;

          Call "http"!"writeResponse"("fr", "outbuf", "tmp", bsize)
          [Al fs, Al q, PREmain[V] [| V "fr" %in fs |] * sched fs * globalInv fs
            * V "q" =*> q * (V "q" ^+ $4) =?> 1 * httpq q
            * V "inbuf" =?>8 bsize
            * V "outbuf" =?>8 bsize * mallocHeap 0 ];;

          "tmp" <-* "q";;
          Call "httpq"!"send"("tmp")
          [Al fs, PREmain[V] [| V "fr" %in fs |] * sched fs * globalInv fs
            * V "q" =?> 2
            * V "inbuf" =?>8 bsize
            * V "outbuf" =?>8 bsize * mallocHeap 0 ]
        };;

        Call "scheduler"!"close"("fr")
        [Al fs, PREmain[V] sched fs * globalInv fs * V "q" =?> 2
          * V "inbuf" =?>8 bsize * V "outbuf" =?>8 bsize * mallocHeap 0]
      }
    end with bfunctionNoRet "main"("fr", "x") [mainS]
      Init
      [Al fs, Al v, PREmain[_] sched fs * globalSock =*> v * db ts * mallocHeap 0];;

      "fr" <- 0;;
      [Al fs, PREmain[_] sched fs * globalSock =?> 1 * db ts * mallocHeap 0]
      While ("fr" < numWorkers) {
        Spawn("xml_driver"!"handler", 100)
        [Al fs, PREmain[_] sched fs * globalSock =?> 1 * db ts * mallocHeap 0];;
        "fr" <- "fr" + 1
      };;

      "fr" <-- Call "scheduler"!"listen"(port)
      [Al fs, Al v, PREmain[_, R] [| R %in fs |] * sched fs * globalSock =*> v
        * db ts * mallocHeap 0];;

      globalSock *<- "fr";;

      Exit 50
    end
  }}.

Lemma buf_size_lower'' : (buf_size < Npow2 32)%N.
  eapply Nlt_trans; [ | apply (Buf_size_upper _ _ _ _ Wf) ].
  specialize (Buf_size_lower _ _ _ _ Wf); intros.
  pre_nomega.
  rewrite N2Nat.inj_mul.
  simpl.
  generalize dependent (N.to_nat buf_size); intros.
  change (Pos.to_nat 2) with 2 in *.
  change (Pos.to_nat 4) with 4.
  omega.
Qed.

Lemma buf_size_lower' : natToW 2 <= NToW buf_size.
  unfold NToW.
  rewrite NToWord_nat.
  pre_nomega.
  rewrite wordToNat_natToWord_idempotent.
  generalize (Buf_size_lower _ _ _ _ Wf).
  intros; nomega.
  rewrite N2Nat.id.
  apply buf_size_lower''.
Qed.

Local Hint Immediate buf_size_lower'.

Close Scope Sep_scope.

Lemma bsize_in : (wordToNat (NToW buf_size) * 4) = bsize.
  unfold NToW, bsize.
  rewrite NToWord_nat.
  rewrite N2Nat.inj_mul.
  rewrite wordToNat_natToWord_idempotent.
  auto.
  rewrite N2Nat.id.
  apply buf_size_lower''.
Qed.

Lemma bsize_roundTrip : wordToNat (natToW bsize) = bsize.
  apply wordToNat_natToWord_idempotent.
  unfold bsize.
  rewrite N2Nat.id.
  apply (Buf_size_upper _ _ _ _ Wf).
Qed.

Hint Rewrite bsize_in bsize_roundTrip : sepFormula.
Hint Rewrite bsize_roundTrip : N.

Hint Extern 1 (_ ?X = 0) =>
  match type of X with
    | list ?A => equate X (@nil A); reflexivity
  end.

Lemma inBounds_nil : forall n, RelDb.inBounds n nil.
  constructor.
Qed.

Hint Immediate inBounds_nil.

Lemma freeable8_8 : forall p n,
  n = 8
  -> freeable p 2
  -> freeable8 p n.
  intros; subst; eexists; split; eauto; eauto.
Qed.

Hint Immediate freeable8_8.

Lemma arrays_begone : forall specs P p q,
  himp specs P (P * (array nil p * array nil q))%Sep.
  unfold array; sepLemma.
Qed.

Hint Immediate arrays_begone.

Lemma bsize_bound : forall w : W,
  w <= natToW bsize
  -> (wordToNat w <= bsize)%nat.
  intros.
  nomega.
Qed.

Hint Immediate bsize_bound.

Ltac t0 := sep unf hints; eauto.

Ltac t1 := unf; unfold localsInvariantMain; post; evaluate hints; descend;
  try match_locals; sep unf hints; eauto.

Ltac t :=
  try match goal with
        | [ |- context[unfold_here] ] => unfold buffer; generalize (NotTooGreedy _ _ _ _ Wf)
      end; try solve [ t0 ]; t1.

Ltac u := abstract t.

Theorem ok0 : moduleOk m0.
  vcgen; abstract t.
Qed.

Section boot.
  Definition heapSize' := Hide.to_nat heapSize.

  Hypothesis heapSizeLowerBound : (3 <= heapSize)%N.

  Let heapSizeLowerBound' : (3 <= heapSize')%nat.
    intros; unfold heapSize'; rewrite Hide.to_nat_eq.
    assert (heapSize >= 3)%N by (apply N.le_ge; apply heapSizeLowerBound); nomega.
  Qed.

  Definition size := heapSize' + 50 + 2 + length ts.

  Hypothesis mem_size : goodSize (size * 4)%nat.

  Let heapSizeUpperBound : goodSize (heapSize' * 4).
    goodSize.
  Qed.

  Lemma heapSizeLowerBound'' : natToW 3 <= NToW heapSize.
    hnf; intros.
    red in H.
    pre_nomega.
    rewrite wordToNat_natToWord_idempotent in H by reflexivity.
    unfold heapSize' in *.
    rewrite Hide.to_nat_eq in *.
    unfold NToW in *.
    rewrite NToWord_nat in *.
    rewrite wordToNat_natToWord_idempotent in H.
    omega.
    rewrite N2Nat.id.
    eapply goodSize_weaken in mem_size.
    2: instantiate (1 := N.to_nat heapSize); unfold size.
    Transparent goodSize.
    unfold goodSize in *.
    rewrite N2Nat.id in *.
    assumption.
    unfold heapSize'.
    rewrite Hide.to_nat_eq.
    omega.
  Qed.

  Hint Immediate heapSizeLowerBound''.

  Definition bootS := {|
    Reserved := 49;
    Formals := nil;
    Precondition := fun _ => st ~> ![ 0 =?> (heapSize' + 50 + 2) * db ts ] st
  |}.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "xml_driver"!"main" @ [mainS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%N;;

        Assert [PREmain[_] globalSched =?> 2 * 0 =?> heapSize' * db ts];;

        Call "malloc"!"init"(0, heapSize)
        [PREmain[_] globalSock =?> 1 * globalSched =?> 1 * mallocHeap 0 * db ts];;

        Goto "xml_driver"!"main"
      end
    }}.

  Lemma bootstrap_Sp_nonzero : forall sp : W,
    sp = 0
    -> sp = (heapSize' * 4)%nat
    -> goodSize (heapSize' * 4)
    -> False.
    intros; eapply bootstrap_Sp_nonzero; try eassumption; eauto.
  Qed.

  Lemma bootstrap_Sp_freeable : forall sp : W,
    sp = (heapSize' * 4)%nat
    -> freeable sp 50.
    intros; eapply bootstrap_Sp_freeable; try eassumption; eauto.
    instantiate (1 := 2).
    unfold size in mem_size.
    eapply goodSize_weaken; try apply mem_size.
    omega.
  Qed.

  Lemma noWrap : noWrapAround 4 (wordToNat (NToW heapSize) - 1).
    intros.
    unfold NToW; rewrite NToWord_nat by auto.
    unfold heapSize' in *; rewrite Hide.to_nat_eq in *.
    rewrite wordToNat_natToWord_idempotent.
    apply noWrap; eauto.
    eapply goodSize_weaken.
    2: instantiate (1 := (heapSize' * 4)%nat).
    unfold heapSize'; rewrite Hide.to_nat_eq; auto.
    unfold heapSize'; rewrite Hide.to_nat_eq; auto.
  Qed.

  Local Hint Immediate bootstrap_Sp_nonzero bootstrap_Sp_freeable noWrap.

  Lemma break : NToW ((heapSize + 50) * 4)%N = ((heapSize' + 50) * 4)%nat.
    intros.
    unfold NToW; rewrite NToWord_nat by auto.
    unfold heapSize'; rewrite N2Nat.inj_mul; auto.
    rewrite Hide.to_nat_eq; rewrite N2Nat.inj_add; auto.
  Qed.

  Lemma times4 : (Hide.heapSize4 heapSize : W) = (heapSize' * 4)%nat.
    rewrite Hide.heapSize4_eq; intros.
    unfold NToW; rewrite NToWord_nat by auto.
    unfold heapSize'; rewrite N2Nat.inj_mul; auto.
    rewrite Hide.to_nat_eq; auto.
  Qed.

  Lemma wordToNat_heapSize : wordToNat (NToW heapSize) = heapSize'.
    unfold heapSize'; rewrite Hide.to_nat_eq.
    unfold NToW.
    rewrite NToWord_nat.
    apply wordToNat_natToWord_idempotent.
    eapply goodSize_weaken.
    2: instantiate (1 := (heapSize' * 4)%nat).
    auto.
    unfold heapSize'; rewrite Hide.to_nat_eq; auto.
  Qed.

  Hint Rewrite break times4 wordToNat_heapSize : sepFormula.

  Lemma globalSched_plus4 :
    Locations.globalSched ^+ natToW 4 = natToW ((heapSize' + 50) * 4 + 4).
    unfold Locations.globalSched, heapSize'.
    rewrite wplus_alt; unfold wplusN, wordBinN.
    unfold NToW; rewrite NToWord_nat by auto.
    rewrite N2Nat.inj_mul; auto.
    rewrite Hide.to_nat_eq; rewrite N2Nat.inj_add; auto.
    change (wordToNat (natToW 4)) with 4.
    change (N.to_nat 4) with 4.
    rewrite wordToNat_natToWord_idempotent.
    reflexivity.
    eapply goodSize_weaken; try apply mem_size.
    unfold size, heapSize'.
    rewrite Hide.to_nat_eq.
    change (N.to_nat 50) with 50.
    omega.
  Qed.

  Hint Rewrite globalSched_plus4 : sepFormula.

  Ltac t := unfold M'''.globalSched, Locations.globalSched, Locations.globalSock, localsInvariantMain;
    genesis; rewrite natToW_plus; reflexivity.

  Theorem okb : moduleOk boot.
    unfold boot; rewrite <- Hide.heapSize4_eq; vcgen; abstract t.
  Qed.

  Global Opaque heapSize'.
  Hint Rewrite N2Nat.inj_mul : N.

  Lemma buf_size_upper' : goodSize (4 * wordToNat (NToWord 32 buf_size)).
    red.
    rewrite Nat2N.inj_mul.
    rewrite NToWord_nat.
    rewrite wordToNat_natToWord_idempotent.
    rewrite N2Nat.id.
    rewrite Nmult_comm.
    apply (Buf_size_upper _ _ _ _ Wf).
    rewrite N2Nat.id.
    clear; generalize (Buf_size_upper _ _ _ _ Wf).
    generalize (Npow2 32).
    intros; nomega.
  Qed.

  Definition m1 := link boot m0.
  Definition m2 := link Buffers.m m1.
  Definition m3 := link XmlLex.m m2.
  Definition m4 := link ArrayOps.m m3.
  Definition m5 := link NumOps.m m4.
  Definition m6 := link MyIo.m m5.
  Definition m7 := link MyHttp.m m6.
  Definition m8 := link MyHttpQ.m m7.
  Definition m9 := link T.m m8.

  Definition m := link (XmlLang.m _ httpq
    buf_size_lower' buf_size_upper'
    (WellFormed _ _ _ _ Wf) (ND _ _ _ _ Wf)
    (GoodSchema _ _ _ _ Wf)) m9.

  Lemma ok1 : moduleOk m1.
    link okb ok0.
  Qed.

  Lemma ok2 : moduleOk m2.
    link Buffers.ok ok1.
  Qed.

  Lemma ok3 : moduleOk m3.
    link XmlLex.ok ok2.
  Qed.

  Lemma ok4 : moduleOk m4.
    link ArrayOps.ok ok3.
  Qed.

  Lemma ok5 : moduleOk m5.
    link NumOps.ok ok4.
  Qed.

  Lemma ok6 : moduleOk m6.
    link MyIo.ok ok5.
  Qed.

  Lemma ok7 : moduleOk m7.
    link MyHttp.ok ok6.
  Qed.

  Lemma ok8 : moduleOk m8.
    link MyHttpQ.ok ok7.
  Qed.

  Lemma ok9 : moduleOk m9.
    link T.ok ok8.
  Qed.

  Lemma ok : moduleOk m.
    link (XmlLang.ok _ httpq buf_size_lower' buf_size_upper' (WellFormed _ _ _ _ Wf)) ok9;
    apply (UF _ _ _ _ Wf).
  Qed.

  Variable stn : settings.
  Variable prog : IL.program.

  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl,
    LabelMap.MapsTo l (pre, bl) (XCAP.Blocks m)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis agreeImp : forall l pre, LabelMap.MapsTo l pre (XCAP.Imports m)
    -> exists w, Labels stn l = Some w
      /\ prog w = None.

  Hypothesis omitImp : forall l w,
    Labels stn ("sys", l) = Some w
    -> prog w = None.

  Variable w : W.
  Hypothesis at_start : Labels stn ("main", Global "main") = Some w.

  Variable st : state.

  Hypothesis prec : forall specs, interp specs (Precondition bootS None (stn, st)).

  Import Safety.

  Theorem safe : sys_safe stn prog (w, st).
    eapply safety; try eassumption; [
      link_simp; unfold labelSys, labelSys'; simpl; tauto
      | apply ok
      | apply LabelMap.find_2; link_simp; reflexivity
      | auto ].
  Qed.
End boot.

End Make.
