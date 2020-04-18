Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.tests.Thread0 Bedrock.Platform.tests.WebServer Bedrock.Platform.Bootstrap.


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


Module Type S.
  Parameter heapSize : N.
  Parameters port numWorkers : W.
End S.

Module Make(M : S).
Import M.

Module M'.
  Definition globalSched : W := ((heapSize + 50) * 4)%N.
  Definition globalSock : W := globalSched ^+ $4.
  Definition globalTree : W := globalSched ^+ $8.
  Definition globalPages : W := globalSched ^+ $12.

  Definition port := M.port.
  Definition numWorkers := M.numWorkers.

  Definition inbuf_size := 256.

  Theorem inbuf_size_lower : (inbuf_size >= 2)%nat.
    unfold inbuf_size; auto.
  Qed.

  Theorem inbuf_size_upper : (N_of_nat (inbuf_size * 4) < Npow2 32)%N.
    reflexivity.
  Qed.
End M'.

Import M'.

Module E := WebServer.Make(M').
Import E.

Section boot.
  Definition heapSize' := Hide.to_nat heapSize.

  Hypothesis heapSizeLowerBound : (3 <= heapSize)%N.

  Let heapSizeLowerBound' : (3 <= heapSize')%nat.
    intros; unfold heapSize'; rewrite Hide.to_nat_eq.
    assert (heapSize >= 3)%N by (apply N.le_ge; auto); nomega.
  Qed.

  Definition size := heapSize' + 50 + 3.

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
    Precondition := fun _ => st ~> Ex n, ![ 0 =?> (heapSize' + 50 + 3) * strings n globalPages ] st
  |}.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "web"!"main" @ [E.mainS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%N;;

        Assert [Al n, PREmain[_] 0 =?> heapSize' * globalSched =?> 3 * strings n globalPages ];;

        Call "malloc"!"init"(0, heapSize)
        [Al n, PREmain[_] globalSched =?> 1 * globalSock =?> 1 * globalTree =?> 1 * strings n globalPages
          * mallocHeap 0];;

        Goto "web"!"main"
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

  Ltac t := unfold globalSched, localsInvariantMain, M'.globalSock, M'.globalTree, M'.globalPages, M'.globalSched;
    genesis; rewrite natToW_plus; reflexivity.

  Theorem ok0 : moduleOk boot.
    unfold boot; rewrite <- Hide.heapSize4_eq; vcgen; abstract t.
  Qed.

  Global Opaque heapSize'.

  Definition m1 := link boot E.T.m.
  Definition m2 := link Buffers.m m1.
  Definition m3 := link E.MyIo.m m2.
  Definition m4 := link StringDb.m m3.
  Definition m := link E.m m4.

  Lemma ok1 : moduleOk m1.
    link ok0 E.T.ok.
  Qed.

  Lemma ok2 : moduleOk m2.
    link Buffers.ok ok1.
  Qed.

  Lemma ok3 : moduleOk m3.
    link E.MyIo.ok ok2.
  Qed.

  Lemma ok4 : moduleOk m4.
    link StringDb.ok ok3.
  Qed.

  Theorem ok : moduleOk m.
    link E.ok ok4.
  Qed.

  Variable stn : settings.
  Variable prog : program.

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
