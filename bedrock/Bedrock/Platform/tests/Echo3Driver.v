Require Import Bedrock.Platform.tests.Thread0 Bedrock.Platform.tests.Echo3 Bedrock.Platform.Bootstrap.


Module Type S.
  Parameter heapSize : nat.
End S.

Module Make(M : S).
Import M.

Module M'.
  Definition globalSched : W := (heapSize + 50) * 4.
  Definition globalSock : W := globalSched ^+ $4.
End M'.

Import M'.

Module E := Echo3.Make(M').
Import E.

Section boot.
  Hypothesis heapSizeLowerBound : (3 <= heapSize)%nat.

  Definition size := heapSize + 50 + 2.

  Hypothesis mem_size : goodSize (size * 4)%nat.

  Let heapSizeUpperBound : goodSize (heapSize * 4).
    goodSize.
  Qed.

  Definition bootS := bootS heapSize 2.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "test"!"main" @ [E.mainS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%nat;;

        Assert [PREmain[_] globalSched =?> 2 * 0 =?> heapSize];;

        Call "malloc"!"init"(0, heapSize)
        [PREmain[_] globalSock =?> 1 * globalSched =?> 1 * mallocHeap 0];;

        Goto "test"!"main"
      end
    }}.

  Ltac t := unfold globalSched, localsInvariantMain, M'.globalSock, M'.globalSched; genesis.

  Theorem ok0 : moduleOk boot.
    vcgen; abstract t.
  Qed.

  Definition m1 := link boot E.T.m.
  Definition m := link E.m m1.

  Lemma ok1 : moduleOk m1.
    link ok0 E.T.ok.
  Qed.

  Theorem ok : moduleOk m.
    link E.ok ok1.
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

  Hypothesis mem_low : forall n, (n < size * 4)%nat -> st.(Mem) n <> None.
  Hypothesis mem_high : forall w, $ (size * 4) <= w -> st.(Mem) w = None.

  Theorem safe : sys_safe stn prog (w, st).
    safety ok.
  Qed.
End boot.

End Make.
