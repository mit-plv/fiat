Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc Bedrock.Platform.Bootstrap Bedrock.Platform.Cito.examples.CountUnique.


Module Type S.
  Parameter heapSize : nat.
End S.

Module Make(M : S).
Import M.

Section boot.
  Hypothesis heapSizeLowerBound : (3 <= heapSize)%nat.

  Definition size := heapSize + 50 + 0.

  Hypothesis mem_size : goodSize (size * 4)%nat.

  Let heapSizeUpperBound : goodSize (heapSize * 4).
    goodSize.
  Qed.

  Definition bootS := bootS heapSize 0.

  Definition boot := bimport [[ "malloc"!"init" @ [Malloc.initS], "top"!"top" @ [topS] ]]
    bmodule "main" {{
      bfunctionNoRet "main"() [bootS]
        Sp <- (heapSize * 4)%nat;;

        Assert [PREonly[_] 0 =?> heapSize];;

        Call "malloc"!"init"(0, heapSize)
        [PREonly[_] mallocHeap 0];;

        Call "top"!"top"()
        [PREonly[_] [| False |] ]
      end
    }}.

  Theorem ok : moduleOk boot.
    vcgen; abstract genesis.
  Qed.

  Require Bedrock.Platform.Cito.examples.ExampleImpl.

  Definition m0 := link ExampleImpl.m boot.
  Definition m1 := link all m0.

  Lemma ok0 : moduleOk m0.
    link ExampleImpl.ok ok.
  Qed.

  Lemma ok1 : moduleOk m1.
    link all_ok ok0.
  Qed.

  Variable stn : settings.
  Variable prog : program.

  Hypothesis inj : forall l1 l2 w, Labels stn l1 = Some w
    -> Labels stn l2 = Some w
    -> l1 = l2.

  Hypothesis agree : forall l pre bl,
    LabelMap.MapsTo l (pre, bl) (XCAP.Blocks m1)
    -> exists w, Labels stn l = Some w
      /\ prog w = Some bl.

  Hypothesis agreeImp : forall l pre, LabelMap.MapsTo l pre (XCAP.Imports m1)
    -> exists w, Labels stn l = Some w
      /\ prog w = None.

  Hypothesis omitImp : forall l w,
    Labels stn ("sys", l) = Some w
    -> prog w = None.

  Variable w : W.
  Hypothesis at_start : Labels stn ("main", Global "main") = Some w.

  Variable st : state.

  Hypothesis mem_low : forall n, (n < size * 4)%nat -> st.(Mem) n <> None.
  Hypothesis mem_high : forall w, ($ (size * 4) <= w)%word -> st.(Mem) w = None.

  Theorem safe : sys_safe stn prog (w, st).
    safety ok1.
  Qed.
End boot.

End Make.
