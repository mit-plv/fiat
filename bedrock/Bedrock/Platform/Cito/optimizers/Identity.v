Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.GoodOptimizer.

Definition id_opt : Optimizer := fun s _ => s.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Module Import GoodOptimizerMake := GoodOptimizer.Make E.
  Require Import Bedrock.Platform.Cito.Semantics.
  Import Semantics.

  Lemma id_opt_good : GoodOptimizer id_opt.
    unfold GoodOptimizer.

    split.
    unfold PreserveRunsTo.
    intros.
    unfold id_opt in *.
    destruct v'; simpl in *.
    eexists.
    split; eauto.

    split.
    unfold PreserveSafe.
    intros.
    unfold id_opt in *.
    eauto.

    split.
    unfold PreserveGoodSize.
    intros.
    unfold id_opt in *.
    eauto.

    unfold PreserveSynReq.
    intros.
    unfold id_opt in *.
    eauto.
  Qed.

End Make.
