Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.MakeWrapper Bedrock.Platform.Cito.examples.ExampleADT Bedrock.Platform.Cito.examples.ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.


Definition f := (
  cfunction "return_zero"()
    "ret" <- $0
  end
)%Citofuncs.

Definition m := cmodule "return_zero" {{
  f
}}.

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Definition fspec :=
  cimport "return_zero"!"return_zero"
  cmodules [[ gm ]]
  definition f.

Notation extra_stack := 10.

Definition topS := SPEC reserving (3 + extra_stack)
  PREonly[_] mallocHeap 0.

Definition top := bimport [[ ("return_zero"!"return_zero", fspec), "sys"!"printInt" @ [printIntS],
                             "sys"!"abort" @ [abortS] ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "return_zero"!"return_zero"(extra_stack)
      [PREonly[_, R] [| R = 0 |] ];;

      Call "sys"!"printInt"("R")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Lemma body_safe : forall env v, Safe env (Body f) v.
  econstructor; eauto.
Qed.

Lemma body_runsto : forall env v v', RunsTo env (Body f) v v'
  -> sel (fst v') (RetVar f) = 0 /\ snd v' = snd v.
  intros.
  inversion_clear H.
  subst vs.
  simpl.
  split.
  apply sel_upd_eq; auto.
  auto.
Qed.
Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.

Theorem top_ok : moduleOk top.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.

  post.
  call_cito 10 (@nil string).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  eapply CompileExprs.change_hyp; [ |
    change (@nil W) with (toArray nil (upd x2 "extra_stack" 10)); apply is_state_in' ].
  autorewrite with sepFormula.
  clear H7.
  hiding ltac:(step auto_ext).
  apply body_safe.
  hiding ltac:(step auto_ext).
  repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
  apply swap; apply injL; intro.
  openhyp.
  match goal with
    | [ x : State |- _ ] => destruct x; simpl in *
  end.
  apply body_runsto in H8; simpl in H8; intuition subst.
  eapply replace_imp.
  change 10 with (wordToNat (sel (upd x2 "extra_stack" 10) "extra_stack")).
  apply is_state_out'.
  clear H7.
  hiding ltac:(step auto_ext).
  hiding ltac:(step auto_ext).

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
Qed.

Definition all := link top (compile_to_bedrock (gm :: nil) (empty _)).

Theorem all_ok : moduleOk all.
  link0 top_ok.
Qed.
