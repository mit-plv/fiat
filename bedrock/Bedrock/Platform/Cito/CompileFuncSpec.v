Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.Inv.
  Module Import InvMake := Make E.
  Module Import InvMake2 := Make M.

  Require Import Bedrock.Platform.Cito.SyntaxFunc.
  Require Import Coq.Strings.String.
  Require Import Bedrock.Platform.Malloc.

  Section TopSection.

    Variable func : FuncCore.

    Definition spec_without_funcs_ok fs : assert :=
      st ~> ExX, internal_spec _ fs func st.

    Definition spec : assert :=
      st ~> Ex fs,
      let stn := fst st in
      funcs_ok stn fs /\
      spec_without_funcs_ok fs st.

    Definition imply (pre new_pre: assert) := forall specs x, interp specs (pre x) -> interp specs (new_pre x).

    Definition verifCond pre := imply pre spec :: nil.

  End TopSection.

End Make.
