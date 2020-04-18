Require Import Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Malloc Bedrock.Platform.Cito.examples.Cell.


Module Type ADT.
  Parameter cell : W -> W -> HProp.

  Axiom cell_fwd : forall n c, cell n c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex junk, c ==*> n, junk.
  Axiom cell_bwd : forall n (c : W), [| c <> 0 |] * [| freeable c 2 |]
    * (Ex junk, c ==*> n, junk) ===> cell n c.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Definition cell (n c : W) : HProp :=
    [| c <> 0 |] * [| freeable c 2 |]
    * Ex junk, c ==*> n, junk.

  Theorem cell_fwd : forall n c, cell n c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex junk, c ==*> n, junk.
    unfold cell; sepLemma.
  Qed.

  Theorem cell_bwd : forall n (c : W), [| c <> 0 |] * [| freeable c 2 |]
    * (Ex junk, c ==*> n, junk) ===> cell n c.
    unfold cell; sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare cell_fwd cell_bwd.
Defined.

Definition newS := newS cell 8.
Definition deleteS := deleteS cell 6.
Definition readS := readS cell 0.
Definition writeS := writeS cell 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "SimpleCell" {{
    bfunction "new"("extra_stack", "x") [newS]
      "x" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[_, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] * mallocHeap 0
       POST[R'] cell 0 R' * mallocHeap 0];;

      "x" *<- 0;;
      Return "x"
    end

    with bfunction "delete"("extra_stack", "self") [deleteS]
      Call "malloc"!"free"(0, "self", 2)
      [PRE[_] Emp
       POST[_] Emp];;

      Return 0
    end

    with bfunction "read"("extra_stack", "self") [readS]
      "self" <-* "self";;
      Return "self"
    end

    with bfunction "write"("extra_stack", "self", "n") [writeS]
      "self" *<- "n";;
      Return 0
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Theorem ok : moduleOk m.
  vcgen; abstract (sep hints; eauto).
Qed.
