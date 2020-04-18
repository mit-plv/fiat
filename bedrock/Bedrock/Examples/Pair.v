Require Import Bedrock.Examples.AutoSep.

(** A very basic abstract predicate: pairs of words *)

Module Type PAIR.
  Parameter pair : W -> W -> W -> HProp.

  Axiom pair_extensional : forall a b p, HProp_extensional (pair a b p).

  Axiom pair_fwd : forall a b p,
    pair a b p ===> p =*> a * (p ^+ $4) =*> b.

  Axiom pair_bwd : forall a b p,
    p =*> a * (p ^+ $4) =*> b ===> pair a b p.
End PAIR.

Module Pair : PAIR.
  Open Scope Sep_scope.

  Definition pair (a b p : W) : HProp :=
    p =*> a * (p ^+ $4) =*> b.

  Theorem pair_extensional : forall a b p, HProp_extensional (pair a b p).
    reflexivity.
  Qed.

  Theorem pair_fwd : forall a b p,
    pair a b p ===> p =*> a * (p ^+ $4) =*> b.
    unfold pair; sepLemma.
  Qed.

  Theorem pair_bwd : forall a b p,
    p =*> a * (p ^+ $4) =*> b ===> pair a b p.
    unfold pair; sepLemma.
  Qed.
End Pair.

Import Pair.
Hint Immediate pair_extensional.

Definition firstS : spec := SPEC("p") reserving 0
  Al a, Al b,
  PRE[V] pair a b (V "p")
  POST[R] [| R = a |] * pair a b (V "p").

Definition updSecondS : spec := SPEC("p", "x") reserving 0
  Al a, Al b,
  PRE[V] pair a b (V "p")
  POST[_] pair a (V "x") (V "p").

Definition pair := bmodule "pair" {{
  bfunction "first"("p") [firstS]
    "p" <-* "p";;
    Return "p"
  end with bfunction "second"("p", "x") [updSecondS]
    "p" <- "p" + 4;;
    "p" *<- "x";;
    Return 0
  end
}}.

(*TIME Clear Timing Profile. *)

Definition hints : TacPackage.
  (*TIME idtac "pair:prepare". Time *)
  prepare pair_fwd pair_bwd.
Defined.

Theorem pairOk : moduleOk pair.
  (*TIME idtac "pair:verify". Time *)
  vcgen; abstract sep hints.
Qed.

(*TIME Print Timing Profile. *)
