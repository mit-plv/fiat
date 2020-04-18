Require Import Bedrock.Examples.AutoSep Bedrock.Examples.Malloc Bedrock.Examples.Sets.

Set Implicit Arguments.


Local Hint Extern 3 (himp _ _ _) => apply himp_star_frame.
Local Hint Extern 3 (himp _ _ _) => apply himp_star_frame_comm.

Module Type USL. (* For "unsorted list" *)
  Parameter usl' : set -> nat -> W -> HProp.
  Parameter usl : set -> W -> HProp.

  Axiom usl'_extensional : forall s n p, HProp_extensional (usl' s n p).
  Axiom usl_extensional : forall s p, HProp_extensional (usl s p).

  Axiom usl'_set_extensional : forall n s s' p, s %= s' -> usl' s n p ===> usl' s' n p.

  Axiom usl_fwd : forall s p, usl s p ===> [| freeable p 2 |]
    * Ex n, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * usl' s n r.
  Axiom usl_bwd : forall s p, ([| freeable p 2 |]
    * Ex n, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * usl' s n r) ===> usl s p.

  Axiom nil_fwd : forall s n (p : W), p = 0 -> usl' s n p ===> [| s %= empty /\ n = O |].
  Axiom nil_bwd : forall s n (p : W), p = 0 -> [| s %= empty /\ n = O |] ===> usl' s n p.

  Axiom cons_fwd : forall s n (p : W), p <> 0 -> usl' s n p ===>
    Ex n', Ex v, Ex p', (p ==*> v, p') * usl' (s %- v) n' p'
    * [| freeable p 2 /\ n = S n' /\ v %in s |].

  Axiom cons_bwd : forall s n (p : W), p <> 0 ->
    (Ex n', Ex v, Ex p', (p ==*> v, p') * usl' (s %- v) n' p'
      * [| freeable p 2 /\ n = S n' /\ v %in s |]) ===> usl' s n p.
End USL.

Module Usl : USL.
  Open Scope Sep_scope.

  Fixpoint usl' (s : set) (n : nat) (p : W) : HProp :=
    match n with
      | O => [| p = 0 /\ s %= empty |]
      | S n' => [| p <> 0 /\ freeable p 2 |] * Ex v, Ex p', (p ==*> v, p')
        * usl' (s %- v) n' p' * [| v %in s |]
    end.

  Definition usl (s : set) (p : W) := [| freeable p 2 |]
    * Ex n, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * usl' s n r.

  Theorem usl'_extensional : forall s n p, HProp_extensional (usl' s n p).
    destruct n; reflexivity.
  Qed.

  Theorem usl_extensional : forall s p, HProp_extensional (usl s p).
    reflexivity.
  Qed.

  Theorem usl'_set_extensional : forall n s s' p, s %= s' -> usl' s n p ===> usl' s' n p.
    induction n; sepLemma.
  Qed.

  Theorem usl_fwd : forall s p, usl s p ===> [| freeable p 2 |]
    * Ex n, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * usl' s n r.
    unfold usl; sepLemma.
  Qed.

  Theorem usl_bwd : forall s p, ([| freeable p 2 |]
    * Ex n, Ex r, Ex junk, p =*> r * (p ^+ $4) =*> junk * usl' s n r) ===> usl s p.
    unfold usl; sepLemma.
  Qed.

  Theorem nil_fwd : forall s n (p : W), p = 0 -> usl' s n p ===> [| s %= empty /\ n = O |].
    destruct n; sepLemma.
  Qed.

  Theorem nil_bwd : forall s n (p : W), p = 0 -> [| s %= empty /\ n = O |] ===> usl' s n p.
    destruct n; sepLemma.
  Qed.

  Theorem cons_fwd : forall s n (p : W), p <> 0 -> usl' s n p ===>
    Ex n', Ex v, Ex p', (p ==*> v, p') * usl' (s %- v) n' p'
    * [| freeable p 2 /\ n = S n' /\ v %in s |].
    destruct n; sepLemma.
  Qed.

  Theorem cons_bwd : forall s n (p : W), p <> 0 ->
    (Ex n', Ex v, Ex p', (p ==*> v, p') * usl' (s %- v) n' p'
      * [| freeable p 2 /\ n = S n' /\ v %in s |]) ===> usl' s n p.
    destruct n; sepLemma;
      match goal with
        | [ H : S _ = S _ |- _ ] => injection H; sepLemma
      end.
  Qed.
End Usl.

Import Usl.
Export Usl.
Hint Immediate usl_extensional usl'_extensional.

(*TIME Clear Timing Profile. *)

Definition hints : TacPackage.
(*TIME idtac "tree-set:prepare1". Time *)
  prepare (usl_fwd, nil_fwd, cons_fwd) (usl_bwd, nil_bwd, cons_bwd).
(*TIME Time *)Defined.

Definition initS := initS usl 7.
Definition lookupS := lookupS usl 1.
Definition addS := addS usl 8.
Definition removeS := removeS usl 6.

Definition uslM := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "usl" {{
  bfunction "init"("r") [initS]
    "r" <-- Call "malloc"!"malloc"(0)
    [PRE[_, R] R =?> 2 * [| freeable R 2 |]
     POST[R'] [| R' = R |] * usl empty R ];;
    "r" *<- 0;;
    Return "r"
  end with bfunction "lookup"("s", "k", "tmp") [lookupS]
    "s" <-* "s";;

    [Al s, Al n,
      PRE[V] usl' s n (V "s")
      POST[R] [| (V "k" %in s) \is R |] * usl' s n (V "s")]
    While ("s" <> 0) {
      "tmp" <-* "s";;
      If ("tmp" = "k") {
        Return 1
      } else {
        "s" <- "s" + 4;;
        "s" <-* "s"
      }
    };;

    Return 0
  end with bfunction "add"("s", "k", "tmp", "tmp2") [addS]
    "tmp" <-- Call "usl"!"lookup"("s", "k")
    [Al s,
      PRE[V, R] [| (V "k" %in s) \is R |] * usl s (V "s") * mallocHeap
      POST[R'] usl (s %+ V "k") (V "s") * mallocHeap];;

    If ("tmp" = 1) {
      Return 0
    } else {
      "tmp" <-- Call "malloc"!"malloc"(0)
      [Al p,
        PRE[V, R] V "s" =*> p * R =?> 2
        POST[_] V "s" =*> R * (R ==*> V "k", p) ];;

      "tmp" *<- "k";;
      "k" <- "tmp" + 4;;
      "tmp2" <-* "s";;
      "k" *<- "tmp2";;
      "s" *<- "tmp";;
      Return 0
    }
  end with bfunction "remove"("s", "k", "prev", "tmp") [removeS]
    "prev" <- "s";;
    "s" <-* "prev";;

    [Al s, Al n,
      PRE[V] V "prev" =*> V "s" * usl' s n (V "s") * mallocHeap
      POST[R] Ex p, Ex n', V "prev" =*> p * usl' (s %- V "k") n' p * mallocHeap]
    While ("s" <> 0) {
      "tmp" <-* "s";;
      If ("tmp" = "k") {
        "tmp" <- "s" + 4;;
        "tmp" <-* "tmp";;
        "prev" *<- "tmp";;

        Call "malloc"!"free"("s", 0)
        [PRE[_] Emp
         POST[_] Emp];;
        Return 0
      } else {
        "prev" <- "s" + 4;;
        "s" <-* "prev"
      }
    };;

    Return 0
  end
}}.

Local Hint Extern 5 (@eq W _ _) => words.
Local Hint Extern 3 (himp _ _ _) => apply usl'_set_extensional.

Lemma contradictory_membership : forall (s : set) v x,
  x = natToW 1
  -> x = natToW 0
  -> s v.
  intros; subst; discriminate.
Qed.

Hint Extern 1 => eapply contradictory_membership; eassumption.

Theorem uslMOk : moduleOk uslM.
(*TIME idtac "tree-set:verify". Time *)
  vcgen; abstract (sep hints; auto).
(*TIME Time *)Qed.

(*TIME Print Timing Profile. *)
