Require Import Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Malloc Bedrock.Platform.Cito.examples.FiniteSet.


Infix "===" := WordSet.Equal.

Module Type ADT.
  Parameter lset : WordSet.t -> W -> HProp.
  Parameter lset' : WordSet.t -> nat -> W -> HProp.

  Axiom lset_fwd : forall s c, lset s c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * Ex n, lset' s n p.
  Axiom lset_bwd : forall s (c : W), ([| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * Ex n, lset' s n p) ===> lset s c.

  Axiom lset'_empty_fwd : forall s n (c : W), c = 0
    -> lset' s n c
    ===> [| n = O |] * [| s === WordSet.empty |].

  Axiom lset'_empty_bwd : forall s n (c : W), c = 0
    -> [| n = O |] * [| s === WordSet.empty |] ===> lset' s n c.

  Axiom lset'_nonempty_fwd : forall s n (c : W), c <> 0
    -> lset' s n c
    ===> Ex n', [| n = S n' |] * [| freeable c 2 |] * Ex x, [| WordSet.In x s |] * Ex p', (c ==*> x, p')
        * lset' (WordSet.remove x s) n' p'.

  Axiom lset'_nonempty_bwd : forall s n (c : W), c <> 0
    -> (Ex n', [| n = S n' |] * [| freeable c 2 |] * Ex x, [| WordSet.In x s |] * Ex p', (c ==*> x, p')
        * lset' (WordSet.remove x s) n' p') ===> lset' s n c.

  Axiom lset'_monotone : forall n s s' p, s === s'
    -> lset' s n p ===> lset' s' n p.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint lset' (s : WordSet.t) (n : nat) (p : W) : HProp :=
    match n with
      | O => [| p = 0 |] * [| s === WordSet.empty |]
      | S n' => [| p <> 0 |] * [| freeable p 2 |]
        * Ex x, [| WordSet.In x s |] * Ex p', (p ==*> x, p')
        * lset' (WordSet.remove x s) n' p'
    end.

  Definition lset (s : WordSet.t) (c : W) : HProp :=
    [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * Ex n, lset' s n p.

  Theorem lset_fwd : forall s c, lset s c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * Ex n, lset' s n p.
    unfold lset; sepLemma.
  Qed.

  Theorem lset_bwd : forall s (c : W), ([| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * Ex n, lset' s n p) ===> lset s c.
    unfold lset; sepLemma.
  Qed.

  Theorem lset'_empty_fwd : forall s n (c : W), c = 0
    -> lset' s n c
    ===> [| n = O |] * [| s === WordSet.empty |].
    destruct n; sepLemma.
  Qed.

  Theorem lset'_empty_bwd : forall s n (c : W), c = 0
    -> [| n = O |] * [| s === WordSet.empty |] ===> lset' s n c.
    destruct n; sepLemma.
  Qed.

  Theorem lset'_nonempty_fwd : forall s n (c : W), c <> 0
    -> lset' s n c
    ===> Ex n', [| n = S n' |] * [| freeable c 2 |] * Ex x, [| WordSet.In x s |] * Ex p', (c ==*> x, p')
        * lset' (WordSet.remove x s) n' p'.
    destruct n; sepLemma.
  Qed.

  Theorem lset'_nonempty_bwd : forall s n (c : W), c <> 0
    -> (Ex n', [| n = S n' |] * [| freeable c 2 |] * Ex x, [| WordSet.In x s |] * Ex p', (c ==*> x, p')
        * lset' (WordSet.remove x s) n' p') ===> lset' s n c.
    destruct n; sepLemma.
    injection H0; sepLemma.
  Qed.

  Theorem lset'_monotone : forall n s s' p, s === s'
    -> lset' s n p ===> lset' s' n p.
    induction n; sepLemma.
    unfold WordSet.Equal in *; firstorder.
    apply H; auto.
    apply IHn.
    hnf; intuition; apply WordSet.remove_spec; apply WordSet.remove_spec in H3; intuition.
    apply H; auto.
    apply H; auto.
  Qed.
End Adt.

Import Adt.
Export Adt.

(* Hm... to avoid stack overflow, need to rebind these! *)
Definition lset'_empty_fwd : forall s n (c : W), c = 0
  -> lset' s n c
  ===> [| n = O |] * [| s === WordSet.empty |] := lset'_empty_fwd.

Definition lset'_empty_bwd : forall s n (c : W), c = 0
  -> [| n = O |] * [| s === WordSet.empty |] ===> lset' s n c := lset'_empty_bwd.

Definition hints : TacPackage.
  prepare (lset_fwd, lset'_empty_fwd, lset'_nonempty_fwd)
  (lset_bwd, lset'_empty_bwd, lset'_nonempty_bwd).
Defined.

Definition newS := newS lset 8.
Definition deleteS := deleteS lset 7.
Definition memS := memS lset 1.
Definition addS := addS lset 9.
Definition sizeS := sizeS lset 1.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "ListSet" {{
    bfunction "new"("extra_stack", "x") [newS]
      "x" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[_, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] * mallocHeap 0
       POST[R'] lset WordSet.empty R' * mallocHeap 0];;

      "x" *<- 0;;
      Return "x"
    end

    with bfunction "delete"("extra_stack", "self", "ls") [deleteS]
      "ls" <-* "self";;

      Call "malloc"!"free"(0, "self", 2)
      [Al s, Al n,
        PRE[V] lset' s n (V "ls") * mallocHeap 0
        POST[_] mallocHeap 0];;

      [Al s, Al n,
        PRE[V] lset' s n (V "ls") * mallocHeap 0
        POST[_] mallocHeap 0]
      While ("ls" <> 0) {
        "self" <-* "ls"+4;;
        Call "malloc"!"free"(0, "ls", 2)
        [Al s, Al n,
          PRE[V] lset' s n (V "self") * mallocHeap 0
          POST[_] mallocHeap 0];;

        "ls" <- "self"
      };;

      Return 0
    end

    with bfunction "mem"("extra_stack", "self", "n", "tmp") [memS]
      "self" <-* "self";;

      [Al s, Al n,
        PRE[V] lset' s n (V "self")
        POST[R] lset' s n (V "self") * [| R = WordSet.mem (V "n") s |] ]
      While ("self" <> 0) {
        "tmp" <-* "self";;

        If ("tmp" = "n") {
          Return 1
        } else {
          "self" <-* "self"+4
        }
      };;

      Return 0
    end

    with bfunction "add"("extra_stack", "self", "n", "tmp") [addS]
      "tmp" <-- Call "ListSet"!"mem"("extra_stack", "self", "n")
      [Al s,
        PRE[V, R] [| R = WordSet.mem (V "n") s |] * lset s (V "self") * mallocHeap 0
        POST[_] lset (WordSet.add (V "n") s) (V "self") * mallocHeap 0];;

      If ("tmp" = 1) {
        Return 0
      } else {
        "tmp" <-- Call "malloc"!"malloc"(0, 2)
        [Al s,
          PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
            * [| ~WordSet.In (V "n") s |] * lset s (V "self")
          POST[_] lset (WordSet.add (V "n") s) (V "self")];;

        "tmp" *<- "n";;
        "n" <-* "self";;
        "tmp"+4 *<- "n";;
        "self" *<- "tmp";;
        Return 0
      }
    end

    with bfunction "size"("extra_stack", "self", "acc") [sizeS]
      "self" <-* "self";;
      "acc" <- 0;;

      [Al s, Al n,
        PRE[V] lset' s n (V "self")
        POST[R] lset' s n (V "self") * [| R = natToW (WordSet.cardinal s) ^+ V "acc" |] ]
      While ("self" <> 0) {
        "acc" <- "acc" + 1;;
        "self" <-* "self"+4
      };;

      Return "acc"
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma Equal_refl : forall s, s === s.
  intros; hnf; tauto.
Qed.

Local Hint Immediate Equal_refl.

Lemma mem_false : forall w s, WordSet.mem w s = false
  -> ~WordSet.In w s.
  intuition.
  apply WordSet.mem_spec in H0.
  congruence.
Qed.

Lemma remove_preserves : forall x n s (w : W),
  x <> n
  -> w = WordSet.mem n (WordSet.remove x s)
  -> w = WordSet.mem n s.
  intros; subst.
  case_eq (WordSet.mem n (WordSet.remove x s)); case_eq (WordSet.mem n s); intuition.

  apply WordSet.mem_spec in H1.
  apply WordSet.remove_spec in H1; intuition.
  apply WordSet.mem_spec in H2.
  congruence.

  apply mem_false in H1.
  apply WordSet.mem_spec in H0.
  exfalso; apply H1.
  apply WordSet.remove_spec; auto.
Qed.

Local Hint Immediate remove_preserves.

Lemma found_it : forall (w : W) n s,
  w = 1
  -> WordSet.In n s
  -> w = WordSet.mem n s.
  intros; subst.
  case_eq (WordSet.mem n s); intuition.
  apply mem_false in H; tauto.
Qed.

Local Hint Immediate found_it.

Lemma not_there : forall (w : W) n s,
  w = 0
  -> s === WordSet.empty
  -> w = WordSet.mem n s.
  intros; subst.
  case_eq (WordSet.mem n s); intuition.
  apply WordSet.mem_spec in H.
  apply H0 in H.
  apply WordSet.empty_spec in H; tauto.
Qed.

Local Hint Immediate not_there.

Lemma add_idem : forall (w : W) n s,
  w = 1
  -> w = WordSet.mem n s
  -> s === WordSet.add n s.
  intros; subst; hnf; intuition.
  apply WordSet.add_spec; auto.
  apply WordSet.add_spec in H; intuition subst.
  symmetry in H0; simpl in H0.
  apply WordSet.mem_spec.
  case_eq (WordSet.mem n s); intuition.
  rewrite H in H0.
  discriminate.
Qed.

Local Hint Immediate add_idem.

Lemma really_not_there : forall (w : W) n s,
  w <> 1
  -> w = WordSet.mem n s
  -> ~WordSet.In n s.
  intuition subst.
  apply WordSet.mem_spec in H1.
  case_eq (WordSet.mem n s); intros; rewrite H0 in *; try congruence; auto.
Qed.

Local Hint Immediate really_not_there.

Lemma In_add : forall n s,
  WordSet.In n (WordSet.add n s).
  intros; apply WordSet.add_spec; auto.
Qed.

Local Hint Immediate In_add.

Lemma add_remove : forall s n,
  ~WordSet.In n s
  -> s === WordSet.remove n (WordSet.add n s).
  intros; hnf; intuition.
  apply WordSet.remove_spec; intuition (try congruence).
  apply WordSet.add_spec; auto.
  apply WordSet.remove_spec in H0; intuition.
  apply WordSet.add_spec in H1; intuition.
Qed.

Local Hint Immediate add_remove.

Local Hint Extern 1 (himp _ (lset' _ _ _) (lset' _ _ _)) => apply lset'_monotone.

Require Coq.MSets.MSetProperties.
Module Props := MSetProperties.WProperties(WordSet).

Lemma length_step : forall w s n acc,
  WordSet.In n s
  -> w = natToW (WordSet.cardinal (WordSet.remove n s)) ^+ (acc ^+ natToW 1)
  -> w = natToW (WordSet.cardinal s) ^+ acc.
  intros; subst.
  replace (WordSet.cardinal s) with (S (WordSet.cardinal (WordSet.remove n s))).
  rewrite (natToW_S (WordSet.cardinal (WordSet.remove n s))); words.
  apply Props.remove_cardinal_1; auto.
Qed.

Local Hint Immediate length_step.

Lemma length_done : forall w acc s,
  w = acc
  -> s === WordSet.empty
  -> w = natToW (WordSet.cardinal s) ^+ acc.
  intros; subst.
  rewrite WordSet.cardinal_spec.
  specialize (WordSet.elements_spec1 s); intro.
  case_eq (WordSet.elements s); simpl; intros.
  words.
  rewrite H1 in H.
  exfalso; apply WordSet.empty_spec with e.
  hnf in H0.
  apply H0.
  apply WordSet.elements_spec1.
  rewrite H1.
  auto.
Qed.

Local Hint Immediate length_done.

Theorem ok : moduleOk m.
  vcgen; abstract (sep hints; eauto).
Qed.
