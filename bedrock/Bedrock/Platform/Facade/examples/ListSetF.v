Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.FiatADTs Bedrock.Platform.Facade.examples.FiniteSetF.


Module Type ADT.
  Parameter lset : Ensemble W -> W -> HProp.
  Parameter lset' : Ensemble W -> nat -> W -> HProp.

  Axiom lset_fwd : forall s c, lset s c ===> [| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * Ex n, lset' s n p.
  Axiom lset_bwd : forall s (c : W), ([| c <> 0 |] * [| freeable c 2 |]
    * Ex p, Ex junk, (c ==*> p, junk) * Ex n, lset' s n p) ===> lset s c.

  Axiom lset'_empty_fwd : forall s n (c : W), c = 0
    -> lset' s n c
    ===> [| n = O |] * [| s === %0 |].

  Axiom lset'_empty_bwd : forall s n (c : W), c = 0
    -> [| n = O |] * [| s === %0 |] ===> lset' s n c.

  Axiom lset'_nonempty_fwd : forall s n (c : W), c <> 0
    -> lset' s n c
    ===> Ex n', [| n = S n' |] * [| freeable c 2 |] * Ex x, [| s %has x |] * Ex p', (c ==*> x, p')
        * lset' (s %- x) n' p'.

  Axiom lset'_nonempty_bwd : forall s n (c : W), c <> 0
    -> (Ex n', [| n = S n' |] * [| freeable c 2 |] * Ex x, [| s %has x |] * Ex p', (c ==*> x, p')
        * lset' (s %- x) n' p') ===> lset' s n c.

  Axiom lset'_monotone : forall n s s' p, s === s'
    -> lset' s n p ===> lset' s' n p.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Fixpoint lset' (s : Ensemble W) (n : nat) (p : W) : HProp :=
    match n with
      | O => [| p = 0 |] * [| s === %0 |]
      | S n' => [| p <> 0 |] * [| freeable p 2 |]
        * Ex x, [| s %has x |] * Ex p', (p ==*> x, p')
        * lset' (s %- x) n' p'
    end.

  Definition lset (s : Ensemble W) (c : W) : HProp :=
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
    ===> [| n = O |] * [| s === %0 |].
    destruct n; sepLemma.
  Qed.

  Theorem lset'_empty_bwd : forall s n (c : W), c = 0
    -> [| n = O |] * [| s === %0 |] ===> lset' s n c.
    destruct n; sepLemma.
  Qed.

  Theorem lset'_nonempty_fwd : forall s n (c : W), c <> 0
    -> lset' s n c
    ===> Ex n', [| n = S n' |] * [| freeable c 2 |] * Ex x, [| s %has x |] * Ex p', (c ==*> x, p')
        * lset' (s %- x) n' p'.
    destruct n; sepLemma.
  Qed.

  Theorem lset'_nonempty_bwd : forall s n (c : W), c <> 0
    -> (Ex n', [| n = S n' |] * [| freeable c 2 |] * Ex x, [| s %has x |] * Ex p', (c ==*> x, p')
        * lset' (s %- x) n' p') ===> lset' s n c.
    destruct n; sepLemma.
    injection H0; sepLemma.
  Qed.

  Theorem lset'_monotone : forall n s s' p, s === s'
    -> lset' s n p ===> lset' s' n p.
    induction n; sepLemma.
    split; do 2 intro.
    apply (proj2 H) in H0.
    apply (proj1 H1) in H0.
    auto.
    destruct H0.
    rewrite has_eq in *.
    apply H; auto.
    apply IHn.
    split; do 2 intro.
    destruct H3.
    split; auto.
    apply H; auto.
    destruct H3.
    split; auto.
    apply H; auto.
  Qed.
End Adt.

Import Adt.
Export Adt.

(* Hm... to avoid stack overflow, need to rebind these! *)
Definition lset'_empty_fwd : forall s n (c : W), c = 0
  -> lset' s n c
  ===> [| n = O |] * [| s === %0 |] := lset'_empty_fwd.

Definition lset'_empty_bwd : forall s n (c : W), c = 0
  -> [| n = O |] * [| s === %0 |] ===> lset' s n c := lset'_empty_bwd.

Definition hints : TacPackage.
  prepare (lset_fwd, lset'_empty_fwd, lset'_nonempty_fwd)
  (lset_bwd, lset'_empty_bwd, lset'_nonempty_bwd).
Defined.

Definition newS := newS lset 8.
Definition deleteS := deleteS lset 7.
Definition memS := memS lset 1.
Definition addS := addS lset 9.
Definition removeS := removeS lset 7.
Definition sizeS := sizeS lset 1.

Definition cardinal_plus (s : Ensemble W) (R acc : W) :=
  exists n, cardinal _ s n /\ R = natToWord _ n ^+ acc.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "ListSet" {{
    bfunction "new"("extra_stack", "x") [newS]
      "x" <-- Call "malloc"!"malloc"(0, 2)
      [PRE[_, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] * mallocHeap 0
       POST[R'] lset %0 R' * mallocHeap 0];;

      "x" *<- 0;;
      Return "x"
    end

    with bfunction "delete"("extra_stack", "self", "ls") [deleteS]
      "ls" <-* "self";;

      Call "malloc"!"free"(0, "self", 2)
      [Al s, Al n,
        PRE[V] lset' s n (V "ls") * mallocHeap 0
        POST[R] [| R = $0 |] * mallocHeap 0];;

      [Al s, Al n,
        PRE[V] lset' s n (V "ls") * mallocHeap 0
        POST[R] [| R = $0 |] * mallocHeap 0]
      While ("ls" <> 0) {
        "self" <-* "ls"+4;;
        Call "malloc"!"free"(0, "ls", 2)
        [Al s, Al n,
          PRE[V] lset' s n (V "self") * mallocHeap 0
          POST[R] [| R = $0 |] * mallocHeap 0];;

        "ls" <- "self"
      };;

      Return 0
    end

    with bfunction "mem"("extra_stack", "self", "n", "tmp") [memS]
      "self" <-* "self";;

      [Al s, Al n,
        PRE[V] lset' s n (V "self")
        POST[R] lset' s n (V "self") * [| s %has V "n" \is R |] ]
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
        PRE[V, R] [| s %has V "n" \is R |] * lset s (V "self") * mallocHeap 0
        POST[R'] [| R' = $0 |] * lset (s %+ V "n") (V "self") * mallocHeap 0];;

      If ("tmp" = 1) {
        Return 0
      } else {
        "tmp" <-- Call "malloc"!"malloc"(0, 2)
        [Al s,
          PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
            * [| ~s %has V "n" |] * lset s (V "self")
          POST[R'] [| R' = $0 |] * lset (s %+ V "n") (V "self")];;

        "tmp" *<- "n";;
        "n" <-* "self";;
        "tmp"+4 *<- "n";;
        "self" *<- "tmp";;
        Return 0
      }
    end

    with bfunction "remove"("extra_stack", "self", "n", "tmp") [removeS]
      "tmp" <-* "self";;

      [Al s, Al n,
        PRE[V] V "self" =*> V "tmp" * lset' s n (V "tmp") * mallocHeap 0
        POST[R] [| R = $0 |] * Ex p, Ex n', V "self" =*> p * lset' (s %- V "n") n' p * mallocHeap 0 ]
      While ("tmp" <> 0) {
        "tmp" <-* "tmp";;

        If ("tmp" = "n") {
          "tmp" <-* "self";;
          "n" <-* "tmp"+4;;
          "self" *<- "n";;

          Call "malloc"!"free"(0, "tmp", 2)
          [PRE[_] Emp
           POST[R] [| R = $0 |] ];;

          Return 0
        } else {
          "tmp" <-* "self";;
          "self" <- "tmp"+4;;
          "tmp" <-* "self"
        }
      };;

      Return 0
    end

    with bfunction "size"("extra_stack", "self", "acc") [sizeS]
      "self" <-* "self";;
      "acc" <- 0;;

      [Al s, Al n,
        PRE[V] lset' s n (V "self")
        POST[R] lset' s n (V "self") * [| cardinal_plus s R (V "acc") |] ]
      While ("self" <> 0) {
        "acc" <- "acc" + 1;;
        "self" <-* "self"+4
      };;

      Return "acc"
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Theorem Singleton_bwd : forall A x y,
  Singleton A x y -> x = y.
  destruct 1; auto.
Qed.

Local Hint Immediate Singleton_bwd.

Ltac sets' := try rewrite has_eq in *;
  unfold propToWord, IF_then_else, add, sub, Ensembles.Add, Subtract, Setminus,
  Same_set, Included, Ensembles.In in *;
  intuition eauto.

Theorem Union_fwd : forall A x y z,
  x z \/ y z
  -> Union A x y z.
Proof.
  intuition; solve [ constructor; auto | constructor 2; auto ].
Qed.

Ltac sets :=
  repeat match goal with
           | [ H : _ === _ |- _ ] => generalize dependent H
           | [ H : _ %has _ |- _ ] => generalize dependent H
           | [ H : ~(_ %has _) |- _ ] => generalize dependent H
           | [ H : _ %has _ \is _ |- _ ] => generalize dependent H
           | [ H : @eq W _ _ |- _ ] => generalize dependent H
           | [ H : not (@eq W _ _) |- _ ] => generalize dependent H
         end; clear; intros;
  sets'; repeat (match goal with
                   | [ H0 : ?X = natToW 0, H1 : ?X = natToW 1 |- _ ] => rewrite H0 in H1; discriminate
                   | [ H : Empty_set _ _ |- _ ] => destruct H
                   | [ H : Singleton _ _ _ |- _ ] => destruct H
                   | [ |- Singleton _ _ _] => constructor
                   | [ H : Union _ _ _ _ |- _ ] => destruct H
                   | [ |- Union _ _ _ _] => apply Union_fwd
                 end; sets').

Theorem empty_bwd : forall x, %0 x -> False.
  destruct 1.
Qed.

Local Hint Resolve empty_bwd.

Lemma cardinal_plus_O : forall s w, cardinal_plus s w 0
  -> cardinal_is s w.
  destruct 1; intuition; eexists; eauto.
Qed.

Local Hint Immediate cardinal_plus_O.

Fixpoint nuke (ls : list W) (w : W) : list W :=
  match ls with
    | nil => nil
    | w' :: ls' =>
      if weq w' w then ls' else w' :: nuke ls' w
  end.

Lemma nuke_ok : forall w ls s,
  EnsembleListEquivalence (s %- w) ls
  -> s %has w
  -> EnsembleListEquivalence s (w :: ls).
  intros.
  destruct H.
  split.
  constructor; auto.
  intro.
  apply H1 in H2.
  destruct H2.
  apply H3.
  constructor.

  simpl; intuition.
  destruct (weq w x); auto.
  right; apply H1.
  constructor; auto.
  subst; sets.
  apply H1 in H3.
  destruct H3; auto.
Qed.

Lemma cardinal_plus_minus : forall s w r acc,
  cardinal_plus (s %- w) r (acc ^+ natToW 1)
  -> s %has w
  -> cardinal_plus s r acc.
  destruct 1; intuition subst.
  destruct H1; intuition subst.
  eexists; split.
  hnf; eauto using nuke_ok.
  simpl.
  rewrite natToWord_S.
  rewrite <- plus_n_O.
  words.
Qed.

Local Hint Immediate cardinal_plus_minus.

Lemma cardinal_is_bottom : forall r acc s,
  r = acc
  -> s === %0
  -> cardinal_plus s r acc.
Proof.
  intros; subst.
  exists 0; intuition.
  exists nil; intuition.
  split; intuition.
  constructor.
  apply H0 in H.
  destruct H.
Qed.

Local Hint Immediate cardinal_is_bottom.

Theorem ok : moduleOk m.
  vcgen; abstract (sep hints; eauto; try apply lset'_monotone; sets).
Qed.
