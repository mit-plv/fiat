Require Import Extraction.Core.

Fixpoint NoDuplicates_helper {A} var (vars: list A) :=
  match vars with
  | nil => True
  | cons var' vars => var <> var' /\ NoDuplicates_helper var vars
  end.

Fixpoint NoDuplicates {A} (vars: list A) :=
  match vars with
  | nil => True
  | cons var vars => NoDuplicates_helper var vars /\ NoDuplicates vars
  end.

Fixpoint PreconditionSet_helper {av} (tenv: Telescope av) (ext: StringMap.t (Value av)) (vars: list string) :=
  match vars with
  | nil => True
  | cons var vars => var ∉ ext /\ NotInTelescope var tenv /\ PreconditionSet_helper tenv ext vars
  end.

Definition PreconditionSet {av} (tenv: Telescope av) (ext: StringMap.t (Value av)) (vars: list string) :=
  NoDuplicates vars /\ PreconditionSet_helper tenv ext vars.

Notation "[[[ x ; .. ; y ]]]" := (cons x .. (cons y nil) ..).

Ltac destruct_ands H :=
  match type of H with
  | _ /\ _ => let h1 := fresh in
            let h2 := fresh in
            destruct H as (h1 & h2);
              destruct_ands h1;
              destruct_ands h2
  | True => clear H
  | _ => idtac
  end.

Ltac PreconditionSet_t :=
  match goal with
  | [ H: PreconditionSet _ _ _ |- _ ] =>
    cbv [PreconditionSet PreconditionSet_helper NoDuplicates NoDuplicates_helper] in H;
      destruct_ands H
  end.
