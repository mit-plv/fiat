Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.PropertiesOfTelescopes.

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
  | cons var vars => (not (StringMap.In var ext)) /\ NotInTelescope var tenv /\ PreconditionSet_helper tenv ext vars
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

Ltac _PreconditionSet_t_in H :=
  cbv beta iota zeta delta [PreconditionSet PreconditionSet_helper NoDuplicates NoDuplicates_helper] in H;
  destruct_ands H.

Ltac _PreconditionSet_t :=
  cbv beta iota zeta delta [PreconditionSet PreconditionSet_helper NoDuplicates NoDuplicates_helper];
  repeat match goal with
         | |- _ /\ _ => split
         end.

Ltac PreconditionSet_t :=
     repeat
     match goal with
     | [ H: PreconditionSet _ _ _ |- _ ] => _PreconditionSet_t_in H
     | [ H: PreconditionSet_helper _ _ _ |- _ ] => _PreconditionSet_t_in H
     | [ H: NoDuplicates _ |- _ ] => _PreconditionSet_t_in H
     | [ H: NoDuplicates_helper _ _ |- _ ] => _PreconditionSet_t_in H
     | [  |- PreconditionSet _ _ _ ] => _PreconditionSet_t
     | [  |- PreconditionSet_helper _ _ _ ] => _PreconditionSet_t
     | [  |- NoDuplicates _ ] => _PreconditionSet_t
     | [  |- NoDuplicates_helper _ _ ] => _PreconditionSet_t
     end.
