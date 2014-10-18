Require Import Coq.Lists.List Coq.Program.Program Coq.Arith.Wf_nat Coq.Init.Wf.
Require Export Parsers.ListLike.
Require Import Common.

Set Implicit Arguments.

Module Type EqDecType.
  Parameter t : Type.
  Axiom eqb : t -> t -> bool.
  Parameter eqb_1 : forall x, eqb x x = true.
  Parameter eqb_2 : forall x y, eqb x y = true -> x = y.
End EqDecType.

Module ListListLike (T : EqDecType) <: ListLike T.
  Definition t := list T.t.
  Bind Scope list_like_scope with t.
  Delimit Scope list_like_scope with list_like.
  Local Open Scope bool_scope.
  Local Open Scope list_like_scope.

  Local Infix "=b" := T.eqb (at level 70, right associativity).

  Definition empty : t := nil.
  (** The empty list. *)
  Notation "[ ]" := empty : list_like_scope.

  Definition is_empty (ls : t) : bool := match ls with nil => true | _ => false end.
  (** Test whether a list is empty or not. *)

  Definition mem (x : T.t) (ls : t) : bool
    := fold_right orb false (map (T.eqb x) ls).
  (** [mem x s] tests whether [x] belongs to the list [s]. *)

  Infix "∈" := mem (at level 20, no associativity) : list_like_scope.
  Notation "y ∉ s" := (negb (y ∈ s)) (at level 20, no associativity) : list_like_scope.

  Definition add : T.t -> t -> t := cons.
  (** [add x s] returns a list containing all elements of [s], plus
      [x]. If [x] was already in [s], [s] is returned unchanged. *)

  Definition remove (x : T.t) (ls : t) : t
    := filter (negb ∘ T.eqb x) ls.
  (** [remove x s] returns a list containing all elements of [s],
      except [x]. If [x] was not in [s], [s] is returned unchanged. *)

  Definition append : t -> t -> t := @app _.
  (** Concatenate two lists. *)

  Infix "++" := append : list_like_scope.

  Definition lt : t -> t -> Prop := ltof _ (@List.length _).
  (** Is one list smaller than another? *)

  Infix "<" := lt : list_like_scope.

  Definition lt_wf : well_founded lt := @well_founded_ltof _ _.

  Local Hint Unfold t empty mem add remove append lt lt_wf is_true ltof : core.

  Section Spec.
    Variable s s' s'': t.
    Variable x y : T.t.

    Local Ltac t :=
      repeat autounfold with core in *;
      repeat match goal with
               | _ => progress simpl in *
               | _ => intro
               | _ => progress subst
               | [ H : false = true |- _ ] => solve [ inversion H ]
               | [ H : true = false |- _ ] => solve [ inversion H ]
               | _ => solve [ trivial ]
               | [ H : forall x, negb ((x =b ?a) || _) = true |- _ ] => specialize (H a)
               | [ H : context[?a =b ?a] |- _ ] => rewrite T.eqb_1 in H
               | [ |- context[?a =b ?a] ] => rewrite T.eqb_1
               | [ H : ?a = true |- context[?a] ] => rewrite H
               | [ H : ?a = false |- context[?a] ] => rewrite H
               | [ H : ?a = true, H' : context[?a] |- _ ] => rewrite H in H'
               | [ H : ?a = false, H' : context[?a] |- _ ] => rewrite H in H'
               | [ H : negb _ = true |- _ ] => symmetry in H; apply Bool.negb_sym in H
               | [ H : negb _ = false |- _ ] => symmetry in H; apply Bool.negb_sym in H
               | [ H : true = negb _ |- _ ] => apply Bool.negb_sym in H
               | [ H : false = negb _ |- _ ] => apply Bool.negb_sym in H
               | [ |- context[(_ || _) = true] ] => rewrite Bool.orb_true_iff
               | [ H : (_ || _) = true |- _ ] => apply Bool.orb_true_elim in H
               | [ |- (_ || _) = false ] => apply Bool.orb_false_iff
               | [ H : (_ || _) = false |- _ ] => apply Bool.orb_false_iff in H
               | [ H : sumbool _ _ |- _ ] => destruct H
               | [ H : and _ _ |- _ ] => destruct H
               | [ H : (_ =b _) = true |- _ ] => apply T.eqb_2 in H
               | [ |- context[if ?a then _ else _] ] => case_eq a
               | [ H : context[if ?a then _ else _] |- _ ] => revert H; case_eq a
               | [ |- context[List.app _ nil] ] => rewrite app_nil_r
               | [ |- (S _ < S _)%nat ] => apply Lt.lt_n_S
               | [ |- (S _ <= S _)%nat ] => apply Le.le_n_S
               | _ => solve [ eauto ]
             end.

    (** Specification of [empty] *)
    Lemma empty_1 : forall x, x ∉ empty.
    Proof. t. Qed.

    (** Specification of is_empty *)
    Lemma is_empty_1 : (forall x, x ∉ s) -> is_empty s.
    Proof. clear; induction s; t. Qed.
    Lemma is_empty_2 : is_empty s -> (forall x, x ∉ s).
    Proof. clear; induction s; t. Qed.

    (** Specification of [add] *)
    Lemma add_1 : x ∈ add x s.
    Proof. clear; t. Qed.
    Lemma add_2 : y ∈ s -> y ∈ add x s.
    Proof. clear; t. Qed.
    Lemma add_3 : y ∉ s -> y ∈ add x s -> y = x.
    Proof. clear; t. Qed.

    (** Specification of [remove] *)
    Lemma remove_1 : x ∉ remove x s.
    Proof. clear; induction s; t. Qed.
    Lemma remove_2 : y ∉ remove x s -> y ∈ s -> y = x.
    Proof. clear; induction s; t. Qed.
    Lemma remove_3 : y ∈ remove x s -> y ∈ s.
    Proof. clear; induction s; t. Qed.

    (** Specification of [append] *)
    Lemma orb_comm_helper a b c : (a || (b || c)) = (b || (a || c)).
    Proof. destruct_head bool; reflexivity. Qed.

    Lemma append_1_helper : x ∈ (s ++ s') = x ∈ (s' ++ s).
    Proof.
      clear; revert s'; induction s as [|? ? IHs]; t.
      rewrite IHs; clear; move s' at top.
      reverse; intro s'; induction s' as [|? ? IHs']; t.
      rewrite <- IHs'; apply orb_comm_helper.
    Qed.

    Lemma append_1' : x ∈ (s ++ s') -> ((x ∈ s) || (x ∈ s')).
    Proof. clear; revert s'; induction s; t; specialize_all_ways; t. Qed.
    Lemma append_2 : x ∈ s -> x ∈ (s ++ s').
    Proof. clear; induction s; t. Qed.
    Lemma append_3 : x ∈ s' -> x ∈ (s ++ s').
    Proof. clear; rewrite append_1_helper; revert s; induction s'; t. Qed.
    Lemma append_1 : x ∈ (s ++ s') = ((x ∈ s) || (x ∈ s')).
    Proof.
      case_eq (x ∈ (s ++ s')).
      { intro H; apply append_1' in H; t. }
      { case_eq (x ∈ s).
        { intro H; apply append_2 in H; t. }
        { case_eq (x ∈ s').
          { intro H; apply append_3 in H; t. }
          { reflexivity. } } }
    Qed.

    Lemma filter_list_dec {T} f (ls : list T) : List.length (filter f ls) <= List.length ls.
    Proof.
      induction ls; trivial; simpl in *.
      repeat match goal with
               | [ |- context[if ?a then _ else _] ] => destruct a; simpl in *
               | [ |- S _ <= S _ ] => solve [ apply Le.le_n_S; auto ]
               | [ |- _ <= S _ ] => solve [ apply le_S; auto ]
             end.
    Qed.

    Local Hint Immediate filter_list_dec.

    (** Specification of [lt] *)
    Lemma lt_1 : x ∈ s -> remove x s < s.
    Proof. clear; induction s; t. Qed.
    Global Instance lt_trans : Transitive lt.
    Proof. unfold lt, ltof; repeat intro; etransitivity; eassumption. Qed.
    Global Instance lt_asym : Asymmetric lt.
    Proof. repeat intro. eapply Lt.lt_irrefl; etransitivity; eassumption. Qed.
  End Spec.
End ListListLike.
