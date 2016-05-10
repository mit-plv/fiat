Require Import Coq.Classes.Morphisms Coq.Relations.Relation_Definitions.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Common.List.ListMorphisms.

Fixpoint Proper_relation_for (T : TypeCode) : relation (interp_TypeCode T)
  := match T return relation (interp_TypeCode T) with
     | csimple T' => eq
     | carrow A B => (Proper_relation_for A ==> Proper_relation_for B)%signature
     end.

Global Instance Proper_relation_for_Symmetric {T} : Symmetric (Proper_relation_for T).
Proof.
  induction T; simpl; try exact _; [].
  unfold respectful.
  intros x y Hxy a b H.
  symmetry.
  eauto.
Qed.

Global Instance Proper_relation_for_Transitive {T} : Transitive (Proper_relation_for T).
Proof.
  induction T; simpl; try exact _; [].
  unfold respectful.
  intros x y z Hxy Hyz a b H.
  etransitivity; [ eapply Hxy | eapply Hyz ]; try eassumption.
  etransitivity; [ symmetry | ]; eassumption.
Qed.

Section terms.
  Local Ltac list_proper_pretac :=
    repeat match goal with
           | [ H : ?ls = _ :> list _ |- _ ] => subst ls
           | [ H : _ = ?ls :> list _ |- _ ] => subst ls
           | _ => intro
           end.
  Local Ltac list_proper_revert :=
    repeat match goal with
           | [ H : ?T |- _ ]
             => match T with
                | list _ => fail 1
                | _ => revert H
                end
           end.
  Local Ltac list_proper_induct :=
    let ls := match goal with ls : list _ |- _ => ls end in
    induction ls; simpl in *; intros.
  Create HintDb list_proper_syntax discriminated.
  Hint Resolve f_equal2 : list_proper_syntax.

  Local Ltac list_proper_tac :=
    list_proper_pretac; list_proper_revert; list_proper_induct; eauto with list_proper_syntax.

  Global Instance RLiteralTerm_Proper {T} (R : RLiteralTerm T)
  : Proper (Proper_relation_for T) (interp_RLiteralTerm R).
  Proof.
    destruct R as [[]|[]]; simpl; try exact _; unfold respectful, Reflective.ritem_rect_nodep;
      try solve [ list_proper_tac ].
    { repeat intro; subst.
      match goal with
      | [ |- match ?e with _ => _ end = match ?e with _ => _ end ] => is_var e; destruct e
      end;
        eauto. }
    { repeat intro; subst.
      eapply (_ : Proper (pointwise_relation _ _ ==> _ ==> _ ==> _) (@Operations.List.first_index_default _));
        hnf; eauto. }
  Qed.

  Definition RApp_Proper_helper {A B f x}
         {Hf : Proper (Proper_relation_for (A --> B)) f}
         {Hx : Proper (Proper_relation_for A) x}
    : Proper (Proper_relation_for B) (f x).
  Proof.
    apply Hf, Hx.
  Qed.

  Global Instance RApp_Proper {A B f x}
         {Hf : Proper (Proper_relation_for (A --> B)) (interp_Term f)}
         {Hx : Proper (Proper_relation_for A) (interp_Term x)}
    : Proper (Proper_relation_for B) (interp_Term (RApp f x)).
  Proof.
    apply Hf, Hx.
  Qed.

  Global Instance RLambda_Proper {A B f}
         {Hf : Proper (Proper_relation_for (A --> B)) (fun x => interp_Term (f x))}
    : Proper (Proper_relation_for (A --> B)) (interp_Term (RLambda f)).
  Proof.
    simpl.
    intros ?? H.
    apply Hf, H.
  Qed.

  Global Instance apply_args_for_Proper {T}
    : Proper ((Proper_relation_for T)
                ==> (@args_for_related _ _ (fun T => @Proper_relation_for T) _)
                ==> (Proper_relation_for (range_of T)))
             (@apply_args_for T).
  Proof.
    intros ?? H ?? Hargs.
    apply args_for_related_noind_ind in Hargs.
    induction Hargs; simpl in *; eauto.
  Qed.

  Global Instance RLiteralApp_Proper {c t args}
         {Hf : Proper (Proper_relation_for c) (interp_RLiteralTerm t)}
         {Hargs : Proper (@args_for_related _ _ (fun T => @Proper_relation_for T) _)
                         (map_args_for (@interp_Term) args)}
    : Proper (Proper_relation_for (range_of c)) (interp_Term (RLiteralApp t args)).
  Proof.
    hnf; simpl_interp_Term.
    apply apply_args_for_Proper; eauto.
  Qed.
End terms.
