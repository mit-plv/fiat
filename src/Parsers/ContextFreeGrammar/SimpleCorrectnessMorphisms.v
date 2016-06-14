(** * Setoid lemmas about what it means for a simple_parse_of to be correct *)
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.SimpleCorrectness.
Require Import Fiat.Common Fiat.Common.SetoidInstances.

Section correctness.
  Context {Char} {HSLM} {HSL : @StringLike Char HSLM} {HSLP : StringLikeProperties Char}.
  Context (G : grammar Char).

  Local Ltac t_step :=
    idtac;
    match goal with
    | _ => progress unfold respectful in *
    | _ => progress simpl in *
    | _ => intro
    | _ => progress subst
    | [ |- context[match ?e with _ => _ end] ] => is_var e; destruct e
    | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
    | [ |- ?R ?x ?x ] => reflexivity
    | _ => solve [ eauto using eq_refl with nocore ]
    | [ H : beq ?x _ |- _ ] => clear H x
    | [ H : beq _ ?x |- _ ] => clear H x
    | [ H : beq ?x ?y |- context[length ?x] ]
      => replace (length x) with (length y) by (rewrite H; reflexivity)
    | [ H : beq ?x ?y |- context[is_char ?x ?ch] ]
      => replace (is_char x ch) with (is_char y ch) by (rewrite H; reflexivity)
    | [ H : forall a b c d e f g h i, ?R (?F _ _ _) (?G _ _ _) |- ?R (?F _ _ _) (?G _ _ _) ]
      => eapply H; setoid_subst_rel (@beq _ _ _); reflexivity
    | [ H : forall a b c d e, ?R (?F _ _ _) (?G _ _ _) |- ?R (?F _ _ _) (?G _ _ _) ]
      => eapply H; setoid_subst_rel (@beq _ _ _); reflexivity
    end.
  Local Ltac t := repeat t_step.

  Section gen.
    Context {R : relation Prop}
            {RRefl : Reflexive R}
            {R_ex : forall A, Proper ((pointwise_relation _ R) ==> R)
                                     (@ex A)}
            {R_and : Proper (R ==> R ==> R) and}.

    Global Instance simple_parse_of_correct_step_Proper_gen
      : Proper ((beq ==> eq ==> eq ==> R)
                  ==> (beq ==> eq ==> eq ==> R)
                  ==> beq ==> eq ==> eq ==> R)
               simple_parse_of_correct_step.
    Proof. unfold simple_parse_of_correct_step; t. Qed.

    Global Instance simple_parse_of_production_correct_step_Proper_gen
      : Proper ((beq ==> eq ==> eq ==> R)
                  ==> (beq ==> eq ==> eq ==> R)
                  ==> beq ==> eq ==> eq ==> R)
               simple_parse_of_production_correct_step.
    Proof.
      unfold simple_parse_of_production_correct_step; t.
      apply R_ex; t.
      apply R_and; t.
    Qed.

    Global Instance simple_parse_of_item_correct_step_Proper_gen
      : Proper ((beq ==> eq ==> eq ==> R)
                  ==> beq ==> eq ==> eq ==> R)
               (simple_parse_of_item_correct_step G).
    Proof. unfold simple_parse_of_item_correct_step; t. Qed.

    Fixpoint simple_parse_of_correct_Proper_gen' (x y : String) (H : x =s y)
             p0 p'
      : R (simple_parse_of_correct G x p0 p') (simple_parse_of_correct G y p0 p')
    with simple_parse_of_production_correct_Proper_gen' (x y : String) (H : x =s y)
             p0 p'
      : R (simple_parse_of_production_correct G x p0 p') (simple_parse_of_production_correct G y p0 p')
    with simple_parse_of_item_correct_Proper_gen' (x y : String) (H : x =s y)
             p0 p'
      : R (simple_parse_of_item_correct G x p0 p') (simple_parse_of_item_correct G y p0 p').
    Proof.
      { destruct p', p0; simpl_simple_parse_of_correct; t. }
      { destruct p', p0; simpl_simple_parse_of_correct; t.
        apply R_ex; t.
        apply R_and; t. }
      { destruct p', p0; simpl_simple_parse_of_correct; t. }
    Qed.

    Global Instance simple_parse_of_correct_Proper_gen
      : Proper (beq ==> eq ==> eq ==> R) (simple_parse_of_correct G).
    Proof. t; apply simple_parse_of_correct_Proper_gen'; assumption. Qed.

    Global Instance simple_parse_of_production_correct_Proper_gen
      : Proper (beq ==> eq ==> eq ==> R) (simple_parse_of_production_correct G).
    Proof. t; apply simple_parse_of_production_correct_Proper_gen'; assumption. Qed.

    Global Instance simple_parse_of_item_correct_Proper_gen
      : Proper (beq ==> eq ==> eq ==> R) (simple_parse_of_item_correct G).
    Proof. t; apply simple_parse_of_item_correct_Proper_gen'; assumption. Qed.
  End gen.

  Global Instance simple_parse_of_correct_step_Proper_impl : Proper _ _
    := @simple_parse_of_correct_step_Proper_gen impl _.
  Global Instance simple_parse_of_correct_step_Proper_iff : Proper _ _
    := @simple_parse_of_correct_step_Proper_gen iff _.
  Global Instance simple_parse_of_correct_step_Proper_flip_impl : Proper _ _
    := @simple_parse_of_correct_step_Proper_gen (flip impl) _.

  Global Instance simple_parse_of_production_correct_step_Proper_impl : Proper _ _
    := @simple_parse_of_production_correct_step_Proper_gen impl _ _ _.
  Global Instance simple_parse_of_production_correct_step_Proper_iff : Proper _ _
    := @simple_parse_of_production_correct_step_Proper_gen iff _ _ _.
  Global Instance simple_parse_of_production_correct_step_Proper_flip_impl : Proper _ _
    := @simple_parse_of_production_correct_step_Proper_gen (flip impl) _ _ _.

  Global Instance simple_parse_of_item_correct_step_Proper_impl : Proper _ _
    := @simple_parse_of_item_correct_step_Proper_gen impl _ _.
  Global Instance simple_parse_of_item_correct_step_Proper_iff : Proper _ _
    := @simple_parse_of_item_correct_step_Proper_gen iff _ _.
  Global Instance simple_parse_of_item_correct_step_Proper_flip_impl : Proper _ _
    := @simple_parse_of_item_correct_step_Proper_gen (flip impl) _ _.

  Global Instance simple_parse_of_correct_Proper_impl : Proper _ _
    := @simple_parse_of_correct_Proper_gen impl _ _ _.
  Global Instance simple_parse_of_correct_Proper_iff : Proper _ _
    := @simple_parse_of_correct_Proper_gen iff _ _ _.
  Global Instance simple_parse_of_correct_Proper_flip_impl : Proper _ _
    := @simple_parse_of_correct_Proper_gen (flip impl) _ _ _.

  Global Instance simple_parse_of_production_correct_Proper_impl : Proper _ _
    := @simple_parse_of_production_correct_Proper_gen impl _ _ _.
  Global Instance simple_parse_of_production_correct_Proper_iff : Proper _ _
    := @simple_parse_of_production_correct_Proper_gen iff _ _ _.
  Global Instance simple_parse_of_production_correct_Proper_flip_impl : Proper _ _
    := @simple_parse_of_production_correct_Proper_gen (flip impl) _ _ _.

  Global Instance simple_parse_of_item_correct_Proper_impl : Proper _ _
    := @simple_parse_of_item_correct_Proper_gen impl _ _ _.
  Global Instance simple_parse_of_item_correct_Proper_iff : Proper _ _
    := @simple_parse_of_item_correct_Proper_gen iff _ _ _.
  Global Instance simple_parse_of_item_correct_Proper_flip_impl : Proper _ _
    := @simple_parse_of_item_correct_Proper_gen (flip impl) _ _ _.
End correctness.
