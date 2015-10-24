(** * Decidable/boolean equality for context free grammars *)
Require Import Coq.Strings.String Coq.Setoids.Setoid.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Common Fiat.Common.Equality.

Set Implicit Arguments.

Scheme Equality for item.

Definition item_bl
: forall {Char eq_Char} (Char_bl : forall x y : Char, eq_Char x y = true -> x = y) {x y},
    item_beq eq_Char x y = true -> x = y
  := internal_item_dec_bl.

Definition item_lb
: forall {Char eq_Char} (Char_lb : forall x y : Char, x = y -> eq_Char x y = true) {x y},
    x = y -> item_beq eq_Char x y = true
  := internal_item_dec_lb.

Section beq_correct.
  Local Ltac t rew_t :=
    match goal with
      | [ |- _ = bool_of_sumbool (?eq_dec ?x ?y) ]
        => revert y; induction x; intro y; simpl
    end;
    match goal with
      | [ |- _ = bool_of_sumbool (?eq_dec ?x ?y) ]
        => destruct (eq_dec x y)
    end;
    subst; simpl in *;
    try solve [ repeat match goal with
                         | [ H : _ <> ?y |- _ ] => is_var y; destruct y
                         | [ H : ?x <> ?x |- _ ] => destruct (H eq_refl)
                         | [ H : _ |- _ ] => rewrite !H; []
                         | _ => progress rew_t
                         | _ => progress simpl in *
                         | _ => split; (congruence || discriminate)
                         | _ => progress subst
                         | [ |- context[bool_of_sumbool ?e] ]
                           => destruct e; simpl
                         | [ |- true = false ] => exfalso
                         | [ |- false = true ] => exfalso
                         | [ H : _ <> _ |- False ] => apply H; clear H
                         | [ |- ?x = false ] => case_eq x; intro
                       end ].

  Lemma item_beq_correct {Char eq_Char}
        (Char_bl : forall x y : Char, eq_Char x y = true -> x = y)
        (Char_lb : forall x y : Char, x = y -> eq_Char x y = true)
        {x y : item Char}
  : item_beq eq_Char x y = item_eq_dec eq_Char Char_bl Char_lb x y.
  Proof.
    t ltac:(first [ rewrite !(Char_lb _ _) by congruence
                  | erewrite (Char_bl _ _) by eassumption
                  | rewrite !string_beq_correct by congruence
                  | rewrite Bool.andb_true_r
                  | rewrite Bool.andb_false_r ]).
  Qed.
  Definition item_eq_dec' {Char} (dec_eq_Char : forall x y : Char, {x = y} + {x <> y})
  : forall x y : item Char, {x = y} + {x <> y}.
  Proof.
    refine (item_eq_dec dec_eq_Char _ _);
    abstract (intros; edestruct dec_eq_Char; simpl in *; subst; congruence).
  Defined.
  Lemma item_beq_correct' {Char} {eq_Char : Char -> Char -> bool} {dec_eq_Char : forall x y : Char, {x = y} + {x <> y}}
        (eq_Char_correct : forall x y, eq_Char x y = dec_eq_Char x y)
        {x y : item Char}
  : item_beq eq_Char x y = item_eq_dec' dec_eq_Char x y.
  Proof.
    unfold item_eq_dec'; erewrite item_beq_correct.
    do 2 edestruct item_eq_dec; subst; simpl; congruence.
    Grab Existential Variables.
    intros ??; rewrite eq_Char_correct; edestruct dec_eq_Char; simpl; congruence.
    intros ??; rewrite eq_Char_correct; edestruct dec_eq_Char; simpl; congruence.
  Qed.
End beq_correct.

Definition production_beq {Char} eq_Char : production Char -> production Char -> bool
  := list_beq (@item_beq Char eq_Char).
Definition productions_beq {Char} eq_Char : productions Char -> productions Char -> bool
  := list_beq (@production_beq Char eq_Char).
Definition production_bl {Char eq_Char} Char_bl {x y : production Char} : production_beq eq_Char x y = true -> x = y
  := list_bl (@item_bl _ _ Char_bl).
Definition productions_bl {Char eq_Char} Char_bl {x y : productions Char} : productions_beq eq_Char x y = true -> x = y
  := list_bl (@production_bl _ _ Char_bl).
Definition production_lb {Char eq_Char} Char_lb {x y : production Char} : x = y -> production_beq eq_Char x y = true
  := list_lb (@item_lb _ _ Char_lb).
Definition productions_lb {Char eq_Char} Char_lb {x y : productions Char} : x = y -> productions_beq eq_Char x y = true
  := list_lb (@production_lb _ _ Char_lb).
Definition production_eq_dec {Char} eq_Char Char_bl Char_lb : forall x y : production Char, {x = y} + {x <> y}
  := list_eq_dec (@item_beq Char eq_Char) (@item_bl _ _ Char_bl) (@item_lb _ _ Char_lb).
Definition productions_eq_dec {Char} eq_Char Char_bl Char_lb : forall x y : productions Char, {x = y} + {x <> y}
  := list_eq_dec (@production_beq Char eq_Char) (@production_bl _ _ Char_bl) (@production_lb _ _ Char_lb).
Definition production_beq_correct {Char eq_Char} Char_bl Char_lb {x y : production Char}
: production_beq eq_Char x y = production_eq_dec eq_Char Char_bl Char_lb x y
  := list_beq_correct _ _.
Definition productions_beq_correct {Char eq_Char} Char_bl Char_lb {x y : productions Char}
: productions_beq eq_Char x y = productions_eq_dec eq_Char Char_bl Char_lb x y
  := list_beq_correct _ _.
Definition production_eq_dec' {Char} dec_eq_Char : forall x y : production Char, {x = y} + {x <> y}
  := list_eq_dec' (@item_eq_dec' _ dec_eq_Char).
Definition productions_eq_dec' {Char} dec_eq_Char : forall x y : productions Char, {x = y} + {x <> y}
  := list_eq_dec' (@production_eq_dec' _ dec_eq_Char).
Definition production_beq_correct' {Char eq_Char dec_eq_Char} eq_Char_correct {x y : production Char}
: production_beq eq_Char x y = production_eq_dec' dec_eq_Char x y
  := list_beq_correct' eq_Char_correct.
Definition productions_beq_correct' {Char eq_Char dec_eq_Char} eq_Char_correct {x y : productions Char}
: productions_beq eq_Char x y = productions_eq_dec' dec_eq_Char x y
  := list_beq_correct' eq_Char_correct.
