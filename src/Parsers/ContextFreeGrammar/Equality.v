(** * Decidable/boolean equality for context free grammars *)
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Common Fiat.Common.Equality.
Require Import Fiat.Common.Enumerable.
Require Import Fiat.Common.List.ListFacts.

Set Implicit Arguments.

Definition item_beq `{Enumerable Char} (x y : item Char)
: bool
  := match x, y with
       | Terminal P, Terminal Q => enumerable_fun_beq bool_beq P Q
       | Terminal _, _ => false
       | NonTerminal nt, NonTerminal nt' => string_beq nt nt'
       | NonTerminal _, _ => false
     end.

Definition item_lb
: forall `{Enumerable Char} {x y},
    x = y -> item_beq x y = true.
Proof.
  intros ?? []; intros; subst; simpl.
  { apply enumerable_fun_lb.
    { apply (@bool_lb). }
    { reflexivity. } }
  { apply (@string_lb); reflexivity. }
Qed.

Definition item_code {Char} (x y : item Char) : Prop
  := match x, y with
       | Terminal P, Terminal Q => forall x, P x = Q x
       | Terminal _, _ => False
       | NonTerminal nt, NonTerminal nt' => nt = nt'
       | NonTerminal _, _ => False
     end.

Global Instance item_code_Equivalence {Char} : Equivalence (@item_code Char).
Proof.
  split; repeat intros [?|?]; simpl in *; repeat (intros [] || intro); eauto with nocore;
  try solve [ reflexivity
            | symmetry; eauto with nocore
            | etransitivity; eauto with nocore ].
Qed.

Definition item_bl
: forall `{Enumerable Char} {x y : item Char},
    item_beq x y = true -> item_code x y.
Proof.
  intros ?? [] [] H; simpl in *;
  try discriminate.
  { intro; eapply (enumerable_fun_bl _ (@bool_bl)) in H; eassumption. }
  { apply string_bl in H; assumption. }
Qed.

Definition item_lb_code
: forall `{Enumerable Char} {x y : item Char},
    item_code x y -> item_beq x y = true.
Proof.
  intros ?? [?|?] [?|?]; simpl; (intros [] || intro).
  { apply enumerable_fun_lb; try assumption.
    intros ??; eapply bool_lb. }
  { apply string_lb; reflexivity. }
Qed.

Definition production_beq `{Enumerable Char} : production Char -> production Char -> bool
  := list_beq (@item_beq Char _).
Definition productions_beq `{Enumerable Char} : productions Char -> productions Char -> bool
  := list_beq (@production_beq Char _).
Definition production_lb `{Enumerable Char} {x y : production Char} : x = y -> production_beq x y = true
  := list_lb (@item_lb _ _).
Definition productions_lb `{Enumerable Char} {x y : productions Char} : x = y -> productions_beq x y = true
  := list_lb (@production_lb _ _).
Definition production_code {Char} : relation (production Char)
  := SetoidList.eqlistA item_code.
Global Instance production_code_Equivalence {Char} : Equivalence (@production_code Char)
  := _.
Definition production_bl `{Enumerable Char} {x y : production Char} : production_beq x y = true -> production_code x y
  := list_blA (@item_bl _ _).
Definition production_lb_code `{Enumerable Char} {x y : production Char}
: production_code x y -> production_beq x y = true
  := list_lbA (@item_lb_code _ _).

Definition productions_code {Char} : relation (productions Char)
  := SetoidList.eqlistA production_code.
Global Instance productions_code_Equivalence {Char} : Equivalence (@productions_code Char)
  := _.
Definition productions_bl `{Enumerable Char} {x y : productions Char} : productions_beq x y = true -> productions_code x y
  := list_blA (@production_bl _ _).

Definition productions_lb_code `{Enumerable Char} {x y : productions Char}
: productions_code x y -> productions_beq x y = true
  := list_lbA (@production_lb_code _ _).


Definition production_code_invert_app {Char} {x y z : production Char}
: production_code (x ++ y)%list z <-> (exists x' y', x' ++ y' = z /\ production_code x x' /\ production_code y y')%list
  := eqlistA_app_iff _ _ _ _.

Definition productions_code_invert_app {Char} {x y z : productions Char}
: productions_code (x ++ y)%list z <-> (exists x' y', x' ++ y' = z /\ productions_code x x' /\ productions_code y y')%list
  := eqlistA_app_iff _ _ _ _.

Global Instance item_beq_Proper `{Enumerable Char}
: Proper (item_code ==> item_code ==> eq) item_beq.
Proof.
  intros x y H' x' y' H''.
  destruct (item_beq x x') eqn:H''';
  destruct (item_beq y y') eqn:H''''; trivial;
  [ apply item_bl in H''';
    rewrite item_lb_code in H''''; [ congruence | ]
  | apply item_bl in H'''';
    rewrite item_lb_code in H'''; [ congruence | ] ];
  etransitivity; try eassumption;
  etransitivity; try eassumption;
  symmetry; assumption.
Qed.

Global Instance production_beq_Proper `{Enumerable Char}
: Proper (production_code ==> production_code ==> eq) production_beq.
Proof.
  intros x y H' x' y' H''.
  destruct (production_beq x x') eqn:H''';
  destruct (production_beq y y') eqn:H''''; trivial;
  [ apply production_bl in H''';
    rewrite production_lb_code in H''''; [ congruence | ]
  | apply production_bl in H'''';
    rewrite production_lb_code in H'''; [ congruence | ] ];
  etransitivity; try eassumption;
  etransitivity; try eassumption;
  symmetry; assumption.
Qed.

Global Instance productions_beq_Proper `{Enumerable Char}
: Proper (productions_code ==> productions_code ==> eq) productions_beq.
Proof.
  intros x y H' x' y' H''.
  destruct (productions_beq x x') eqn:H''';
  destruct (productions_beq y y') eqn:H''''; trivial;
  [ apply productions_bl in H''';
    rewrite productions_lb_code in H''''; [ congruence | ]
  | apply productions_bl in H'''';
    rewrite productions_lb_code in H'''; [ congruence | ] ];
  etransitivity; try eassumption;
  etransitivity; try eassumption;
  symmetry; assumption.
Qed.
