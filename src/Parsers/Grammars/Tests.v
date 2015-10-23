Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar Fiat.Parsers.ContextFreeGrammarNotations.
Require Import Fiat.Common.StringOperations Fiat.Common.StringFacts.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.String.

Require Import Fiat.Parsers.Grammars.ABStar.
Require Import Fiat.Parsers.Grammars.ExpressionNumPlus.
Require Import Fiat.Parsers.Grammars.ExpressionNumPlusParen.
Require Import Fiat.Parsers.Grammars.ExpressionParen.

Section ab_star.
  Example ab_star_parses_empty : parse_of_grammar ""%string ab_star_grammar.
  Proof.
    hnf; simpl.
    repeat constructor.
  Defined.

  Example ab_star_parses_ab : parse_of_grammar "ab"%string ab_star_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead.
    apply ParseProductionCons with (n := 1); simpl.
    { refine (ParseTerminal _ _ _ _); reflexivity. }
    { apply ParseProductionCons with (n := 1); simpl.
      { refine (ParseTerminal _ _ _ _); reflexivity. }
      { apply ParseProductionCons with (n := 1); simpl;
        repeat (simpl; constructor). } }
  Defined.

  Example ab_star_parses_abab : parse_of_grammar "abab"%string ab_star_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead.
    apply ParseProductionCons with (n := 1); simpl.
    { refine (ParseTerminal _ _ _ _); reflexivity. }
    { apply ParseProductionCons with (n := 1); simpl.
      { refine (ParseTerminal _ _ _ _); reflexivity. }
      { apply ParseProductionCons with (n := 2); simpl;
        try solve [ repeat (simpl; constructor) ].
        constructor.
        apply ab_star_parses_ab. } }
  Defined.
End ab_star.

Section num_paren.
  (*Context {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}.*)
  Local Arguments append : simpl never.

  Local Ltac safe_step :=
    idtac;
    (match goal with
       | _ => reflexivity
       | [ |- parse_of_production _ ?s (Terminal _ :: _) ]
         => apply ParseProductionCons with (n := 1)
       | [ |- parse_of_production _ ?s (_ :: nil) ]
         => apply ParseProductionCons with (n := String.length s)
       | [ |- parse_of_production _ ?s (_ :: nil) ]
         => apply ParseProductionCons with (n := StringLike.length s)
       | [ |- parse_of_production _ ?s (_ :: Terminal _ :: nil) ]
         => apply ParseProductionCons with (n := StringLike.length s - 1)
       | [ |- parse_of_production _ _ nil ]
         => apply ParseProductionNil
       | [ |- parse_of_item _ _ (Terminal _) ]
         => apply ParseTerminal
       | [ |- parse_of_item _ _ (NonTerminal _) ]
         => apply ParseNonTerminal
       | [ |- is_true (is_char (take 1 _) _) ] => apply get_0
       (*| [ |- context[StringLike.get _ (of_string _)] ] => (rewrite !get_of_string; simpl)*)
       (*| [ |- context[StringLike.length _] ] => (progress rewrite ?take_length, ?drop_length, ?of_string_length; simpl List.length; simpl minus)*)
       (*| [ |- context[StringLike.get _ _] ] => (progress repeat rewrite ?take_of_string, ?drop_of_string; simpl; rewrite get_of_string; reflexivity)*)
       | _ => progress simpl
     end).

  Local Ltac fin :=
    repeat first [ safe_step
                 | apply ParseProductionCons with (n := 1); solve [ fin ]
                 | constructor (solve [ fin ]) ].

  Example paren_expr_parses_1 : parse_of_grammar ((*of_string*) ((*list_of_string*) "(((123)))"%string)) paren_expr_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead; repeat safe_step; [].
    apply ParseTail, ParseHead; repeat safe_step; [].
    apply ParseTail, ParseHead; repeat safe_step; [].
    apply ParseHead; repeat safe_step; [].
    apply ParseTail, ParseHead; repeat safe_step; [].
    apply ParseProductionCons with (n := 1); repeat safe_step; [ fin | ].
    apply ParseTail, ParseHead; repeat safe_step; [].
    apply ParseProductionCons with (n := 1); repeat safe_step; [ fin | ].
    apply ParseHead; repeat safe_step; [].
    apply ParseTail, ParseTail, ParseTail, ParseHead; repeat safe_step.
  Qed.
End num_paren.

Section num_plus.
  Local Arguments append : simpl never.

  Local Ltac fin'0 tac :=
    repeat first [ idtac;
                   (lazymatch goal with
                   | [ |- parse_of_production _ ?s (Terminal _ :: _) ]
                     => apply ParseProductionCons with (n := 1)
                   | [ |- parse_of_production _ ?s (_ :: nil) ]
                     => apply ParseProductionCons with (n := String.length s)
                   | [ |- parse_of_production _ ?s (_ :: Terminal _ :: nil) ]
                     => apply ParseProductionCons with (n := String.length s - 1)
                   | _ => (apply ParseProductionCons with (n := 1); solve [ tac ])
                    end)
                 | idtac;
                   match goal with
                     | [ |- _ = _ ] => reflexivity
                     | [ |- is_true true ] => reflexivity
                   end
                 | apply ParseProductionNil
                 | apply ParseTerminal
                 | apply ParseNonTerminal
                 | progress simpl ].

  Local Ltac fin' := idtac; fin'0 fin'.

  Local Ltac fin :=
    repeat first [ progress fin'0 fin
                 | solve [ constructor (solve [ fin ]) ] ].

  Example plus_expr_parses_1 : parse_of_grammar "1+2+3+4+5"%string plus_expr_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead.
    match goal with
      | [ |- parse_of_production _ ?s _ ] => set (n := s)
    end.
    change n with ("1" ++ ("+" ++ ("2" ++ ("+" ++ ("3" ++ ("+" ++ ("4" ++ ("+" ++ "5"))))))))%string; subst n.
    simpl.
    fin'.
    apply ParseProductionCons with (n := 1); fin'.
    { apply ParseHead; fin. }
    apply ParseTail, ParseHead; fin'.
    apply ParseProductionCons with (n := 1); fin'.
    { apply ParseHead; fin. }
    apply ParseTail, ParseHead; fin'.
    apply ParseProductionCons with (n := 1); fin'.
    { apply ParseHead; fin. }
    apply ParseTail, ParseHead; fin'.
    apply ParseProductionCons with (n := 1); fin'.
    { apply ParseHead; fin. }
    apply ParseHead; fin.
  Defined.
End num_plus.

Section num_plus_paren.
  Local Arguments append : simpl never.

  Local Ltac fin :=
    repeat first [ idtac;
                   (lazymatch goal with
                   | [ |- parse_of_production _ ?s (Terminal _ :: _) ]
                     => apply ParseProductionCons with (n := 1)
                   | [ |- parse_of_production _ ?s (_ :: nil) ]
                     => apply ParseProductionCons with (n := String.length s)
                   | [ |- parse_of_production _ ?s (_ :: Terminal _ :: nil) ]
                     => apply ParseProductionCons with (n := String.length s - 1)
                    end)
                 | apply ParseProductionNil
                 | refine (ParseTerminal _ _ _)
                 | refine (ParseNonTerminal _ _)
                 | progress simpl
                 | solve [ constructor (solve [ fin ]) ] ].

  Example plus_paren_expr_parses_1 : parse_of_grammar "1+(2+3)+4+5"%string plus_expr_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead.
    match goal with
      | [ |- parse_of_production _ ?s _ ] => set (n := s)
    end.
    change n with (((("1"))) ++ ("+" ++ (("(" ++ ((((("2"))) ++ ("+" ++ ("3"))) ++ ")")) ++ ("+" ++ ("4" ++ ("+" ++ "5"))))))%string; subst n.
    apply ParseProductionCons with (n := 1); [ solve [ fin ] | simpl ].
    apply ParseProductionCons with (n := 1); [ solve [ fin ] | simpl ].
    apply ParseProductionCons with (n := 9); [ | solve [ fin ] ].
    constructor; simpl.
    apply ParseTail, ParseHead.
    apply ParseProductionCons with (n := 5); simpl.
    { constructor; simpl.
      apply ParseTail, ParseHead.
      apply ParseProductionCons with (n := 1); [ solve [ fin ] | simpl ].
      apply ParseProductionCons with (n := 3); simpl; [ | solve [ fin ] ].
      constructor; simpl.
      apply ParseTail, ParseHead; fin.
      apply ParseProductionCons with (n := 1); fin. }
    { apply ParseProductionCons with (n := 1); simpl; [ solve [ fin ] | ].
      apply ParseProductionCons with (n := 3); simpl; [ | solve [ fin ] ].
      constructor; simpl.
      apply ParseTail, ParseHead; fin.
      apply ParseProductionCons with (n := 1); fin. }
  Defined.
End num_plus_paren.
