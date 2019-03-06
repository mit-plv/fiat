Require Import Coq.Strings.String Coq.Strings.Ascii Coq.Lists.List.
Require Import Fiat.Parsers.ContextFreeGrammar.Core Fiat.Parsers.ContextFreeGrammar.Notations.
Require Import Fiat.Parsers.StringLike.String.

Require Import Fiat.Parsers.Grammars.ABStar.
Require Import Fiat.Parsers.Grammars.ExpressionNumPlusParen.
Require Import Fiat.Parsers.Grammars.ExpressionParen.
Require Import Fiat.Parsers.Grammars.StringLiteral.
Require Import Fiat.Parsers.Grammars.JSComment.

Local Arguments Equality.ascii_beq !_ !_.
Local Arguments Equality.string_beq !_ !_.
Local Arguments list_to_productions / _ _ _ _.
Local Arguments ascii_of_nat !_ / .
Local Arguments ascii_of_pos !_ / .

Local Notation LF := (ascii_of_nat 10).
Local Notation CR := (ascii_of_nat 13).
Local Notation TAB := (ascii_of_nat 9).
Local Notation SPACE := " "%char.

Local Coercion test_string_of_ascii (ch : ascii) := String.String ch EmptyString.
Global Arguments test_string_of_ascii / _.

Local Notation newline := (String.String LF EmptyString).

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
   | [ |- parse_of_production _ ?s (_ :: Terminal _ :: Terminal _ :: nil) ]
     => apply ParseProductionCons with (n := StringLike.length s - 2)
   | [ |- parse_of_production _ _ nil ]
     => apply ParseProductionNil
   | [ |- parse_of_item _ _ (Terminal _) ]
     => (refine (ParseTerminal _ _ _ _ _ _);
          simpl;
          erewrite ?Equality.ascii_lb by reflexivity;
          reflexivity)
   | [ |- parse_of_item _ _ (Terminal _) ]
     => (refine (ParseTerminal _ _ _ _ _ _);
          simpl;
          [ .. | erewrite ?Equality.ascii_lb by reflexivity ];
          reflexivity)
   | [ |- parse_of_item _ _ (NonTerminal _) ]
     => apply ParseNonTerminal
   | [ |- parse_of _ _ (_::nil) ] => apply ParseHead
   | [ |- parse_of _ ?s (nil::_) ]
     => first [ unify s ""%string; apply ParseHead
              | apply ParseTail ]
    | [ |- parse_of _ (String.String ?ch _) (((Terminal (Equality.ascii_beq ?ch')):: _)::_) ]
      => first [ unify ch ch'; fail 1
               | apply ParseTail ]
   | [ |- is_true (is_char (take 1 _) _) ] => apply get_0
   | _ => progress simpl
   | _ => tauto
   end).

Section ab_star.
  Example ab_star_parses_empty : parse_of_grammar ""%string ab_star_grammar.
  Proof.
    hnf; simpl.
    repeat constructor.
  Defined.

  Example ab_star_parses_ab : parse_of_grammar "ab"%string ab_star_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead; repeat safe_step.
  Defined.

  Example ab_star_parses_abab : parse_of_grammar "abab"%string ab_star_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead; repeat safe_step.
  Defined.
End ab_star.

Section num_paren.
  Example paren_expr_parses_1 : parse_of_grammar ((*of_string*) ((*list_of_string*) "(((123)))"%string)) paren_expr_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail, ParseHead; repeat safe_step; [].
    apply ParseTail, ParseHead; repeat safe_step; [].
    apply ParseTail, ParseHead; repeat safe_step; [].
    apply ParseHead; repeat safe_step; [].
    apply ParseTail, ParseHead; repeat safe_step; [].
    apply ParseTail, ParseHead; repeat safe_step; [].
    apply ParseHead; repeat safe_step.
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
                 | refine (ParseTerminal _ _ _ _ _ _);
                   simpl; erewrite ?Equality.ascii_lb by reflexivity; reflexivity
                 | apply ParseNonTerminal
                 | progress simpl
                 | tauto ].

  Local Ltac fin' := idtac; fin'0 fin'.

  Local Ltac fin :=
    repeat first [ progress fin'0 fin
                 | solve [ constructor; solve [ fin ] ] ].

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
    { fin. }
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
                 | refine (ParseTerminal _ _ _ _ _ _);
                   simpl; erewrite ?Equality.ascii_lb by reflexivity; reflexivity
                 | refine (ParseNonTerminal _ _)
                 | progress simpl
                 | solve [ constructor; solve [ fin ] ] ].

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
    constructor; simpl; try tauto.
    apply ParseTail, ParseHead.
    apply ParseProductionCons with (n := 5); simpl.
    { constructor; simpl; try tauto.
      apply ParseTail, ParseHead.
      apply ParseProductionCons with (n := 1); [ solve [ fin ] | simpl ].
      apply ParseProductionCons with (n := 3); simpl; [ | solve [ fin ] ].
      constructor; simpl; try tauto.
      apply ParseTail, ParseHead; fin.
      apply ParseProductionCons with (n := 1); fin. }
    { apply ParseProductionCons with (n := 1); simpl; [ solve [ fin ] | ].
      apply ParseProductionCons with (n := 3); simpl; [ | solve [ fin ] ].
      constructor; simpl; try tauto.
      apply ParseTail, ParseHead; fin.
      apply ParseProductionCons with (n := 1); fin. }
  Defined.
End num_plus_paren.

Section string_literal.
  Example string_literal_parses_empty : parse_of_grammar """"""%string string_grammar.
  Proof.
    hnf; simpl.
    repeat safe_step.
  Qed.

  Example string_literal_parses_escapes : parse_of_grammar """\""\\a"""%string string_grammar.
  Proof.
    hnf; simpl.
    apply ParseHead; repeat safe_step; [].
    apply ParseHead; repeat safe_step; [].
    apply ParseProductionCons with (n := 1); repeat safe_step.
    apply ParseHead; repeat safe_step; [].
    apply ParseProductionCons with (n := 1); repeat safe_step.
    apply ParseProductionCons with (n := 1); repeat safe_step.
  Qed.
End string_literal.

Section js_comment.
  Example js_comment_parses_singleline : parse_of_grammar ("// asdf // /* */ /* adfs" ++ newline)%string js_comment_grammar.
  Proof.
    hnf; simpl.
    apply ParseHead; repeat safe_step.
  Qed.

  Example js_comment_parses_multiple : parse_of_grammar "/******/"%string js_comment_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail; repeat safe_step.
    apply ParseTail, ParseHead; repeat safe_step.
    apply ParseTail, ParseHead; repeat safe_step.
  Qed.

  Example js_comment_parses_multiline : parse_of_grammar ("/* x *" ++ newline ++ "a // as/*" ++ newline ++ "a* / */")%string js_comment_grammar.
  Proof.
    hnf; simpl.
    apply ParseTail; repeat safe_step.
    apply ParseTail; repeat safe_step.
    apply ParseHead; repeat safe_step.
    apply ParseTail, ParseHead; repeat safe_step.
    apply ParseTail, ParseHead; repeat safe_step.
  Qed.
End js_comment.
