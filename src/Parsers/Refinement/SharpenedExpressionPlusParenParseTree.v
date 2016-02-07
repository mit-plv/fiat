(** Sharpened ADT for #, +, () *)
Require Import Fiat.Parsers.Grammars.ExpressionNumPlusParen.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.SharpenedExpressionPlusParen.
Require Import Fiat.Parsers.Grammars.EvalGrammarTactics.

Definition parser_informative (str : Coq.Strings.String.string)
  : option (parse_of_item plus_expr_grammar str (NonTerminal (Start_symbol plus_expr_grammar))).
Proof.
  Time make_parser_informative ComputationalSplitter.
Defined.

Section eval.
  Fixpoint evalT_productions {str ps} (pt : parse_of plus_expr_grammar str ps) : Type
  with evalT_production {str p} (pt : parse_of_production plus_expr_grammar str p) : Type
  with evalT_item {str it} (pt : parse_of_item plus_expr_grammar str it) : Type.
  Proof.
    { handle_evalT_parse. }
    { handle_evalT_parse. }
    { handle_evalT_parse.
      { (* number case *)
        exact nat. }
      { (* pexpr case *)
        exact nat. }
      { (* expr case *)
        exact nat. } }
  Defined.

  (** Most of this is boilerplate.  It should be factored out, as it's
      mostly common to all gramamrs (but there's some funky dependent
      types stuff going on, which might be tricky to factor out. *)
  Fixpoint eval_productions {str ps} (pt : parse_of plus_expr_grammar str ps) : evalT_productions pt
  with eval_production {str p} (pt : parse_of_production plus_expr_grammar str p) : evalT_production pt
  with eval_item {str it} (pt : parse_of_item plus_expr_grammar str it) : evalT_item pt.
  Proof.
    { handle_eval_parse. }
    { handle_eval_parse. }
    { handle_eval_parse;
      (** Here's the grammar-specific part, which handles each type of production *)
      try match type of eval_production with
          | ({ ch' : ascii | ch' = ?ch } * unit)%type (* [0-9] *)
            => match goal with
               | [ Hcheck : is_true (?P ch), Hp : ?P = (fun ch0 => (Compare_dec.leb 48 (?f ch0) && Compare_dec.leb (?f ch0) 57)%bool) |- _ ]
                 => exact (f (proj1_sig (fst eval_production)) - 48 (* "0" *))
               end
          | (nat * unit)%type
            => match goal with
               | [ Hcheck : context["number" = "number"] |- _ ] (* "number" *)
                 => exact (fst eval_production)
               | [ Hcheck : context["pexpr" = "pexpr"] |- _ ] (* "pexpr" *)
                 => exact (fst eval_production)
               end
          end;
      try match type of eval_productions with
          | ({ ch' : ascii | ch' = ?ch } * (nat * unit))%type (* [0-9] "number" *)
            => match goal with
               | [ Hcheck : is_true (?P ch), Hp : ?P = (fun ch0 => (Compare_dec.leb 48 (?f ch0) && Compare_dec.leb (?f ch0) 57)%bool) |- _ ]
                 => exact (10 * (f (proj1_sig (fst eval_productions)) - 48 (* "0" *))
                           + fst (snd eval_productions))
               end
          | ({ch1 : ascii | ch1 = ?l} * (nat * ({ch2 : ascii | ch2 = ?r} * ())))%type (* "(" "expr" ")" *)
            => match goal with
               | [ Hcheckl : is_true (?Pl l), Hcheckr : is_true (?Pr r),
                                                        Hl : ?Pl = Equality.ascii_beq "("%char, Hr : ?Pr = Equality.ascii_beq ")"%char |- _ ]
                 => exact (fst (snd eval_productions))
               end
          | (nat * ({ch1 : ascii | ch1 = ?ch} * (nat * ())))%type (* "pexpr" "+" "expr" *)
            => match goal with
               | [ Hcheck : is_true (?P ch), HP : ?P = Equality.ascii_beq "+"%char |- _ ]
                 => exact (fst eval_productions + fst (snd (snd eval_productions)))
               end
          end. }
  Defined.
End eval.

Definition parser_eval (str : Coq.Strings.String.string)
  : option nat.
Proof.
  refine match parser_informative str with
         | Some pt => let n := eval_item pt in
                      Some _
         | None => None
         end.
  clearbody n.
  let nt' := match type of pt with parse_of_item _ _ ?nt => nt end in
  remember nt' as nt eqn:H in pt, n;
    compute in H.
  destruct_parses.
  exact n.
Defined.
