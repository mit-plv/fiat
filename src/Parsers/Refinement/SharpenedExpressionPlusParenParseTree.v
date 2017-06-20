(** Sharpened ADT for #, +, () *)
Require Import Fiat.Parsers.Grammars.ExpressionNumPlusParen.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.SharpenedExpressionPlusParen.
Require Import Fiat.Parsers.Grammars.EvalGrammarTactics.

Definition parser_informative_opaque (str : Coq.Strings.String.string)
  : option (parse_of_item plus_expr_grammar str (NonTerminal (Start_symbol plus_expr_grammar))).
Proof.
  Time make_parser_informative_opaque ComputationalSplitter.
Defined.

Definition parser_informative (str : Coq.Strings.String.string)
  : option (@simple_parse_of_item Ascii.ascii).
Proof.
  Time make_parser_informative ComputationalSplitter.
Defined.

Section eval.
  Local Open Scope N_scope.
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
               | [ Hcheck : is_true (?P ch), Hp : ?P = (fun ch0 => (BinNat.N.leb 48 (?f ch0) && BinNat.N.leb (?f ch0) 57)%bool) |- _ ]
                 => exact (BinNat.N.to_nat (f (proj1_sig (fst eval_production)) - 48 (* "0" *)))
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
               | [ Hcheck : is_true (?P ch), Hp : ?P = (fun ch0 => (BinNat.N.leb 48 (?f ch0) && BinNat.N.leb (?f ch0) 57)%bool) |- _ ]
                 => exact (N.to_nat (10 * (f (proj1_sig (fst eval_productions)) - 48 (* "0" *)))
                           + fst (snd eval_productions))%nat
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
                 => exact (fst eval_productions + fst (snd (snd eval_productions)))%nat
               end
          end. }
  Defined.
End eval.

Definition parser_eval_opaque (str : Coq.Strings.String.string)
  : option nat.
Proof.
  refine match parser_informative_opaque str with
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

Section evals.
  (* grammar_of_pregrammar
  [[["expr" ::== "pexpr" || ("pexpr" "+") "expr";;
  "pexpr" ::== "number" || ("(" "expr") ")";;
  "number" ::== [0-9] || [0-9] "number"]]] *)
  Fixpoint sevalT_productions (pt : @simple_parse_of Ascii.ascii) : Type
  with sevalT_production (pt : @simple_parse_of_production Ascii.ascii) : Type
  with sevalT_item (pt : @simple_parse_of_item Ascii.ascii) : Type.
  Proof.
    { refine match pt with
               | SimpleParseHead pt' => sevalT_production pt'
               | SimpleParseTail pt' => sevalT_productions pt'
             end. }
    { refine match pt return Type with
               | SimpleParseProductionNil => unit
               | SimpleParseProductionCons p ps => (sevalT_item p * sevalT_production ps)%type
             end. }
    { refine match pt return Type with
               | SimpleParseTerminal ch => unit (*{ ch' : _ | ch' = ch }*)
               | SimpleParseNonTerminal _ _ => nat
             end. }
  Defined.

  Definition impossible {T} : T -> nat.
  Proof.
    intro; exact 0.
  Qed.

  Fixpoint seval_productions (pt : @simple_parse_of Ascii.ascii) : sevalT_productions pt
  with seval_production (pt : @simple_parse_of_production Ascii.ascii) : sevalT_production pt
  with seval_item (pt : @simple_parse_of_item Ascii.ascii) : sevalT_item pt.
  Proof.
    { destruct pt; simpl; eauto with nocore. }
    { destruct pt; simpl; eauto using tt, pair with nocore. }
    { destruct pt as [ch|nt pt]; simpl.
      { eexists; reflexivity. }
      { specialize (seval_productions pt).
        revert seval_productions.
        destruct (string_dec nt "number");
          [
          | destruct (string_dec nt "pexpr");
            [
            | destruct (string_dec nt "expr");
              [
              | exact impossible ] ] ].
        { (* "number" ::== [0-9] || [0-9] "number"]]] *)
          refine match pt return sevalT_productions pt -> nat with
                   | SimpleParseHead
                       (SimpleParseTerminal ch::[])
                     (* [0-9] *)
                     => fun _ => N.to_nat (opt.N_of_ascii ch - 48) (* opt.nat_of_ascii "0" is 48 *)
                   | SimpleParseTail
                       (SimpleParseHead
                          (SimpleParseTerminal ch::SimpleParseNonTerminal number pt'::[]))
                     (* [0-9] "number" *)
                     => fun v
                        => (N.to_nat (opt.N_of_ascii ch - 48 (* opt.nat_of_ascii "0" is 48 *))
                            * 10
                            + fst (snd v))%nat
                   | _ => impossible
                 end. }
        { (* "pexpr" ::== "number" || "(" "expr" ")";; *)
          refine match pt return sevalT_productions pt -> nat with
                   | SimpleParseHead
                       (SimpleParseNonTerminal number pt'::[])
                     (* "number" *)
                     => fst
                   | SimpleParseTail
                       (SimpleParseHead
                          (SimpleParseTerminal ch::SimpleParseNonTerminal expr pt'::SimpleParseTerminal ch'::[]))
                     (* "(" "expr" ")" *)
                     => fun v => fst (snd v)
                   | _ => impossible
                 end. }
        { (* "expr" ::== "pexpr" || "pexpr" "+" "expr" *)
          refine match pt return sevalT_productions pt -> nat with
                   | SimpleParseHead
                       (SimpleParseNonTerminal pexpr pt'::[])
                     (* "pexpr" *)
                     => fst
                   | SimpleParseTail
                       (SimpleParseHead
                          (SimpleParseNonTerminal pexpr n1::SimpleParseTerminal plus::SimpleParseNonTerminal expr n2::[]))
                     (* "pexpr" "+" "expr" *)
                     => fun v => fst v + fst (snd (snd v))
                   | _ => impossible
                 end. } } }
  Defined.
End evals.

Definition parser_eval (str : Coq.Strings.String.string)
  : option nat.
Proof.
  refine match parser_informative str with
         | Some (SimpleParseNonTerminal nt pt)
           => let n := seval_item (SimpleParseNonTerminal nt pt) in
              Some n
         | Some (SimpleParseTerminal _) => None
         | None => None
         end.
Defined.

Check let n := 3 in eq_refl (Some n) <: parser_eval "(1+1)+1" = Some n.
Check let n := 5 in eq_refl (Some n) <: parser_eval "((1+1)+(1+1))+1" = Some n.
Check let n := 55 in eq_refl (Some n) <: parser_eval "(((((55)))))" = Some n.
