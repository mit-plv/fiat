(** Sharpened ADT for #, +, () *)
Require Import Fiat.Parsers.Grammars.ExpressionNumPlusParen.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.SharpenedExpressionPlusParen.

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
    { refine match pt with
             | ParseHead pat pats pt => evalT_production _ pat pt
             | ParseTail pat pats pt => evalT_productions _ pats pt
             end. }
    { refine match pt with
             | ParseProductionNil pf => unit
             | ParseProductionCons n it its pit pits => (evalT_item _ it pit * evalT_production _ its pits)%type
             end. }
    { refine match pt with
             | ParseTerminal ch' _ _ _ => { ch : Ascii.ascii | ch = ch' }
             | ParseNonTerminal nt Hin pnt => _
             end.
      let nts := match type of Hin with List.In _ ?ls => ls end in
      let nts' := (eval compute in nts) in
      change nts with nts' in Hin.
      apply (Equality.list_in_lb (@Equality.string_lb)) in Hin.
      simpl in Hin.
      let v := match type of Hin with ?v = _ => v end in
      pose v as HinT.
      repeat match (eval unfold HinT in HinT) with
             | context G[orb (orb ?x ?y) ?z]
               => let G' := context G[orb x (orb y z)] in
                  clear HinT;
                    pose G' as HinT
             end.
      repeat try match (eval unfold HinT in HinT) with
                 | (orb (?f ?a ?b) _)
                   => destruct (f a b); [ clear Hin HinT; pose (a = b) | simpl in Hin, HinT ]
                 end.
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
    { refine match pt return evalT_productions pt with
             | ParseHead pat pats pt => eval_production _ pat pt
             | ParseTail pat pats pt => eval_productions _ pats pt
             end. }
    { refine match pt return evalT_production pt with
             | ParseProductionNil pf => tt
             | ParseProductionCons n it its pit pits => (eval_item _ it pit, eval_production _ its pits)
             end. }
    { refine match pt return evalT_item pt with
             | ParseTerminal ch _ _ _ => exist _ ch eq_refl
             | ParseNonTerminal nt Hin pnt => _
             end.
      simpl.
      let nts := match type of Hin with List.In _ ?ls => ls end in
      let nts' := (eval compute in nts) in
      change nts with nts' in Hin.
      generalize (Equality.list_in_lb (@Equality.string_lb) Hin); clear Hin; intro Hin.
      simpl in Hin.
      let v := match type of Hin with ?v = _ => v end in
      pose v as HinT.
      repeat match (eval unfold HinT in HinT) with
             | context G[orb (orb ?x ?y) ?z]
               => let G' := context G[orb x (orb y z)] in
                  clear HinT;
                    pose G' as HinT
             end.
      (** Pattern match on the parse trees until the types simplify *)
      repeat try match (eval unfold HinT in HinT) with
                 | (orb (?f ?a ?b) _)
                   => let H := fresh in
                      destruct (f a b) eqn:H;
                        [ try clear Hin HinT;
                          apply Equality.string_bl in H
                        | simpl in Hin, HinT; clear H ]
                 end;
        try apply Equality.string_bl in Hin;
        try clear HinT;
        subst nt;
        simpl in pnt;
        cbv [list_to_productions option_rect fst List.find] in pnt;
        repeat match type of pnt with
               | context[Equality.string_beq ?x ?y]
                 => let v := (eval compute in (Equality.string_beq x y)) in
                    change (Equality.string_beq x y) with v in pnt
               end;
        cbv [snd] in pnt;
        let ps' := match type of pnt with parse_of _ _ ?ps => ps end in
        remember ps' as ps eqn:H in pnt;
          (destruct pnt as [p ps ppt|?? ppps];
           [ specialize (eval_production _ _ ppt)
           | specialize (eval_productions _ _ ppps) ]);
          repeat match goal with
                 | [ H : nil = cons _ _ |- _ ] => exfalso; clear -H; abstract congruence
                 | [ H : cons _ _ = nil |- _ ] => exfalso; clear -H; abstract congruence
                 | [ H : Terminal _ = NonTerminal _ |- _ ] => exfalso; clear -H; abstract congruence
                 | [ H : NonTerminal _ = Terminal _ |- _ ] => exfalso; clear -H; abstract congruence
                 | _ => progress simpl in *
                 | [ H : cons ?x _ = cons _ _ |- _ ]
                   => pose proof (f_equal (@List.hd _ x) H);
                        pose proof (f_equal (@List.tl _) H);
                        clear H
                 | [ H : Terminal _ = Terminal _ |- _ ] => inversion H; clear H
                 | [ H : NonTerminal _ = NonTerminal _ |- _ ] => inversion H; clear H
                 | [ p : parse_of_production _ _ ?v, H : ?v::_ = cons _ _ |- _ ] => destruct p
                 | [ p : parse_of_production _ _ ?v, H : ?v = cons _ _ |- _ ]    => destruct p
                 | [ p : parse_of_production _ _ ?v, H : ?v = nil |- _ ]         => destruct p
                 | [ p : parse_of _ _ ?v, H : ?v = cons _ _ |- _ ]               => destruct p
                 | [ p : parse_of _ _ ?v, H : ?v = nil |- _ ]                    => destruct p
                 | [ p : parse_of_item _ _ ?v, H : ?v = Terminal _ |- _ ]        => destruct p
                 | [ p : parse_of_item _ _ ?v, H : ?v = NonTerminal _ |- _ ]     => destruct p
                 | [ H : ?x = ?x |- _ ] => clear H
                 end;
          repeat match goal with
                 | [ H : ?nt = _ :> string |- _ ] => is_var nt; subst nt; simpl in *
                 end;
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
  repeat match goal with
         | [ H : nil = cons _ _ |- _ ] => exfalso; clear -H; abstract congruence
         | [ H : cons _ _ = nil |- _ ] => exfalso; clear -H; abstract congruence
         | [ H : Terminal _ = NonTerminal _ |- _ ] => exfalso; clear -H; abstract congruence
         | [ H : NonTerminal _ = Terminal _ |- _ ] => exfalso; clear -H; abstract congruence
         | _ => progress simpl in *
         | [ H : cons ?x _ = cons _ _ |- _ ]
           => pose proof (f_equal (@List.hd _ x) H);
                pose proof (f_equal (@List.tl _) H);
                clear H
         | [ H : Terminal _ = Terminal _ |- _ ] => inversion H; clear H
         | [ H : NonTerminal _ = NonTerminal _ |- _ ] => inversion H; clear H
         | [ p : parse_of_production _ _ ?v, H : ?v::_ = cons _ _ |- _ ] => destruct p
         | [ p : parse_of_production _ _ ?v, H : ?v = cons _ _ |- _ ]    => destruct p
         | [ p : parse_of_production _ _ ?v, H : ?v = nil |- _ ]         => destruct p
         | [ p : parse_of _ _ ?v, H : ?v = cons _ _ |- _ ]               => destruct p
         | [ p : parse_of _ _ ?v, H : ?v = nil |- _ ]                    => destruct p
         | [ p : parse_of_item _ _ ?v, H : ?v = Terminal _ |- _ ]        => destruct p
         | [ p : parse_of_item _ _ ?v, H : ?v = NonTerminal _ |- _ ]     => destruct p
         | [ H : ?x = ?x |- _ ] => clear H
         end;
    repeat match goal with
           | [ H : ?nt = _ :> string |- _ ] => is_var nt; subst nt; simpl in *
           end.
  exact n.
Defined.
