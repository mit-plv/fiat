Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.

Ltac handle_evalT_parse :=
  lazymatch goal with
  | [ evalT_productions : forall str ps, parse_of _ str ps -> Type,
        evalT_production : forall str p, parse_of_production _ str p -> Type,
        evalT_item : forall str it, parse_of_item _ str it -> Type |- Type ]
    => idtac;
       lazymatch goal with
       | [ pt : parse_of _ _ _ |- Type ]
         => refine match pt with
                   | ParseHead pat pats pt => evalT_production _ pat pt
                   | ParseTail pat pats pt => evalT_productions _ pats pt
                   end
       | [ pt : parse_of_production _ _ _ |- Type ]
         => refine match pt with
                   | ParseProductionNil pf => unit
                   | ParseProductionCons n it its pit pits => (evalT_item _ it pit * evalT_production _ its pits)%type
                   end
       | [ pt : parse_of_item _ _ _ |- Type ]
         => refine match pt with
                   | ParseTerminal ch' _ _ _ => { ch : Ascii.ascii | ch = ch' }
                   | ParseNonTerminal nt Hin pnt => _
                   end;
            lazymatch goal with
            | [ Hin : List.In _ ?nts |- _ ]
              => let nts' := (eval compute in nts) in
                 change nts with nts' in Hin;
                 apply (Equality.list_in_lb (@Equality.string_lb)) in Hin;
                 simpl in Hin;
                 let HinT := fresh "HinT" in
                 let v := match type of Hin with ?v = _ => v end in
                 pose v as HinT;
                 repeat match (eval unfold HinT in HinT) with
                        | context G[orb (orb ?x ?y) ?z]
                          => let G' := context G[orb x (orb y z)] in
                             clear HinT;
                             pose G' as HinT
                        end;
                 repeat try match (eval unfold HinT in HinT) with
                            | (orb (?f ?a ?b) _)
                              => destruct (f a b); [ clear Hin HinT; pose (a = b) | simpl in Hin, HinT ]
                            end
            end
       end
  end.

Ltac destruct_parses :=
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
Ltac handle_eval_parse :=
  lazymatch goal with
  | [ eval_productions : (forall str ps (pt : parse_of _ str ps), @?evalT_productions str ps pt),
                         eval_production : (forall str p (pt : parse_of_production _ str p), @?evalT_production str p pt),
                                           eval_item : (forall str it (pt : parse_of_item _ str it), @?evalT_item str it pt)
      |- _ ]
    => idtac;
       lazymatch goal with
       | [ pt : parse_of _ _ _ |- _ ]
         => refine match pt return evalT_productions _ _ pt with
                   | ParseHead pat pats pt => eval_production _ pat pt
                   | ParseTail pat pats pt => eval_productions _ pats pt
                   end
       | [ pt : parse_of_production _ _ _ |- _ ]
         => refine match pt return evalT_production _ _ pt with
                   | ParseProductionNil pf => tt
                   | ParseProductionCons n it its pit pits => (eval_item _ it pit, eval_production _ its pits)
                   end
       | [ pt : parse_of_item _ _ _ |- _ ]
         => refine match pt return evalT_item _ _ pt with
                   | ParseTerminal ch _ _ _ => exist _ ch eq_refl
                   | ParseNonTerminal nt Hin pnt => _
                   end;
            simpl;
            lazymatch goal with
            | [ |- context[Equality.list_in_lb (@Equality.string_lb) ?Hin] ]
              => let f := match goal with |- context[?f Hin] => f end in
                 generalize (f Hin); clear Hin; intro Hin;
                 simpl in Hin;
                 let HinT := fresh "HinT" in
                 let v := match type of Hin with ?v = _ => v end in
                 pose v as HinT;
                 repeat match (eval unfold HinT in HinT) with
                        | context G[orb (orb ?x ?y) ?z]
                          => let G' := context G[orb x (orb y z)] in
                             clear HinT;
                             pose G' as HinT
                        end;
                 (** Pattern match on the parse trees until the types simplify *)
                 repeat match (eval unfold HinT in HinT) with
                        | (orb (?f ?a ?b) _)
                          => let H := fresh in
                             destruct (f a b) eqn:H;
                             [ try clear Hin HinT;
                               apply Equality.string_bl in H
                             | simpl in Hin, HinT; clear H ]
                        end;
                 try apply Equality.string_bl in Hin;
                 try clear HinT;
                 lazymatch goal with
                 | [ pnt : parse_of _ _ _, H : _ = ?nt :> string |- _ ]
                   => is_var nt;
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
                      destruct_parses
                 end
            end
       end
  end.
