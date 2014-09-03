(** * Definition of a [comp]-based non-computational CFG parser *)
Require Import Coq.Lists.List Coq.Program.Program.
Require Import Parsers.ContextFreeGrammar Parsers.Specification.
Require Import Common.

Set Implicit Arguments.
(*(** We implement a generic recursive descent parser.  We parameterize
    over a number of parameters:

    - [T : Type] - the type of results of successful parsing.
      Parameterizing over this allows, e.g., higher-order parsing.

      TODO?: generalize this to use continuations instead, so we can
      do monadic side-effects when parsing.

    - [aggregate : String → T → String → T → T] - takes the results of
      two successful adjacent parses and combines them.

    - [pick_parses : String → nonterminal → list (list String)] - A
      non-terminal is a list of patterns.  This function will break up
      a string into a list of possible splits; a split is an
      assignment of a part of the string to each pattern.


    The basic idea is that

FIXME *)*)
Infix "=s" := (@dec_eq _ _) (at level 70, right associativity) : string_like_scope.
Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context CharType (String : string_like CharType) (G : grammar CharType).
  Context (T : String -> nonterminal CharType -> Type)
          (aggregate : forall s1 nt1, T s1 nt1 -> forall s2 nt2, T s2 nt2 -> T (s1 ++ s2)%string_like (nt1 ++ nt2)%list)
          (T_reverse_lookup : forall str name, T str (Lookup G name) -> T str [ [ NonTerminal _ name ] ]).
  Context (pick_parses : String -> nonterminal CharType -> list (list String)).
  Context (make_leaf : forall c, T [[c]]%string_like [ [ Terminal c ] ]).
  Context (make_empty : T (Empty _) [ [ ] ]).

  Section parts.
    Local Ltac t' :=
      idtac;
      match goal with
        | _ => progress subst
        | _ => exact id
        | _ => assumption
        | [ H : ?x <> ?x |- _ ] => solve [ destruct (H eq_refl) ]
        | [ H : parse_of_item _ _ _ _ |- _ ] => inversion H; clear H
        | [ H : parse_of_pattern _ _ _ _ |- _ ] => inversion H; clear H
      end.

    Class by_t' T := make_by_t' : T.
    Hint Extern 0 (by_t' _) => unfold by_t'; solve [ repeat t' ] : typeclass_instances.

    Local Ltac t :=
      repeat match goal with
               | [ |- False ] => clear abstract by_t' || fail 1
               | _ => progress t'
             end.


    Section item.
      Variable parse_nonterminal : forall str nt, (T str nt * parse_of _ G str nt)
                                                  + (parse_of _ G str nt -> False).

      Definition parse_item str it : (T str [ [ it ] ] * parse_of_item _ G str it)
                                     + (parse_of_item _ G str it -> False).
      Proof.
        refine (match it with
                  | Terminal ch => match [[ch]] =s str with
                                     | left pf => inl (_ (make_leaf ch), _ (ParseTerminal _ _ ch))
                                     | right _ => inr (fun H => _)
                                   end
                  | NonTerminal name => match parse_nonterminal str (Lookup G name) with
                                          | inl (t, parse) => inl (T_reverse_lookup _ t, ParseNonTerminal _ parse)
                                          | inr pf => inr (fun H => pf _)
                                        end
                end);
        t.
      Defined.
    End item.

    Section pattern.
      Variable parse_nonterminal : forall str nt, (T str nt * parse_of _ G str nt)
                                                  + (parse_of _ G str nt -> False).

      Fixpoint parse_pattern str pat : (T str [ pat ] * parse_of_pattern _ G str pat)
                                       + (parse_of_pattern _ G str pat -> False).
      Proof.
        refine (match pat with
                  | nil => match Empty _ =s str with
                             | left pf => inl (_ make_empty, _ (ParsePatternNil _ _))
                             | right _ => inr (fun H => _)
                           end
                  | pat'::pats' => _
                end);
        t.



      Definition parse_item str it : (T str [ [ it ] ] * parse_of_item _ G str it)
                                     + (parse_of_item _ G str it -> False).
      Proof.
        refine (match it with
                  | Terminal ch => match [[ch]] =s str with
                                     | left pf => inl (_ (make_leaf ch), _ (ParseTerminal _ _ ch))
                                     | right _ => inr (fun H => _)
                                   end
                  | NonTerminal name => match parse_nonterminal str (Lookup G name) with
                                          | inl (t, parse) => inl (T_reverse_lookup _ t, ParseNonTerminal _ parse)
                                          | inr pf => inr (fun H => pf _)
                                        end
                end);
        t.
      Defined.
    with parse_of_pattern : String -> pattern -> Type :=
    | ParsePatternNil : parse_of_pattern (Empty _) nil
    | ParsePatternCons : forall str pat strs pats,
                           parse_of_item str pat
                           -> parse_of_pattern strs pats
                           -> parse_of_pattern (str ++ strs) (pat::pats)

      (** We


        inversion H.

    Next Obligation.

    Proof.
      destruct it as [c|]; simpl.
      {
      intros str it.
