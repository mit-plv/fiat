(** * Definition of a function that tears down a simple parse tree and computes a value *)

Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.GenericBaseTypes.
Require Import Fiat.Parsers.GenericRecognizer.

Section recursive_descent_parser.
  Context {Char T} (G : pregrammar_with_actions Char T).

  Definition impossible {A} : option A. Proof using Type. exact None. Qed.

  Definition evaluate_item'
             (evaluate_productions : simple_parse_of Char -> rproductions_with_actions Char T -> option T)
             (pit : simple_parse_of_item Char)
    : option match pit with
             | SimpleParseTerminal _ => Char
             | SimpleParseNonTerminal _ _ => T
             end
    := match pit return option match pit with
                               | SimpleParseTerminal _ => Char
                               | SimpleParseNonTerminal _ _ => T
                               end
       with
       | SimpleParseTerminal ch => Some ch
       | SimpleParseNonTerminal nt p'
         => evaluate_productions p' (list_to_productions nil (pregrammar_arproductions G) nt)
       end.

  Definition evaluate_ritem'
             (evaluate_productions : simple_parse_of Char -> rproductions_with_actions Char T -> option T)
             (pit : simple_parse_of_item Char)
             (it : Reflective.ritem Char)
    : option match it with
             | Reflective.RTerminal _ => Char
             | Reflective.RNonTerminal _ => T
             end
    := match pit, it as x
             return option match pit with
                           | SimpleParseTerminal _ => Char
                           | SimpleParseNonTerminal _ _ => T
                           end
                    -> option match x with
                              | Reflective.RTerminal _ => Char
                              | Reflective.RNonTerminal _ => T
                              end
       with
       | SimpleParseTerminal ch, Reflective.RTerminal ch'
         => (* assert [(interp_to_predicate ch') ch = true] *)
         fun x => x
       | SimpleParseNonTerminal nt p', Reflective.RNonTerminal nt'
         => if Equality.string_beq nt nt'
            then fun x => x
            else fun _ => impossible
       | SimpleParseTerminal _, Reflective.RNonTerminal _
       | SimpleParseNonTerminal _ _, Reflective.RTerminal _
         => fun _ => None
       end (evaluate_item' evaluate_productions pit).


  Fixpoint evaluate_productions (p : simple_parse_of Char) (acts : rproductions_with_actions Char T) {struct p} : option T
  with evaluate_production (p : simple_parse_of_production Char) (act : rproduction_with_action Char T) {struct p} : option T.
  Proof.
    { refine match p, acts with
             | SimpleParseHead p', act::acts => evaluate_production p' act
             | SimpleParseTail ps', act::acts => evaluate_productions ps' acts
             | _, nil => None
             end%list. }
    { refine (match p, projT1 act as pat return action_of_rproduction T pat -> option T with
              | SimpleParseProductionNil, nil => @Some _
              | SimpleParseProductionCons it its, x::xs
                => fun act
                   => let v := evaluate_ritem' evaluate_productions it x in
                      match v with
                      | Some v => evaluate_production its (existT _ xs (act v))
                      | None => None
                      end
              | SimpleParseProductionNil, _::_
              | SimpleParseProductionCons _ _, nil
                => fun _ => None
              end%list (projT2 act)). }
  Defined.

  Definition evaluate_item
             (pit : simple_parse_of_item Char)
    : option match pit with
             | SimpleParseTerminal _ => Char
             | SimpleParseNonTerminal _ _ => T
             end
    := evaluate_item' evaluate_productions pit.
End recursive_descent_parser.
