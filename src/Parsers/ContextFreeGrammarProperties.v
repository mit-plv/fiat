(** * Properties about Context Free Grammars *)
Require Import Parsers.StringLike Parsers.ContextFreeGrammar.

Set Implicit Arguments.

Delimit Scope string_like_scope with string_like.

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar CharType).

  Section definitions.
    Context (P : String -> String.string -> Type).

    Definition Forall_parse_of_item'
               (Forall_parse_of : forall {str pats} (p : parse_of String G str pats), Type)
               {str it} (p : parse_of_item String G str it)
      := match p return Type with
           | ParseTerminal x => unit
           | ParseNonTerminal name str p'
             => (P str name * Forall_parse_of p')%type
         end.

    Fixpoint Forall_parse_of {str pats} (p : parse_of String G str pats)
      := match p with
           | ParseHead str pat pats p'
             => Forall_parse_of_production p'
           | ParseTail _ _ _ p'
             => Forall_parse_of p'
         end
    with Forall_parse_of_production {str pat} (p : parse_of_production String G str pat)
         := match p return Type with
              | ParseProductionNil => unit
              | ParseProductionCons str pat strs pats p' p''
                => (Forall_parse_of_item' (@Forall_parse_of) p' * Forall_parse_of_production p'')%type
            end.

    Definition Forall_parse_of_item {str it} (p : parse_of_item String G str it)
      := @Forall_parse_of_item' (@Forall_parse_of) str it p.
  End definitions.

  Section expand.
    Context (P P' : String -> String.string -> Type)
            (f : forall str n, P str n -> P' str n).

    Definition expand_forall_parse_of_item'
               {Forall_parse_of : forall P {str pats} (p : parse_of String G str pats), Type}
               (expand : forall {str pats p}, @Forall_parse_of P str pats p -> @Forall_parse_of P' str pats p)
               {str it p}
    : @Forall_parse_of_item' P (@Forall_parse_of P) str it p
      -> @Forall_parse_of_item' P' (@Forall_parse_of P') str it p.
    Proof.
      destruct p; simpl.
      { exact (fun x => x). }
      { intro ab.
        exact (f (fst ab), expand _ _ _ (snd ab)). }
    Defined.

    Global Arguments expand_forall_parse_of_item' : simpl never.

    Fixpoint expand_forall_parse_of {str pats} (p : parse_of String G str pats)
    : Forall_parse_of P p -> Forall_parse_of P' p
      := match p return Forall_parse_of P p -> Forall_parse_of P' p with
           | ParseHead str pat pats p'
             => expand_forall_parse_of_production p'
           | ParseTail _ _ _ p'
             => expand_forall_parse_of p'
         end
    with expand_forall_parse_of_production {str pat} (p : parse_of_production String G str pat)
         : Forall_parse_of_production P p -> Forall_parse_of_production P' p
         := match p return Forall_parse_of_production P p -> Forall_parse_of_production P' p with
              | ParseProductionNil => fun x => x
              | ParseProductionCons str pat strs pats p' p''
                => fun ab => (expand_forall_parse_of_item' (@expand_forall_parse_of) (fst ab),
                              expand_forall_parse_of_production p'' (snd ab))
            end.

    Definition expand_forall_parse_of_item {str it} (p : parse_of_item String G str it)
      := @expand_forall_parse_of_item' _ (@expand_forall_parse_of) str it p.
  End expand.
End cfg.
