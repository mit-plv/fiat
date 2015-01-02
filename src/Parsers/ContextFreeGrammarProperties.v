(** * Properties about Context Free Grammars *)
Require Import Coq.Strings.String.
Require Import Parsers.StringLike Parsers.ContextFreeGrammar.

Set Implicit Arguments.

Delimit Scope string_like_scope with string_like.

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar CharType)
          (P : string -> Type).

  Definition Forall_parse_of_item'
             (Forall_parse_of : forall {str pats} (p : parse_of String G str pats), Type)
             {str it} (p : parse_of_item String G str it)
    := match p return Type with
         | ParseTerminal x => unit
         | ParseNonTerminal name str p'
           => (P name * Forall_parse_of p')%type
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
End cfg.
