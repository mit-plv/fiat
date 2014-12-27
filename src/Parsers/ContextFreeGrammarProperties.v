(** * Properties about Context Free Grammars *)
Require Import Parsers.StringLike Parsers.ContextFreeGrammar.

Set Implicit Arguments.

Delimit Scope string_like_scope with string_like.

Section cfg.
  Context CharType (String : string_like CharType) (G : grammar CharType)
          (P : productions CharType -> Type).

  Fixpoint Forall_parse_of {str pats} (p : parse_of String G str pats)
    := match p with
         | ParseHead str pat pats p'
           => Forall_parse_of_production p'
         | ParseTail _ _ _ p'
           => Forall_parse_of p'
       end
  with Forall_parse_of_production {str pat} (p : parse_of_production String G str pat)
       := let Forall_parse_of_item {str it} (p : parse_of_item String G str it)
              := match p return Type with
                   | ParseTerminal x => unit
                   | ParseNonTerminal name str p'
                     => (P (Lookup G name) * Forall_parse_of p')%type
                 end in
          match p return Type with
            | ParseProductionNil => unit
            | ParseProductionCons str pat strs pats p' p''
              => (Forall_parse_of_item p' * Forall_parse_of_production p'')%type
          end.

  Definition Forall_parse_of_item {str it} (p : parse_of_item String G str it)
    := match p return Type with
         | ParseTerminal x => unit
         | ParseNonTerminal name str p'
           => (P (Lookup G name) * Forall_parse_of p')%type
       end.
End cfg.
