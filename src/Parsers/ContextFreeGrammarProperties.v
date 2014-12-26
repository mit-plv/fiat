(** * Properties about Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Import Coq.Relations.Relation_Definitions.
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

  Inductive is_subparse_of : forall {str pats}, relation (parse_of String G str pats) :=
  | SubParseHead : forall str pat pats
                          (p p' : parse_of_production str pat),
                     is_subparse_of_production p p'
                     -> is_subparse_of (ParseHead p) (ParseHead p').


    Inductive parse_of : String -> productions -> Type :=
    | ParseHead : forall str pat pats, parse_of_production str pat
                                       -> parse_of str (pat::pats)
    | ParseTail : forall str pat pats, parse_of str pats
                                       -> parse_of str (pat::pats)
    with parse_of_production : String -> production -> Type :=
    | ParseProductionNil : parse_of_production (Empty _) nil
    | ParseProductionCons : forall str pat strs pats,
                           parse_of_item str pat
                           -> parse_of_production strs pats
                           -> parse_of_production (str ++ strs) (pat::pats)
    with parse_of_item : String -> item -> Type :=
    | ParseTerminal : forall x, parse_of_item [[ x ]]%string_like (Terminal x)
    | ParseNonTerminal : forall name str, parse_of str (Lookup G name)
                                          -> parse_of_item str (NonTerminal name).
End cfg.
