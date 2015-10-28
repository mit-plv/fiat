(** * Simply-typed interface of the parser *)
Require Export Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.

Set Implicit Arguments.

Local Open Scope list_scope.
Reserved Infix "~=" (at level 70).

Section interface.
  Context {Char} (G : grammar Char).

  (** A production is reachable if it is the tail of a production
      associated to a valid nonterminal. *)
  Definition production_is_reachable (p : production Char) : Prop
    := exists nt prefix,
         List.In nt (Valid_nonterminals G)
         /\ List.In
              (prefix ++ p)
              (Lookup G nt).

  (** A list of splits is complete if, for every reachable production,
      it contains every index of the string that yields a parse tree
      for that production by splitting at that index. *)
  Definition split_list_is_complete `{HSL : StringLike Char} (str : String) (it : item Char) (its : production Char)
             (splits : list nat)
  : Prop
    := forall n,
         n <= length str
         -> production_is_reachable (it::its)
         -> parse_of_item G (take n str) it
         -> parse_of_production G (drop n str) its
         -> List.In n (List.map (min (length str)) splits).

  Record Splitter :=
    {
      string_type :> StringLike Char;
      splits_for : String -> item Char -> production Char -> list nat;
      (** give a list of indices for splitting a given string *)

      string_type_properties :> StringLikeProperties Char;
      splits_for_complete : forall str it its,
                              split_list_is_complete str it its (splits_for str it its)
      (** [splits_for] must contain all valid indices for splitting *)
    }.

  Global Existing Instance string_type.
  Global Existing Instance string_type_properties.

  Record Parser (HSL : StringLike Char) :=
    {
      has_parse : @String Char HSL -> bool;
      (** does this string parse as the start symbol of the grammar? *)

      has_parse_sound : forall str,
                          has_parse str = true
                          -> parse_of_item G str (NonTerminal (Start_symbol G));

      has_parse_complete : forall str,
                             parse_of_item G str (NonTerminal (Start_symbol G))
                             -> has_parse str = true
    }.
End interface.
