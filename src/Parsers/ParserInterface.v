(** * Simply-typed interface of the parser *)
Require Export Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Export Fiat.Parsers.ContextFreeGrammar.Carriers.

Set Implicit Arguments.

Local Open Scope list_scope.
Reserved Infix "~=" (at level 70).

Section interface.
  Context {Char} (G : grammar Char).

  (** A list of splits is complete if, for every reachable production,
      it contains every index of the string that yields a parse tree
      for that production by splitting at that index. *)
  Definition split_list_is_complete `{HSL : StringLike Char} (str : String) (p : production Char)
             (splits : list nat)
  : Prop
    := forall it its,
         p = it::its
         -> forall n,
              n <= length str
              -> production_is_reachable G (it::its)
              -> parse_of_item G (take n str) it
              -> parse_of_production G (drop n str) its
              -> List.In n (List.map (min (length str)) splits).

  Definition split_list_is_complete_idx `{HSL : StringLike Char} (str : String) (p : default_production_carrierT)
             (splits : list nat)
  : Prop
    := is_true (default_production_carrier_valid (G := G) p)
       -> split_list_is_complete str (default_to_production (G := G) p) splits.

  Record Splitter :=
    {
      string_type :> StringLike Char;
      splits_for : String -> default_production_carrierT -> list nat;
      (** give a list of indices for splitting a given string *)

      string_type_properties :> StringLikeProperties Char;
      splits_for_complete : forall str idx,
                              split_list_is_complete_idx str idx (splits_for str idx)
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
