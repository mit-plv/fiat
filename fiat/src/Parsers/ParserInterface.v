(** * Simply-typed interface of the parser *)
Require Export Fiat.Parsers.ContextFreeGrammar.Core.
Require Export Fiat.Parsers.ContextFreeGrammar.SimpleCorrectness.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Export Fiat.Parsers.ContextFreeGrammar.Carriers.

Set Implicit Arguments.

Local Open Scope list_scope.
Reserved Infix "~=" (at level 70).

Section preinterface.
  Context {Char} (G : pregrammar' Char).

  (** A list of splits is complete if, for every reachable production,
      it contains every index of the string that yields a parse tree
      for that production by splitting at that index. *)
  Definition split_list_is_complete `{HSL : StringLike Char}
             (str : String)
             (offset len : nat)
             (p : production Char)
             (splits : list nat)
  : Prop
    := len = 0 \/ offset + len <= length str
       -> let str := substring offset len str in
          forall it its,
            p = it::its
            -> forall n,
              n <= length str
              -> production_is_reachable G (it::its)
              -> parse_of_item G (take n str) it
              -> parse_of_production G (drop n str) its
              -> List.In n (List.map (min (length str)) splits).

  Definition split_list_is_complete_idx `{HSL : StringLike Char}
             (str : String)
             (offset len : nat)
             (p : default_production_carrierT)
             (splits : list nat)
  : Prop
    := is_true (default_production_carrier_valid (G := G) p)
       -> split_list_is_complete str offset len (default_to_production (G := G) p) splits.

  Record Splitter :=
    {
      string_type_min :> StringLikeMin Char;
      string_type :> StringLike Char;
      splits_for : String -> default_production_carrierT -> nat -> nat -> list nat;
      (** give a list of indices for splitting a given string *)

      string_type_properties :> StringLikeProperties Char;
      splits_for_complete : forall str idx offset len,
                              split_list_is_complete_idx str offset len idx (splits_for str idx offset len)
      (** [splits_for] must contain all valid indices for splitting *)
    }.

  Global Existing Instance string_type_min.
  Global Existing Instance string_type.
  Global Existing Instance string_type_properties.
End preinterface.

Record Parser {Char} (G : grammar Char)
       {HSLM : StringLikeMin Char} (HSL : StringLike Char) :=
  {
    has_parse : @String Char HSLM -> bool;
    (** does this string parse as the start symbol of the grammar? *)

    has_parse_sound : forall str,
                        has_parse str = true
                        -> parse_of_item G str (NonTerminal (Start_symbol G));

    has_parse_complete : forall str,
                           parse_of_item G str (NonTerminal (Start_symbol G))
                           -> has_parse str = true;

    parse : @String Char HSLM -> option (@simple_parse_of_item Char);
    (** find the parse tree of the string as the start symbol of the grammar *)

    parse_correct : forall str, has_parse str = if parse str then true else false;

    parse_sound : forall str t,
        parse str = Some t
        -> simple_parse_of_item_correct G str (NonTerminal (Start_symbol G)) t

  }.
