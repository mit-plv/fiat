(** * Simply-typed interface of the parser *)
Require Export ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarProperties.

Set Implicit Arguments.

Local Open Scope list_scope.
Reserved Infix "~=" (at level 70).

Section interface.
  Context {string} `{StringLike string} (G : grammar string).

  (** A production is reachable if it is the tail of a production
      associated to a valid nonterminal. *)
  Definition production_is_reachable (p : production string) : Prop
    := exists nt prefix,
         List.In nt (Valid_nonterminals G)
         /\ List.In
              (prefix ++ p)
              (Lookup G nt).

  (** A list of splits is complete if, for every reachable production,
      it contains every index of the string that yields a parse tree
      for that production by splitting at that index. *)
  Definition split_list_is_complete (str : String) (it : item string) (its : production string)
             (splits : list nat)
  : Prop
    := forall n,
         n <= length str
         -> parse_of_item G (take n str) it
         -> parse_of_production G (drop n str) its
         -> production_is_reachable (it::its)
         -> List.In n splits.

  Record Splitter :=
    {
      split_rep : Type;
      (** metadata associated with the string, to help split it *)
      split_take : nat -> split_rep -> split_rep;
      (** take the metadata associated with the first [n] characters *)
      split_drop : nat -> split_rep -> split_rep;
      (** take the metadata associated with all but the first [n] characters *)
      splits_for : split_rep -> item string -> production string -> list nat;
      (** give a list of indices for splitting a given string *)

      split_invariant : String -> split_rep -> Prop where "s ~= st" := (split_invariant s st);
      (** invariant relating a [String] to a representation *)


      take_respectful : forall str st n,
                          str ~= st
                          -> fst (SplitAt n str) ~= split_take n st;
      (** [split_take] must respect the invariant *)
      drop_respectful : forall str st n,
                          str ~= st
                          -> snd (SplitAt n str) ~= split_drop n st;
      (** [split_drop] must respect the invariant *)
      splits_for_complete : forall str st it its,
                              str ~= st
                              -> split_list_is_complete str it its (splits_for st it its)
      (** [splits_for] must contain all valid indices for splitting *)
    }.

  Record Parser (splitter : Splitter) :=
    {
      has_parse : String -> split_rep splitter -> bool;
      (** does this string parse as the start symbol of the grammar? *)

      has_parse_sound : forall str st,
                          split_invariant splitter str st
                          -> has_parse str st = true
                          -> parse_of_item String G str (NonTerminal _ (Start_symbol G));

      has_parse_complete : forall str (p : parse_of_item String G str (NonTerminal _ (Start_symbol G))),
                             Forall_parse_of_item
                               (fun _ nt => List.In nt (Valid_nonterminals G))
                               p
                             -> forall st,
                                  split_invariant splitter str st
                                  -> has_parse str st = true
    }.
End interface.
