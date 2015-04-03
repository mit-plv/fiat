(** * Reflective helpers for simply-typed interface of the parser *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarProperties.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarEquality.
Require Import ADTSynthesis.Parsers.ParserInterface.
Require Import ADTSynthesis.Parsers.Refinement.IndexedAndAtMostOneNonTerminal.
Require Import ADTSynthesis.Computation.Core.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Equality.

Set Implicit Arguments.

Fixpoint tails {A} (ls : list A) : list (list A)
  := match ls with
       | nil => [nil]
       | x::xs => (x::xs)::tails xs
     end.

(** Reflective version of [split_list_is_complete] and [production_is_reachable] *)
Definition forall_reachable_productions {Char} (G : grammar Char) {T} (f : production Char -> T -> T) (init : T)
: T
  := fold_right
       f
       init
       (flatten1
          (flatten1
             (map
                (fun nt =>
                   (map
                      tails
                      (Lookup G nt)))
                (Valid_nonterminals G)))).

Global Arguments forall_reachable_productions / .

Section interface.
  Context (G : grammar Ascii.ascii).

  Definition expanded_fallback_list
             (s : (String.string * (nat * nat)))
             (it : item Ascii.ascii) (its : production Ascii.ascii)
             (dummy : list nat)
  : Comp ((String.string * (nat * nat)) * list nat)
    := (ls <- (forall_reachable_productions
                 G
                 (fun p else_case
                  => if production_beq ascii_beq p (it::its)
                     then (match p return Comp (list nat) with
                             | nil => ret dummy
                             | _::nil => ret [min (String.length (fst s) - fst (snd s)) (snd (snd s))]
                             | (Terminal _):: _ :: _ => ret [1]
                             | (NonTerminal nt):: p'
                               => if has_only_terminals p'
                                  then
                                    ret [min (String.length (fst s) - fst (snd s)) (snd (snd s)) -
                                         Datatypes.length p']
                                  else { splits : list nat
                                       | forall n,
                                           n <= length (fst s)
                                           -> parse_of_item G (take n (fst s)) (NonTerminal nt)
                                           -> parse_of_production G (drop n (fst s)) p'
                                           -> List.In n splits }
                           end)
                     else else_case)
                 (ret dummy));
        ret (s, ls))%comp.

  Global Arguments expanded_fallback_list / .

  Lemma step_expanded_fallback_list {s p} dummy
  : refine (fallback_ls <- {ls : list nat |
                            match fst p with
                              | Terminal _ => True
                              | NonTerminal _ =>
                                if has_only_terminals (snd p)
                                then True
                                else
                                  split_list_is_complete G
                                                         (substring (fst (snd s))
                                                                    (snd (snd s)) (fst s))
                                                         (fst p) (snd p) ls
                            end};
            ret
              (s,
               match snd p with
                 | [] => [min (String.length (fst s) - fst (snd s)) (snd (snd s))]
                 | _ :: _ =>
                   match fst p with
                     | Terminal _ => [1]
                     | NonTerminal _ =>
                       if has_only_terminals (snd p)
                       then
                         [min (String.length (fst s) - fst (snd s)) (snd (snd s)) -
                          Datatypes.length (snd p)]
                       else fallback_ls
                   end
               end))
           (expanded_fallback_list s (fst p) (snd p) dummy).
  Proof.
    unfold expanded_fallback_list, forall_reachable_productions, split_list_is_complete, production_is_reachable.
    generalize (Valid_nonterminals G).
    intro ls; revert p; induction ls.
    { simpl.
      repeat intro; computes_to_inv; subst.
      destruct (fst p); simpl.
      {
    intro ls; induction ls
    simplify with monad laws.

{ls : list nat |
                     match fst n with
                     | Terminal _ => True
                     | NonTerminal _ =>
                         if has_only_terminals (snd n)
                         then True
                         else
                          split_list_is_complete G
                            (substring (fst (snd r_n))
                               (snd (snd r_n)) (fst r_n))
                            (fst n) (snd n) ls
                     end}


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
         -> parse_of_item G (take n str) it
         -> parse_of_production G (drop n str) its
         -> production_is_reachable (it::its)
         -> List.In n splits.

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

  Record Parser (splitter : Splitter) :=
    {
      has_parse : @String Char splitter -> bool;
      (** does this string parse as the start symbol of the grammar? *)

      has_parse_sound : forall str,
                          has_parse str = true
                          -> parse_of_item G str (NonTerminal (Start_symbol G));

      has_parse_complete : forall str (p : parse_of_item G str (NonTerminal (Start_symbol G))),
                             Forall_parse_of_item
                               (fun _ nt => List.In nt (Valid_nonterminals G))
                               p
                             -> has_parse str = true
    }.
End interface.
