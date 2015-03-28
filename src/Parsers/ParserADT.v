(** * Reference implementation of a splitter and parser based on that splitter *)
Require Import ADTNotation.BuildADT ADTNotation.BuildADTSig.
Require Import ADT.ComputationalADT.
Require Import Parsers.ContextFreeGrammar.
Require Import Parsers.BooleanRecognizer.
Require Import ADTSynthesis.Common.List.Operations.
Require Import ADTRefinement.GeneralRefinements.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.

Section ReferenceImpl.
  Context {CharType} {String : string_like CharType} (G : grammar CharType).

  (** Representation of a [String] that can be split *)
  Definition string_rep : ADTSig :=
    ADTsignature {
      Constructor "new" : String -> rep,
      (** Initialize, with a given [String] to be parsed or split. *)

      Method "take" : rep x nat -> rep x unit,
      (** Return the first [n] characters, for the given [n : nat]. *)

      Method "drop" : rep x nat -> rep x unit,
      (** Return everything but the first [n] characters, for the given [n : nat]. *)

      Method "splits" : rep x item CharType * production CharType -> rep x list nat
    }.

  Definition production_is_reachable (p : item CharType * production CharType) : Prop
    := exists nt prefix,
         List.In nt (Valid_nonterminals G)
         /\ List.In
              (prefix ++ ((fst p)::(snd p)))
              (Lookup G nt).

  (** Reference implementation of a [String] that can be split *)
  Definition string_spec : ADT string_rep := ADTRep String {
    Def Constructor "new"(s : String) : rep :=
      ret s,

    Def Method "take"(s : rep, n : nat) : unit :=
      ret (fst (SplitAt n s), tt),

    Def Method "drop"(s : rep, n : nat) : unit :=
      ret (snd (SplitAt n s), tt),

    Def Method "splits"(s : rep, p : item CharType * production CharType) : list nat :=
      ls <- { ls : list nat
            | forall n,
                n <= Length s
                -> parse_of_item String G (fst (SplitAt n s)) (fst p)
                -> parse_of_production String G (snd (SplitAt n s)) (snd p)
                -> production_is_reachable p
                -> List.In n ls };
      ret (s, ls)
  }.

  Section parser.
    Context (splitter : Sharpened string_spec).

    Let split_stateT (s : String) : Type.
    Proof.
      (** FIXME: What goes here? *)
      (* exact { r : rep of splitter | rep inv holds with s }. *)
    Admitted.

    Check parse_nonterminal split_stateT.
    Definition has_parse (s : String) : bool
parse_nonterminal
