(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.BooleanBaseTypes.
Require Import ADTSynthesis.Parsers.StringLike.Properties.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Wf.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}.

  Section bool.
    Section parts.
      Definition parse_item
                 (str_matches_nonterminal : String.string -> bool)
                 (str : String)
                 (it : item Char)
      : bool
        := match it with
             | Terminal ch => str ~= [ ch ]
             | NonTerminal nt => str_matches_nonterminal nt
           end.

      Section production.
        Context {str0}
                (parse_nonterminal
                 : forall (str : String),
                     str ≤s str0
                     -> String.string
                     -> bool).

        (** To match a [production], we must match all of its items.
            But we may do so on any particular split. *)
        Fixpoint parse_production
                 (str : String)
                 (pf : str ≤s str0)
                 (prod : production Char)
        : bool.
        Proof.
          refine
            match prod with
              | nil =>
                (** 0-length production, only accept empty *)
                Nat.eq_dec (length str) 0
              | it::its
                => let parse_production' := fun str pf => parse_production str pf its in
                   fold_right
                     orb
                     false
                     (map (fun n =>
                             (parse_item
                                (parse_nonterminal (str := take n str) _)
                                (take n str)
                                it)
                               && parse_production' (drop n str) _)%bool
                          (split_string_for_production it its str))
            end;
          revert pf; clear -HSLP; intros;
          abstract (rewrite ?str_le_take, ?str_le_drop; assumption).
        Defined.
      End production.

      Section productions.
        Context {str0}
                (parse_nonterminal
                 : forall (str : String)
                          (pf : str ≤s str0),
                     String.string -> bool).

        (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
        Definition parse_productions
                   (str : String)
                   (pf : str ≤s str0)
                   (prods : productions Char)
        : bool
          := fold_right orb
                        false
                        (map (parse_production parse_nonterminal pf)
                             prods).
      End productions.


      Section nonterminals.
        Section step.
          Context {str0 valid}
                  (parse_nonterminal
                   : forall (p : String * nonterminals_listT),
                       prod_relation (ltof _ length) nonterminals_listT_R p (str0, valid)
                       -> forall str : String,
                            str ≤s fst p -> String.string -> bool).

          Definition parse_nonterminal_step
                     (str : String)
                     (pf : str ≤s str0)
                     (nt : String.string)
          : bool.
          Proof.
            refine
              (if lt_dec (length str) (length str0)
               then (** [str] got smaller, so we reset the valid nonterminals list *)
                 parse_productions
                   (@parse_nonterminal
                      (str : String, initial_nonterminals_data)
                      (or_introl _))
                   (or_intror (reflexivity _))
                   (Lookup G nt)
               else (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
                 if Sumbool.sumbool_of_bool (is_valid_nonterminal valid nt)
                 then (** It was valid, so we can remove it *)
                   parse_productions
                     (@parse_nonterminal
                        (str0 : String, remove_nonterminal valid nt)
                        (or_intror (conj eq_refl (remove_nonterminal_dec _ nt _))))
                     (str := str)
                     _
                     (Lookup G nt)
                 else (** oops, we already saw this nonterminal in the past.  ABORT! *)
                   false);
            assumption.
          Defined.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_nonterminal_or_abort
          : forall (p : String * nonterminals_listT)
                   (str : String),
              str ≤s fst p
              -> String.string
              -> bool
            := Fix3
                 _ _ _
                 (well_founded_prod_relation
                    (well_founded_ltof _ length)
                    ntl_wf)
                 _
                 (fun sl => @parse_nonterminal_step (fst sl) (snd sl)).

          Definition parse_nonterminal
                     (str : String)
                     (nt : String.string)
          : bool
            := @parse_nonterminal_or_abort
                 (str : String, initial_nonterminals_data) str
                 (or_intror (reflexivity _)) nt.
        End wf.
      End nonterminals.
    End parts.
  End bool.
End recursive_descent_parser.
