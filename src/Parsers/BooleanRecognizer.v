(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common Fiat.Common.Wf.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}.

  Section bool.
    Section parts.
      Definition parse_item'
                 (str_matches_nonterminal : String.string -> bool)
                 (str : String)
                 (it : item Char)
      : bool
        := match it with
             | Terminal ch => str ~= [ ch ]
             | NonTerminal nt => str_matches_nonterminal nt
           end.

      Section production.
        Context {len0}
                (parse_nonterminal
                 : forall (str : String) (len : nat),
                     len <= len0
                     -> String.string
                     -> bool).

        (** To match a [production], we must match all of its items.
            But we may do so on any particular split. *)
        Fixpoint parse_production'
                 (str : String)
                 (len : nat)
                 (pf : len <= len0)
                 (prod : production Char)
        : bool.
        Proof.
          refine
            match prod with
              | nil =>
                (** 0-length production, only accept empty *)
                beq_nat (length str) 0
              | it::its
                => let parse_production' := fun str len pf => parse_production' str len pf its in
                   fold_left
                     orb
                     (map (fun n =>
                             (parse_item'
                                (parse_nonterminal (take n str) (len := min n len) _)
                                (take n str)
                                it)
                               && parse_production' (drop n str) (len - n) _)%bool
                          (split_string_for_production it its str))
                     false
            end;
          clear -pf;
          abstract (try apply Min.min_case_strong; omega).
        Defined.
      End production.

      Section productions.
        Context {len0}
                (parse_nonterminal
                 : forall (str : String)
                          (len : nat)
                          (pf : len <= len0),
                     String.string -> bool).

        (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
        Definition parse_productions'
                   (str : String)
                   (len : nat)
                   (pf : len <= len0)
                   (prods : productions Char)
        : bool
          := fold_right orb
                        false
                        (map (parse_production' parse_nonterminal str pf)
                             prods).
      End productions.


      Section nonterminals.
        Section step.
          Context {len0 valid_len}
                  (parse_nonterminal
                   : forall (p : nat * nat),
                       prod_relation lt lt p (len0, valid_len)
                       -> forall (valid : nonterminals_listT)
                                 (str : String) (len : nat),
                            len <= fst p -> String.string -> bool).

          Definition parse_nonterminal_step
                     (valid : nonterminals_listT)
                     (str : String)
                     (len : nat)
                     (pf : len <= len0)
                     (nt : String.string)
          : bool.
          Proof.
            refine
              (parse_productions'
                 (sumbool_rect
                    (fun b => forall (str' : String) (len' : nat), len' <= (if b then len else len0) -> String.string -> bool)
                    (fun _ => (** [str] got smaller, so we reset the valid nonterminals list *)
                       @parse_nonterminal
                         (len, nonterminals_length initial_nonterminals_data)
                         (or_introl _)
                         initial_nonterminals_data)
                    (fun _ => (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
                       sumbool_rect
                         (fun _ => forall (str' : String) (len' : nat), len' <= len0 -> String.string -> bool)
                         (fun is_valid => (** It was valid, so we can remove it *)
                            @parse_nonterminal
                              (len0, pred valid_len)
                              (or_intror (conj eq_refl _))
                              (remove_nonterminal valid nt))

                         (fun _ _ _ _ _ => (** oops, we already saw this nonterminal in the past.  ABORT! *)
                            false)
                         (Sumbool.sumbool_of_bool (negb (EqNat.beq_nat valid_len 0) && is_valid_nonterminal valid nt)))
                    (lt_dec len len0))
                 str
                 (len := len)
                 (sumbool_rect
                    (fun b => len <= (if b then len else len0))
                    (fun _ => le_n _)
                    (fun _ => _)
                    (lt_dec len len0))
                 (Lookup G nt));
            first [ assumption
                  | simpl;
                    generalize (proj1 (proj1 (Bool.andb_true_iff _ _) is_valid));
                    clear; intro;
                    abstract (
                        destruct valid_len; try apply Lt.lt_n_Sn; [];
                        exfalso; simpl in *; congruence
                  ) ].
          Defined.
        End step.

        Section wf.
          (** TODO: add comment explaining signature *)
          Definition parse_nonterminal_or_abort
          : forall (p : nat * nat)
                   (valid : nonterminals_listT)
                   (str : String) (len : nat),
              len <= fst p
              -> String.string
              -> bool
            := @Fix
                 (nat * nat)
                 _
                 (well_founded_prod_relation lt_wf lt_wf)
                 _
                 (fun sl => @parse_nonterminal_step (fst sl) (snd sl)).

          Definition parse_nonterminal
                     (str : String)
                     (nt : String.string)
          : bool
            := @parse_nonterminal_or_abort
                 (length str, nonterminals_length initial_nonterminals_data)
                 initial_nonterminals_data
                 str (length str)
                 (le_n _) nt.
        End wf.
      End nonterminals.

      Definition parse_item
                 (str : String)
                 (it : item Char)
      : bool
        := parse_item' (parse_nonterminal str) str it.

      Definition parse_production
                 (str : String)
                 (pat : production Char)
      : bool
        := parse_production' (parse_nonterminal_or_abort (length str, nonterminals_length initial_nonterminals_data) initial_nonterminals_data) str (reflexivity _) pat.

      Definition parse_productions
                 (str : String)
                 (pats : productions Char)
      : bool
        := parse_productions' (parse_nonterminal_or_abort (length str, nonterminals_length initial_nonterminals_data) initial_nonterminals_data) str (reflexivity _) pats.
    End parts.
  End bool.
End recursive_descent_parser.
