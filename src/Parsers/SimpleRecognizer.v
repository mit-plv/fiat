(** * Definition of a simple_parse_of-returning CFG parser-recognizer *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common Fiat.Common.Wf.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context {Char} {HSLM : StringLikeMin Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}.
  Context (str : String).

  Local Notation simple_parse_of := (@simple_parse_of Char) (only parsing).
  Local Notation simple_parse_of_production := (@simple_parse_of_production Char) (only parsing).

  Section simple.
    Section parts.
      Definition parse_item'
                 (str_matches_nonterminal : nonterminal_carrierT -> option simple_parse_of)
                 (offset : nat) (len : nat)
                 (it : item Char)
      : option simple_parse_of_item
        := match it with
             | Terminal P => if EqNat.beq_nat len 1 && char_at_matches offset str P
                             then Some (SimpleParseTerminal (unsafe_get offset str))
                             else None
             | NonTerminal nt => if is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt)
                                 then option_map
                                        (SimpleParseNonTerminal nt)
                                        (str_matches_nonterminal (of_nonterminal nt))
                                 else None
           end%bool.

      Section production.
        Context {len0}
                (parse_nonterminal
                 : forall (offset : nat) (len : nat),
                     len <= len0
                     -> nonterminal_carrierT
                     -> option simple_parse_of).

        Definition option_SimpleParseProductionCons
        : option simple_parse_of_item
          -> option simple_parse_of_production
          -> option simple_parse_of_production
          := fun pit pits
             => match pit, pits with
                  | Some pit', Some pits' => Some (SimpleParseProductionCons pit' pits')
                  | None, _ => None
                  | _, None => None
                end.

        Definition option_orb {A} (x y : option A) : option A
          := match x, y with
               | Some x', _ => Some x'
               | None, Some y' => Some y'
               | None, None => None
             end.

        (** To match a [production], we must match all of its items.
            But we may do so on any particular split. *)
        Definition parse_production'_for
                 (splits : production_carrierT -> String -> nat -> nat -> list nat)
                 (offset : nat)
                 (len : nat)
                 (pf : len <= len0)
                 (prod_idx : production_carrierT)
        : option simple_parse_of_production.
        Proof.
          revert offset len pf.
          refine
            (list_rect
               (fun _ =>
                  forall (idx : production_carrierT)
                         (offset : nat)
                         (len : nat)
                         (pf : len <= len0),
                    option simple_parse_of_production)
               ((** 0-length production, only accept empty *)
                 fun _ offset len _ => if beq_nat len 0
                                       then Some SimpleParseProductionNil
                                       else None)
               (fun it its parse_production' idx offset len pf
                => fold_left
                     option_orb
                     (map (fun n =>
                             option_SimpleParseProductionCons
                               (parse_item'
                                  (parse_nonterminal offset (len := min n len) _)
                                  offset
                                  (min n len)
                                  it)
                               (parse_production' (production_tl idx) (offset + n) (len - n) _))
                          (splits idx str offset len))
                     None)
               (to_production prod_idx)
               prod_idx);
          clear -pf;
          abstract (try apply Min.min_case_strong; omega).
        Defined.

        Definition parse_production'
                 (offset : nat)
                 (len : nat)
                 (pf : len <= len0)
                 (prod_idx : production_carrierT)
        : option simple_parse_of_production
          := parse_production'_for split_string_for_production offset pf prod_idx.
      End production.

      Section productions.
        Context {len0}
                (parse_nonterminal
                 : forall (offset : nat)
                          (len : nat)
                          (pf : len <= len0),
                     nonterminal_carrierT -> option simple_parse_of).

        Definition option_simple_parse_of_orb
                   (x : option simple_parse_of_production)
                   (xs : option simple_parse_of)
        : option simple_parse_of
          := match x, xs with
               | Some x', _ => Some (SimpleParseHead x')
               | None, Some xs' => Some (SimpleParseTail xs')
               | None, None => None
             end.

        (** To parse as a given list of [production]s, we must parse as one of the [production]s. *)
        Definition parse_productions'
                   (offset : nat)
                   (len : nat)
                   (pf : len <= len0)
                   (prods : list production_carrierT)
        : option simple_parse_of
          := fold_right option_simple_parse_of_orb
                        None
                        (map (parse_production' parse_nonterminal offset pf)
                             prods).
      End productions.


      Section nonterminals.
        Section step.
          Context {len0 valid_len}
                  (parse_nonterminal
                   : forall (p : nat * nat),
                       prod_relation lt lt p (len0, valid_len)
                       -> forall (valid : nonterminals_listT)
                                 (offset : nat) (len : nat),
                            len <= fst p -> nonterminal_carrierT -> option simple_parse_of).

          Definition parse_nonterminal_step
                     (valid : nonterminals_listT)
                     (offset : nat)
                     (len : nat)
                     (pf : len <= len0)
                     (nt : nonterminal_carrierT)
          : option simple_parse_of.
          Proof.
            refine
              (option_rect
                 (fun _ => option simple_parse_of)
                 (fun parse_nonterminal
                  => parse_productions'
                       parse_nonterminal
                       offset
                       (len := len)
                       (sumbool_rect
                          (fun b => len <= (if b then len else len0))
                          (fun _ => le_n _)
                          (fun _ => _)
                          (lt_dec len len0))
                       (nonterminal_to_production nt))
                 None
                 (sumbool_rect
                    (fun b => option (forall (offset' : nat) (len' : nat), len' <= (if b then len else len0) -> nonterminal_carrierT -> option simple_parse_of))
                    (fun _ => (** [str] got smaller, so we reset the valid nonterminals list *)
                       Some (@parse_nonterminal
                               (len, nonterminals_length initial_nonterminals_data)
                               (or_introl _)
                               initial_nonterminals_data))
                    (fun _ => (** [str] didn't get smaller, so we cache the fact that we've hit this nonterminal already *)
                       sumbool_rect
                         (fun _ => option (forall (offset' : nat) (len' : nat), len' <= len0 -> nonterminal_carrierT -> option simple_parse_of))
                         (fun is_valid => (** It was valid, so we can remove it *)
                            Some (@parse_nonterminal
                                    (len0, pred valid_len)
                                    (or_intror (conj eq_refl _))
                                    (remove_nonterminal valid nt)))

                         (fun _ => (** oops, we already saw this nonterminal in the past.  ABORT! *)
                            None)
                         (Sumbool.sumbool_of_bool (negb (EqNat.beq_nat valid_len 0) && is_valid_nonterminal valid nt)))
                    (lt_dec len len0)));
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
                   (offset : nat) (len : nat),
              len <= fst p
              -> nonterminal_carrierT
              -> option simple_parse_of
            := @Fix
                 (nat * nat)
                 _
                 (well_founded_prod_relation lt_wf lt_wf)
                 _
                 (fun sl => @parse_nonterminal_step (fst sl) (snd sl)).

          Definition parse_nonterminal'
                     (nt : nonterminal_carrierT)
          : option simple_parse_of
            := @parse_nonterminal_or_abort
                 (length str, nonterminals_length initial_nonterminals_data)
                 initial_nonterminals_data
                 0 (length str)
                 (le_n _) nt.

          Definition parse_nonterminal
                     (nt : String.string)
          : option simple_parse_of
            := parse_nonterminal' (of_nonterminal nt).
        End wf.
      End nonterminals.

      Definition parse_item
                 (it : item Char)
      : option simple_parse_of_item
        := parse_item' parse_nonterminal' 0 (length str) it.

      Definition parse_production
                 (pat : production_carrierT)
      : option simple_parse_of_production
        := parse_production' (parse_nonterminal_or_abort (length str, nonterminals_length initial_nonterminals_data) initial_nonterminals_data) 0 (reflexivity _) pat.

      Definition parse_productions
                 (pats : list production_carrierT)
      : option simple_parse_of
        := parse_productions' (parse_nonterminal_or_abort (length str, nonterminals_length initial_nonterminals_data) initial_nonterminals_data) 0 (reflexivity _) pats.
    End parts.
  End simple.
End recursive_descent_parser.
