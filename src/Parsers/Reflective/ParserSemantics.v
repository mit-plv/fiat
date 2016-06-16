Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.GenericRecognizer.
Require Import Fiat.Common.Wf Fiat.Common.Wf2.
Set Implicit Arguments.

Definition step_option_rec
           {T}
           (is_valid_nonterminal : list nat -> nat -> bool)
           (len0 valid_len0 : nat)
           (parse_nt : forall len0' valid_len : nat,
               Wf.prod_relation lt lt (len0', valid_len) (len0, valid_len0) ->
               list nat -> nat -> forall len : nat, len <= len0' -> nat -> T)
           (G_length : nat)
           (up_to_G_length : list nat)
           (valids : list nat) (offset len : nat)
           (nt : nat)
  : option (nat -> nat -> nat -> T).
Proof.
  refine (sumbool_rect (fun _ => option (nat -> nat -> nat -> T))
                       (fun pf =>
                          Some
                            (fun offset' len0_minus_len'
                             => parse_nt len G_length
                                         (or_introl pf)
                                         up_to_G_length
                                         offset'
                                         (len - len0_minus_len') (Minus.le_minus len len0_minus_len')))
                       (fun _
                        => _)
                       (Compare_dec.lt_dec len len0)).
  refine (sumbool_rect
            (fun _ => option (nat -> nat -> nat -> T))
            (fun is_valid
             => _)
            (fun _ => None)
            (Sumbool.sumbool_of_bool (negb (EqNat.beq_nat valid_len0 0) && is_valid_nonterminal valids nt))%bool).
  refine (Some
            (fun offset' len0_minus_len' =>
               parse_nt len0 (pred valid_len0)
                        (or_intror (conj eq_refl (GenericRecognizer.pred_lt_beq _)))
                        (RDPList.filter_out_eq nt valids) offset'
                        (len0 - len0_minus_len') (Minus.le_minus len0 len0_minus_len'))).
  apply (proj1 (proj1 (Bool.andb_true_iff _ _) is_valid)).
Defined.

Definition interp_has_parse_term'
           {T}
           (interp_Term : forall {T}, Term interp_TypeCode T -> interp_TypeCode T)
           (is_valid_nonterminal : list nat -> nat -> bool)
           (strlen : nat)
           (char_at_matches_interp : nat -> Reflective.RCharExpr Ascii.ascii -> bool)
           (split_string_for_production : nat * (nat * nat) -> nat -> nat -> list nat)
           (t : has_parse_term interp_TypeCode T) : interp_TypeCode T
  := match t with
     | RFix2 G_length up_to_G_length f default valid_len valids nt_idx
       => Wf2.Fix2
            (Wf.well_founded_prod_relation Wf_nat.lt_wf Wf_nat.lt_wf)
            (fun aa' : nat * nat =>
               list nat -> nat -> forall a1 : nat, a1 <= fst aa' -> nat -> interp_TypeCode T)
            (fun (len0 valid_len0 : nat)
                 (parse_nt : forall len0' valid_len : nat,
                     Wf.prod_relation lt lt (len0', valid_len) (len0, valid_len0) ->
                     list nat -> nat -> forall len : nat, len <= len0' -> nat -> interp_TypeCode T)
                 (valids : list nat) (offset len : nat)
                 (pf : len <= len0)
                 (nt : nat)
             => option_rect
                  (fun _ : option (interp_TypeCode (cnat --> cnat --> cnat --> T)) => interp_TypeCode T)
                  (fun parse_nt
                   => interp_Term
                        f
                        (fun n : interp_TypeCode cnat => char_at_matches_interp n (*str*))
                        (fun n : interp_TypeCode (cnat * (cnat * cnat)) => split_string_for_production n (*str*))
                        len0 valid_len parse_nt valids offset len nt)
                  (interp_Term default)
                  (@step_option_rec (interp_TypeCode T) is_valid_nonterminal len0 valid_len0 parse_nt G_length up_to_G_length valids offset len nt))
            strlen
            valid_len
            valids
            0
            strlen
            (le_n _)
            nt_idx
     end.

Definition interp_has_parse_term {T}
  := Eval cbv [interp_has_parse_term'] in @interp_has_parse_term' T (@interp_Term).
