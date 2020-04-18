(** * Definition of the common part of the interface of the CFG parser *)
Require Import Coq.Lists.List Coq.Arith.Wf_nat.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context {Char} {HSLM : StringLikeMin Char} {G : grammar Char}.

  Class parser_computational_predataT :=
    { nonterminals_listT : Type;
      nonterminal_carrierT : Type;
      of_nonterminal : String.string -> nonterminal_carrierT;
      to_nonterminal : nonterminal_carrierT -> String.string;
      production_carrierT : Type;
      to_production : production_carrierT -> production Char;
      nonterminal_to_production : nonterminal_carrierT -> list production_carrierT;
      production_tl : production_carrierT -> production_carrierT;
      production_carrier_valid : production_carrierT -> bool;
      initial_nonterminals_data : nonterminals_listT;
      nonterminals_length : nonterminals_listT -> nat;
      is_valid_nonterminal : nonterminals_listT -> nonterminal_carrierT -> bool;
      remove_nonterminal : nonterminals_listT -> nonterminal_carrierT -> nonterminals_listT }.

  Class parser_removal_dataT' {predata : parser_computational_predataT} :=
    { nonterminals_listT_R : nonterminals_listT -> nonterminals_listT -> Prop
      := ltof _ nonterminals_length;
      nonterminals_length_zero : forall ls,
                                   nonterminals_length ls = 0
                                   -> forall nt, is_valid_nonterminal ls nt = false;
      remove_nonterminal_dec : forall ls nonterminal,
                                 is_valid_nonterminal ls nonterminal
                                 -> nonterminals_listT_R (remove_nonterminal ls nonterminal) ls;
      remove_nonterminal_noninc : forall ls nonterminal,
                                    ~nonterminals_listT_R ls (remove_nonterminal ls nonterminal);
      initial_nonterminals_correct : forall nonterminal,
                                       is_valid_nonterminal initial_nonterminals_data (of_nonterminal nonterminal) <-> List.In nonterminal (Valid_nonterminals G);
      initial_nonterminals_correct' : forall nonterminal,
                                       is_valid_nonterminal initial_nonterminals_data nonterminal <-> List.In (to_nonterminal nonterminal) (Valid_nonterminals G);
      to_of_nonterminal : forall nonterminal,
                            List.In nonterminal (Valid_nonterminals G)
                            -> to_nonterminal (of_nonterminal nonterminal) = nonterminal;
      of_to_nonterminal : forall nonterminal,
                            is_valid_nonterminal initial_nonterminals_data nonterminal
                            -> of_nonterminal (to_nonterminal nonterminal) = nonterminal;
      production_tl_correct : forall p,
                                to_production (production_tl p) = tl (to_production p);
      nonterminal_to_production_correct
      : forall nt,
          List.In nt (Valid_nonterminals G)
          -> List.map to_production (nonterminal_to_production (of_nonterminal nt))
             = Lookup G nt;
      production_tl_valid
      : forall p,
          production_carrier_valid p -> production_carrier_valid (production_tl p);
      nonterminal_to_production_valid
      : forall nt,
          is_valid_nonterminal initial_nonterminals_data nt
          -> List.Forall production_carrier_valid (nonterminal_to_production nt);
      ntl_wf : well_founded nonterminals_listT_R
      := well_founded_ltof _ _;
      remove_nonterminal_1
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps'
          -> is_valid_nonterminal ls ps';
      remove_nonterminal_2
      : forall ls ps ps',
          is_valid_nonterminal (remove_nonterminal ls ps) ps' = false
          <-> is_valid_nonterminal ls ps' = false \/ ps = ps' }.

  Definition sub_nonterminals_listT `{parser_computational_predataT} (x y : nonterminals_listT) : Prop
    := forall p, is_valid_nonterminal x p -> is_valid_nonterminal y p.

  Class split_dataT `{parser_computational_predataT} :=
    { split_string_for_production
      : production_carrierT -> String -> nat -> nat -> list nat }.

  Class boolean_parser_dataT :=
    { predata :> parser_computational_predataT;
      split_data :> split_dataT }.

  Global Coercion predata : boolean_parser_dataT >-> parser_computational_predataT.
  Global Coercion split_data : boolean_parser_dataT >-> split_dataT.
End recursive_descent_parser.
