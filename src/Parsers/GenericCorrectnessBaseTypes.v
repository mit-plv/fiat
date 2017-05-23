(** * Definition of the generic part of the interface of the correctness proof of the CFG parser *)
Require Import Coq.Classes.Morphisms.
Require Import Coq.Arith.EqNat.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.GenericBaseTypes.
Require Import Fiat.Parsers.BaseTypes.

Set Implicit Arguments.

Section correctness.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
          {predata : @parser_computational_predataT Char}
          {gendata : @generic_parser_dataT Char}.

  Class generic_parser_correctness_dataT :=
    { parse_nt_is_correct
      : forall (str : String)
               (nt : nonterminal_carrierT)
               (expected_result : bool)
               (actual_result : parse_nt_T),
        Prop;
      parse_item_is_correct
      : forall (str : String)
               (it : item Char)
               (expected_result : bool)
               (actual_result : parse_item_T),
          Prop;
      parse_production_is_correct
      : forall (str : String)
               (p : production_carrierT)
               (expected_result : bool)
               (actual_result : parse_production_T),
          Prop;
      parse_productions_is_correct
      : forall (str : String)
               (p : list production_carrierT)
               (expected_result : bool)
               (actual_result : parse_productions_T),
          Prop;

      parse_nt_is_correct_Proper
      : Proper (beq ==> eq ==> eq ==> eq ==> Basics.impl) parse_nt_is_correct;
      parse_item_is_correct_Proper
      : Proper (beq ==> eq ==> eq ==> eq ==> Basics.impl) parse_item_is_correct;
      parse_production_is_correct_Proper
      : Proper (beq ==> eq ==> eq ==> eq ==> Basics.impl) parse_production_is_correct;
      parse_productions_is_correct_Proper
      : Proper (beq ==> eq ==> eq ==> eq ==> Basics.impl) parse_productions_is_correct;

      parse_nt_is_correct_disjoint
      : forall str nt v,
          parse_nt_is_correct str nt true v -> parse_nt_is_correct str nt false v -> False;
      parse_item_is_correct_disjoint
      : forall str it v,
          parse_item_is_correct str it true v -> parse_item_is_correct str it false v -> False;
      parse_production_is_correct_disjoint
      : forall str p v,
          parse_production_is_correct str p true v -> parse_production_is_correct str p false v -> False;
      parse_productions_is_correct_disjoint
      : forall str ps v,
          parse_productions_is_correct str ps true v -> parse_productions_is_correct str ps false v -> False;

      ret_Terminal_true_correct
      : forall str offset len ch,
          len = 0 \/ offset + len <= length str
          -> (beq_nat len 1 && char_at_matches offset str ch)%bool = true
          -> parse_item_is_correct
               (substring offset len str) (Terminal ch)
               true (ret_Terminal_true (unsafe_get offset str));
      ret_Terminal_false_correct
      : forall str it ch,
          parse_item_is_correct str it false (ret_Terminal_false ch);
      ret_NonTerminal_true_correct
      : forall str nt b rv,
          is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt) = true
          -> parse_nt_is_correct str (of_nonterminal nt) b rv
          -> parse_item_is_correct str (NonTerminal nt) b (ret_NonTerminal_true nt rv);
      ret_NonTerminal_false_correct
      : forall str nt,
          parse_item_is_correct str (NonTerminal nt) false (ret_NonTerminal_false nt);
      ret_production_nil_true_is_correct
      : forall str offset len prod_idx,
          to_production prod_idx = nil ->
          len = 0 ->
          parse_production_is_correct
            (substring offset len str) prod_idx
            true ret_production_nil_true;
      ret_production_nil_false_is_correct
      : forall str prod_idx,
          parse_production_is_correct str prod_idx false ret_production_nil_false;
      ret_orb_production_base_is_correct
      : forall str prod_idx,
          parse_production_is_correct str prod_idx false ret_orb_production_base;
      ret_orb_production_is_correct
      : forall str prod_idx b1 b2 rv1 rv2,
          parse_production_is_correct str prod_idx b1 rv1
          -> parse_production_is_correct str prod_idx b2 rv2
          -> parse_production_is_correct str prod_idx (orb b1 b2) (ret_orb_production rv1 rv2);
      ret_production_cons_is_correct
      : forall str offset len split_loc prod_idx it its b1 b2 rv1 rv2,
          to_production prod_idx = cons it its
          -> parse_item_is_correct (substring offset (min split_loc len) str) it b1 rv1
          -> parse_production_is_correct (substring (offset + split_loc) (len - split_loc) str) (production_tl prod_idx) b2 rv2
          -> parse_production_is_correct (substring offset len str) prod_idx (andb b1 b2) (ret_production_cons rv1 rv2);
      ret_orb_productions_base_is_correct
      : forall str prods,
          parse_productions_is_correct str prods false ret_orb_productions_base;
      ret_orb_productions_is_correct
      : forall str p ps b1 b2 rv1 rv2,
          parse_production_is_correct str p b1 rv1
          -> parse_productions_is_correct str ps b2 rv2
          -> parse_productions_is_correct str (p::ps) (orb b1 b2) (ret_orb_productions rv1 rv2);
      ret_nt_is_correct
      : forall str nt b v,
          is_valid_nonterminal initial_nonterminals_data nt = true
          -> parse_productions_is_correct str (nonterminal_to_production nt) b v
          -> parse_nt_is_correct str nt b (ret_nt (to_nonterminal nt) v);
      ret_nt_invalid_is_correct
      : forall str nt,
          parse_nt_is_correct str nt false ret_nt_invalid
    }.

  Section better_proper.
    Local Existing Instances parse_nt_is_correct_Proper parse_item_is_correct_Proper parse_production_is_correct_Proper parse_productions_is_correct_Proper.
    Local Ltac t :=
      repeat intro; subst;
      match goal with
      | [ H : beq _ _ |- _ ] => symmetry in H
      end;
      let R := match goal with |- ?R _ _ _ _ => R end in
      let c := constr:(_ : Proper _ R) in
      eapply c; first [ eassumption | reflexivity ].
    Global Instance parse_nt_is_correct_Proper_useful
      : Proper (eq ==> beq ==> eq ==> eq ==> eq ==> Basics.flip Basics.impl) (@parse_nt_is_correct).
    Proof. t. Qed.
    Global Instance parse_item_is_correct_Proper_useful
      : Proper (eq ==> beq ==> eq ==> eq ==> eq ==> Basics.flip Basics.impl) (@parse_item_is_correct).
    Proof. t. Qed.
    Global Instance parse_production_is_correct_Proper_useful
      : Proper (eq ==> beq ==> eq ==> eq ==> eq ==> Basics.flip Basics.impl) (@parse_production_is_correct).
    Proof. t. Qed.
    Global Instance parse_productions_is_correct_Proper_useful
      : Proper (eq ==> beq ==> eq ==> eq ==> eq ==> Basics.flip Basics.impl) (@parse_productions_is_correct).
    Proof. t. Qed.
  End better_proper.
End correctness.

Create HintDb generic_parser_correctness discriminated.
Hint Resolve ret_Terminal_true_correct ret_Terminal_false_correct ret_NonTerminal_true_correct ret_NonTerminal_false_correct ret_production_nil_true_is_correct ret_production_nil_false_is_correct ret_orb_production_base_is_correct ret_orb_production_is_correct ret_production_cons_is_correct ret_orb_productions_base_is_correct ret_orb_productions_is_correct ret_nt_is_correct ret_nt_invalid_is_correct : generic_parser_correctness.
