(** * Extensionality of boolean recognizer *)
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BooleanRecognizer.
Require Import Fiat.Parsers.GenericRecognizerExt.

Set Implicit Arguments.
Section recursive_descent_parser.
  Context {Char} {HSL : StringLikeMin Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {rdata : @parser_removal_dataT' _ G _}.

  Local Existing Instance boolean_gendata.

  Local Notation nt_ret_T := bool (only parsing).

  Global Instance parse_item'_Proper
  : Proper (eq ==> pointwise_relation _ eq ==> eq ==> eq ==> eq ==> eq) (parse_item')
    := parse_item'_Proper.

  Definition parse_item'_ext
    : forall (str : String)
             (str_matches_nonterminal str_matches_nonterminal' : nonterminal_carrierT -> _)
             (ext : forall s, str_matches_nonterminal s = str_matches_nonterminal' s)
             (offset : nat)
             (len : nat)
             (it : item Char),
      parse_item' str str_matches_nonterminal offset len it
      = parse_item' str str_matches_nonterminal' offset len it
    := parse_item'_ext.

  Section production.
    Definition parse_production'_for_ext
               {len0} str
               (parse_nonterminal parse_nonterminal'
                : forall _ _ _, nt_ret_T)
               ext
      : forall splits splits'
               (Hsplits : forall idx offset len, splits idx str offset len = splits' idx str offset len)
               (offset : nat)
               (len0_minus_len : nat)
               prod_idx,
        parse_production'_for (len0 := len0) str parse_nonterminal splits offset len0_minus_len prod_idx
        = parse_production'_for (len0 := len0) str parse_nonterminal' splits' offset len0_minus_len prod_idx
      := parse_production'_for_ext str _ _ ext.

    Definition parse_production'_ext
               {len0} str
               (parse_nonterminal parse_nonterminal'
                : forall _ _ _, nt_ret_T)
               ext
      : forall (offset : nat)
               (len0_minus_len : nat)
               prod_idx,
        parse_production' (len0 := len0) str parse_nonterminal offset len0_minus_len prod_idx
        = parse_production' (len0 := len0) str parse_nonterminal' offset len0_minus_len prod_idx
      := parse_production'_ext str _ _ ext.
  End production.

  Global Instance parse_production'_for_Proper {str len0}
  : Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq)))
              ==> (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq))))
              ==> eq
              ==> eq
              ==> eq
              ==> eq)
           (parse_production'_for str (len0 := len0))
    := parse_production'_for_Proper.

  Global Instance parse_production'_Proper {str len0}
    : Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq)))
                ==> eq
                ==> eq
                ==> eq
                ==> eq)
             (parse_production' str (len0 := len0))
    := parse_production'_Proper.

  Section productions.
    Definition parse_productions'_ext
               {len0} str
               (parse_nonterminal parse_nonterminal'
                : forall _ _ _, nt_ret_T)
               ext
      : forall (offset : nat)
               (len0_minus_len : nat)
               (prods : list production_carrierT),
        parse_productions' (len0 := len0) str parse_nonterminal offset len0_minus_len prods
        = parse_productions' (len0 := len0) str parse_nonterminal' offset len0_minus_len prods
      := parse_productions'_ext str _ _ ext.
  End productions.

  Global Instance parse_productions'_Proper {str len0}
  : Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ eq)))
              ==> eq
              ==> eq
              ==> eq
              ==> eq)
           (parse_productions' str (len0 := len0))
    := parse_productions'_Proper.

  Section nonterminals.
    Section step.
      Context {len0 valid_len} (str : String)
              (parse_nonterminal parse_nonterminal'
               : forall (p : nat * nat),
                   Wf.prod_relation lt lt p (len0, valid_len)
                   -> forall (valid : nonterminals_listT)
                             (offset : nat) (len : nat),
                        len <= fst p -> nonterminal_carrierT -> nt_ret_T)
              (ext : forall p pf valid str len pf' nt,
                       parse_nonterminal p pf valid str len pf' nt
                       = parse_nonterminal' p pf valid str len pf' nt).

      Definition parse_nonterminal_step_ext
        : forall (valid : nonterminals_listT)
                 (offset : nat)
                 (len : nat)
                 (pf pf' : len <= len0)
                 (nt : nonterminal_carrierT),
          parse_nonterminal_step str parse_nonterminal valid offset pf nt
          = parse_nonterminal_step str parse_nonterminal' valid offset pf' nt
        := parse_nonterminal_step_ext str _ _ ext.
    End step.

    Global Instance parse_nonterminal_step_Proper {str len0 valid_len}
    : Proper ((forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (forall_relation (fun _ => pointwise_relation _ (pointwise_relation _ eq)))))))
                ==> eq
                ==> eq
                ==> forall_relation (fun _ => (fun _ _ => True) ==> eq ==> eq))
             (parse_nonterminal_step str (len0 := len0) (valid_len := valid_len))
      := parse_nonterminal_step_Proper.
  End nonterminals.
End recursive_descent_parser.
