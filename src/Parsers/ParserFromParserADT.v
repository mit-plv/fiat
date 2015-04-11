(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import ADTSynthesis.Parsers.SplitterFromParserADT.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarNotations.
Require Export ADTSynthesis.Parsers.ParserImplementationOptimized.
Require Import ADTSynthesis.ADT.ComputationalADT.
Require Import ADTSynthesis.ADTRefinement.GeneralRefinements.
Require Import ADTSynthesis.Parsers.ParserADTSpecification.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarTransfer.
Require Import ADTSynthesis.Parsers.StringLike.Core.
Require Import ADTSynthesis.Parsers.StringLike.String.
Require Import ADTSynthesis.ADTRefinement.Core.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section parser.
  Context {ls : list (String.string * productions Ascii.ascii)}.
  Local Notation G := (list_to_grammar (nil::nil) ls) (only parsing).
  Context (splitter_impl : FullySharpened (string_spec G)).

  Definition new_string_of_base_string (str : String.string)
    := (cConstructors (projT1 splitter_impl) {| StringBound.bindex := "new" |} (str : String.string)).

  Lemma new_string_of_base_string_R {str}
  : AbsR (projT2 splitter_impl) str (new_string_of_base_string str).
  Proof.
    unfold new_string_of_base_string.
    pose proof (ADTRefinementPreservesConstructors (projT2 splitter_impl) {| StringBound.bindex := "new" |} str (cConstructors (projT1 splitter_impl) {| StringBound.bindex := "new" |} str) (ReturnComputes _)) as H'';
      computes_to_inv;
      simpl in H'';
      computes_to_inv; subst; assumption.
  Qed.

  Definition new_string_of_string str : @String Ascii.ascii (adt_based_splitter splitter_impl)
    := (exist
          _
          (new_string_of_base_string str)
          (ex_intro
             _
             str
             new_string_of_base_string_R)).

  Definition parser : Parser G string_stringlike.
  Proof.
    refine (@parser ls (adt_based_splitter splitter_impl)
                    new_string_of_string
                    (fun rep str => AbsR (projT2 splitter_impl) str (` rep))
                    (@new_string_of_base_string_R) _ _);
    abstract (
        split;
        first [ (intros ????);
                simpl;
                erewrite mis_char_eq; intros; eassumption
              | (intros ???);
                simpl;
                erewrite mlength_eq; intros; eassumption
              | intros; apply mtake_R; assumption
              | intros; refine (mdrop_R _ _); assumption ]
      ).
  Defined.
End parser.
