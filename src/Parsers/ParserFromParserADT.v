(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import Fiat.Parsers.SplitterFromParserADT.
Require Import Fiat.Parsers.ContextFreeGrammar.Notations.
Require Export Fiat.Parsers.ParserImplementationOptimized.
Require Import Fiat.ADT.ComputationalADT.
Require Import Fiat.ADTRefinement.GeneralRefinements.
Require Import Fiat.Parsers.ParserADTSpecification.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.ContextFreeGrammar.Transfer.
Require Import Fiat.Parsers.BooleanRecognizerEquality.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.ADTRefinement.Core.
Require Import Fiat.Common.BoundedLookup.
Require Import Fiat.ADTNotation.BuildADTSig.
Require Import Fiat.Parsers.StringLike.Core.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section parser.
  Context {stringlike_stringlike : StringLike Ascii.ascii}
          {stringlike_stringlike_properties : StringLikeProperties Ascii.ascii}.
  Context {ls : list (String.string * productions Ascii.ascii)}.
  Local Notation G := (list_to_grammar nil ls) (only parsing).
  Context (Hvalid : is_true (grammar_rvalid G)).
  Context (splitter_impl : FullySharpened (string_spec G stringlike_stringlike)).

  Definition newS := ibound (indexb (@Build_BoundedIndex _ _ (ConstructorNames (string_rep Ascii.ascii String.string Carriers.default_production_carrierT)) "new" _ )).

  Definition new_string_of_base_string (str : @String _ stringlike_stringlike)
    := (cConstructors (projT1 splitter_impl) newS str).

  Lemma new_string_of_base_string_R {str}
  : AbsR (projT2 splitter_impl) str (new_string_of_base_string str).
  Proof.
    unfold new_string_of_base_string.
    pose proof (ADTRefinementPreservesConstructors (projT2 splitter_impl) newS str (cConstructors (projT1 splitter_impl) newS str) (ReturnComputes _)) as H'';
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

  Local Instance split_dataProj : @split_dataT _ (adt_based_StringLike_lite splitter_impl) (RDPList.rdp_list_predata (G := G))
    := { split_string_for_production idx str := msplits splitter_impl idx str }.

  Local Instance adtProj
  : @StringLikeProj
      _
      (adt_based_splitter splitter_impl)
      (adt_based_StringLike_lite splitter_impl)
      (ParserImplementation.parser_data (adt_based_splitter splitter_impl))
      split_dataProj
    := { proj := @proj1_sig _ _ }.
  Proof.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
  Defined.

  Context {constT varT}
          {strC : @BooleanRecognizerOptimized.str_carrier
                    Ascii.ascii
                    (adt_based_StringLike_lite splitter_impl)
                    constT varT}.

  Definition parser' : Parser G stringlike_stringlike.
  Proof.
    refine (@parser ls Hvalid (adt_based_splitter splitter_impl)
                    (adt_based_StringLike_lite splitter_impl)
                    _
                    adtProj
                    stringlike_stringlike
                    new_string_of_string
                    (fun rep str => AbsR (projT2 splitter_impl) str (` rep))
                    (@new_string_of_base_string_R) _ _
                    _ _ strC);
    abstract (
        split;
        unfold flip, length, take, drop, is_char, adt_based_splitter, string_type, adt_based_StringLike, proj1_sig, String;
        (lazymatch goal with
        | [ |- appcontext[mis_char] ]
          => ((intros ????); erewrite mis_char_eq; intros; eassumption)
        | [ |- appcontext[mlength] ]
          => ((intros ???); erewrite mlength_eq; intros; eassumption)
        | [ |- appcontext[mtake] ]
          => (intros; refine (mtake_R _ _); assumption)
        | [ |- appcontext[mdrop] ]
          => (intros; refine (mdrop_R _ _); assumption)
         end)
      ).
  Defined.
End parser.

Definition parser''
           {HSL HSLP}
           {ls}
           Hvalid
           splitter_impl
           {constT varT strC}
           val (H : val = has_parse (@parser' HSL HSLP ls Hvalid splitter_impl constT varT strC))
: Parser (list_to_grammar nil ls) HSL.
Proof.
  refine {| has_parse := val |};
  abstract (subst val; apply parser').
Defined.

Definition parser
           {HSL : StringLike Ascii.ascii}
           {HSLP : StringLikeProperties Ascii.ascii}
           {ls : list (string * productions Ascii.ascii)}
           (Hvalid : is_true (grammar_rvalid (list_to_grammar nil ls)))
           (splitter_impl : FullySharpened (string_spec (list_to_grammar nil ls) HSL))
           {constT varT}
           {strC : @BooleanRecognizerOptimized.str_carrier
                     Ascii.ascii
                     (adt_based_StringLike_lite splitter_impl)
                     constT varT}
: Parser (list_to_grammar nil ls) HSL.
Proof.
  let term := (eval cbv beta delta [parser''] in (@parser'' HSL HSLP ls Hvalid splitter_impl constT varT strC)) in
  refine (term _ _).
  cbv beta iota zeta delta [has_parse parser' parser transfer_parser new_string_of_string proj adtProj proj1_sig new_string_of_base_string cConstructors StringLike.length adt_based_StringLike_lite mlength mtake mdrop mis_char mget mto_string msplits pdata data' BaseTypes.split_string_for_production split_dataProj adt_based_splitter BuildComputationalADT.callcADTMethod ibound indexb cMethods cRep BaseTypes.predata ParserImplementation.parser_data adt_based_StringLike RDPList.rdp_list_predata RDPList.rdp_list_nonterminals_listT list_to_grammar Valid_nonterminals RDPList.rdp_list_is_valid_nonterminal RDPList.rdp_list_remove_nonterminal list_to_productions newS Fin.R].
  cbv beta iota zeta delta [drop take is_char String length get bool_eq beq].
  match goal with
    | [ |- _ = ?x :> ?T ] => instantiate (1 := x); exact_no_check (@eq_refl T x)
  end.
Defined.

Global Arguments parser {HSL HSLP} {ls} Hvalid splitter_impl {constT varT strC} / .
