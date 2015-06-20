(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import Fiat.Parsers.SplitterFromParserADT.
Require Import Fiat.Parsers.ContextFreeGrammarNotations.
Require Export Fiat.Parsers.ParserImplementationOptimized.
Require Import Fiat.ADT.ComputationalADT.
Require Import Fiat.ADTRefinement.GeneralRefinements.
Require Import Fiat.Parsers.ParserADTSpecification.
Require Import Fiat.Parsers.ContextFreeGrammarTransfer.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.BooleanRecognizerEquality.
Require Import Fiat.ADTRefinement.Core.

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

  Local Instance adtProj
  : @StringLikeProj
      _
      (adt_based_splitter splitter_impl)
      (adt_based_StringLike_lite splitter_impl)
      (ParserImplementation.parser_data (adt_based_splitter splitter_impl))
      (fun it its str => msplits splitter_impl (it, its) str)
      (fun prods str => mrules splitter_impl prods str)
    := { proj := @proj1_sig _ _ }.
  Proof.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
  Defined.

  Context {constT varT}
          {strC : @BooleanRecognizerOptimized.str_carrier_data
                    Ascii.ascii
                    (adt_based_StringLike_lite splitter_impl)
                    constT varT}
          {strCH : @BooleanRecognizerOptimized.str_carrier_ok
                     _ _ _ _ strC}.

  Definition parser' : Parser G string_stringlike.
  Proof.
    refine (@ParserImplementationOptimized.parser'
              ls (adt_based_splitter splitter_impl)
              (adt_based_StringLike_lite splitter_impl)
              _
              _
              adtProj new_string_of_string
              (fun rep str => AbsR (projT2 splitter_impl) str (` rep))
              (@new_string_of_base_string_R) _ _
              _ _ strC _);
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

  Local Arguments new_string_of_base_string : simpl never.
  Local Arguments BooleanRecognizerOptimized.to_string / .
  Local Arguments BooleanRecognizerOptimized.of_string_var / .
  Local Arguments BooleanRecognizerOptimized.of_string_const / .
  Local Arguments mlength : simpl never.
  Local Arguments mrules : simpl never.
  Local Arguments msplits : simpl never.
  Local Arguments mdrop : simpl never.
  Local Arguments mtake : simpl never.
  Local Arguments mis_char : simpl never.
  Local Arguments cMethods : simpl never.
  Local Arguments cConstructors : simpl never.
  Local Arguments BooleanRecognizer.parse_production' / .
  Local Arguments option_rect / .
  Local Arguments option_map / .
  Local Arguments BooleanRecognizer.parse_item' / .
  Local Arguments RDPList.rdp_list_is_valid_nonterminal / .
  Local Arguments StringBound.indexb / .
  Local Arguments StringBound.bindex / .
  Local Arguments list_to_grammar / .
  Local Arguments List.hd / .
  Local Arguments projT1 / .
  Local Arguments projT2 / .
  Local Arguments cRep / .

  (*Local Arguments pcMethods / .
  Local Arguments pcConstructors / .
  Local Arguments List.nth_error / .
  Local Arguments List.map / .
  Local Arguments List.fold_right / .
  Local Arguments List.fold_left / .
  Local Arguments Datatypes.length / .
  Local Arguments List.filter / .
*)

  Local Ltac pre_do_unfold_0 term tac :=
    idtac;
    let term' := (match True with
                    | _ => eval cbv delta [term] in term
                    | _ => term
                  end) in
    let term'' := (eval cbv beta iota zeta delta [cConstructors pcConstructors cMethods pcMethods fst snd projT1 projT2 List.map List.filter List.nth_error Datatypes.length List.fold_right List.fold_left] in term') in
    tac term''.

  Local Ltac do_unfold_0_in term impl :=
    idtac;
    pre_do_unfold_0 term ltac:(fun term'' =>
                                 progress change term with term'' in impl);
    cbv beta in impl.

  Local Ltac do_unfold_0 term :=
    idtac;
    pre_do_unfold_0 term ltac:(fun term'' => progress change term with term'');
    cbv beta.

  Definition parser'' : Parser G string_stringlike.
  Proof.
    cut { impl : _ | has_parse parser' = impl }.
    { intros [impl H].
      exists impl;
        abstract (
            subst;
            apply parser'
          ). }
    { simpl.
      do_unfold_0 mis_char.
      do_unfold_0 (Datatypes.length (List.map fst ls)).
      do_unfold_0 (List.map fst ls).
      do_unfold_0 mtake.
      do_unfold_0 msplits.
      do_unfold_0 mlength.
      do_unfold_0 mrules.
      do_unfold_0 new_string_of_base_string.
      unfold List.map, List.fold_right, List.fold_left, List.nth_error, List.filter.
      eexists.
      exact eq_refl. }
  Defined.

  Definition parser''' : Parser G string_stringlike.
  Proof.
    exists (has_parse parser'');
    abstract apply parser''.
  Defined.

  Definition parser'''' : Parser G string_stringlike.
  Proof.
    let impl := (eval cbv beta iota zeta delta [has_parse parser'' parser'''] in (has_parse parser''')) in
    (exists impl).
    { exact (has_parse_sound parser'''). }
    { exact (has_parse_complete parser'''). }
  Defined.

  Definition parser : Parser G string_stringlike
    := Eval cbv delta [parser''''] in parser''''.

End parser.

Global Arguments parser {ls} splitter_impl {constT varT strC strCH}.
