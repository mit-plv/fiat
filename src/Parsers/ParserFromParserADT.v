(** Reference implementation of a splitter and parser based on that splitter *)
Require Import Coq.Strings.String.
Require Import Fiat.Common.BoundedLookup.
Require Import Fiat.ADT.ComputationalADT.
Require Import Fiat.ADTRefinement.GeneralRefinements.
Require Import Fiat.ADTRefinement.Core.
Require Import Fiat.ADTNotation.BuildADTSig.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ParserADTSpecification.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.ContextFreeGrammar.Transfer.
Require Export Fiat.Parsers.ParserImplementationOptimized.
Require Import Fiat.Parsers.SplitterFromParserADT.
Require Import Fiat.Parsers.BooleanRecognizerEquality.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Core.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope ADTSig_scope.
Local Open Scope ADT_scope.
Local Open Scope string_scope.

Section parser.
  Context {stringlike_stringlikemin : StringLikeMin Ascii.ascii}
          {stringlike_stringlike : StringLike Ascii.ascii}
          {stringlike_stringlike_properties : StringLikeProperties Ascii.ascii}.
  Context {G : pregrammar Ascii.ascii}.
  Context (Hvalid : is_true (grammar_rvalid G)).
  Context (splitter_impl : FullySharpened (string_spec G stringlike_stringlike)).

  Definition newS := ibound (indexb (@Build_BoundedIndex _ _ (ConstructorNames (string_rep Ascii.ascii String.string Carriers.default_production_carrierT)) "new" _ )).

  Definition new_string_of_base_string (str : @String _ stringlike_stringlikemin)
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

  Local Instance split_dataProj' : @split_dataT _ (adt_based_StringLikeMin_lite splitter_impl) (RDPList.rdp_list_predata (G := G))
    := { split_string_for_production idx str offset len := msplits splitter_impl idx offset len str }.

  Local Instance split_dataProj : @split_dataT _ (adt_based_splitter splitter_impl) (ParserImplementation.parser_data (adt_based_splitter splitter_impl))
    := { split_string_for_production idx str offset len := msplits splitter_impl idx offset len (proj1_sig str) }.

  Local Instance adtProj
  : @StringLikeProj
      _
      (adt_based_splitter splitter_impl)
      (adt_based_StringLikeMin_lite splitter_impl)
      (ParserImplementation.parser_data (adt_based_splitter splitter_impl))
      (ParserImplementation.parser_split_data (adt_based_splitter splitter_impl))
      (@RecognizerPreOptimized.optsplitdata _ _ _ split_dataProj')
    := { proj := @proj1_sig _ _ }.
  Proof.
    reflexivity.
    reflexivity.
    reflexivity.
  Defined.

  Definition parser' : Parser G stringlike_stringlike.
  Proof.
    refine (@parser G Hvalid (adt_based_splitter splitter_impl)
                    (adt_based_StringLikeMin_lite splitter_impl)
                    _
                    _
                    stringlike_stringlikemin
                    stringlike_stringlike
                    new_string_of_string
                    (fun rep str => AbsR (projT2 splitter_impl) str (` rep))
                    (@new_string_of_base_string_R)
                    _
                    _);
    abstract (
        split;
        unfold flip, length, take, drop, is_char, adt_based_splitter, string_type, adt_based_StringLikeMin, adt_based_StringLike, string_type_min, proj1_sig, String;
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
           {HSLM HSL HSLP}
           {G}
           Hvalid
           splitter_impl
           val (H : val = has_parse (@parser' HSLM HSL HSLP G Hvalid splitter_impl))
           valp (Hp : valp = parse (@parser' HSLM HSL HSLP G Hvalid splitter_impl))
: Parser G HSL.
Proof.
  refine {| has_parse := val ; parse := valp |};
  abstract (subst val valp; apply parser').
Defined.

Module Import local_opt.
  Import RecognizerOptimized.
  Ltac change_opt' ls nt str :=
    idtac;
    match goal with
      | _ => progress change (List.map fst ls) with (opt.map opt.fst ls)
      | _ => progress change (snd (of_string str)) with (opt.snd (of_string str))
      | _ => progress change (Equality.string_beq nt) with (opt.string_beq nt)
      | _ => progress change (Operations.List.uniquize (fun x0 y0 => Equality.string_beq (fst x0) (fst y0)) ls)
             with (opt.uniquize (fun x0 y0 => opt.string_beq (opt.fst x0) (opt.fst y0)) ls)
      | [ |- context G[Operations.List.uniquize Equality.string_beq (opt.map ?f ?ls)] ]
        => progress change (Operations.List.uniquize Equality.string_beq (opt.map f ls))
           with (opt.uniquize opt.string_beq (opt.map f ls))
      | [ |- context G[List.length (opt.uniquize ?beq ?ls)] ]
        => progress change (List.length (opt.uniquize beq ls))
           with (opt.length (opt.uniquize beq ls))
      | [ |- context G[Operations.List.first_index_default (opt.string_beq ?x) (opt.length ?ls) (opt.uniquize ?beq ?ls')] ]
        => change (Operations.List.first_index_default (opt.string_beq x) (opt.length ls) (opt.uniquize beq ls'))
           with (opt.first_index_default (opt.string_beq x) (opt.length ls) (opt.uniquize beq ls'))
      | [ |- context G[Operations.List.up_to (opt.length ?ls)] ]
        => change (Operations.List.up_to (opt.length ls))
           with (opt.up_to (opt.length ls))
      | [ |- context G[List.rev (opt.up_to ?ls)] ]
        => change (List.rev (opt.up_to ls))
           with (opt.rev (opt.up_to ls))
      | [ |- context G[List.map (fun x0 : ?T => Operations.List.up_to (Datatypes.length (snd x0)))
                                (opt.uniquize ?beq ?ls)] ]
        => change (List.map (fun x0 : T => Operations.List.up_to (Datatypes.length (snd x0)))
                            (opt.uniquize beq ls))
           with (opt.map (fun x0 : T => opt.up_to (opt.length (snd x0)))
                         (opt.uniquize beq ls))
      | [ |- context G[List.combine (opt.rev ?ls) (opt.map ?f ?ls')] ]
        => change (List.combine (opt.rev ls) (opt.map f ls'))
           with (opt.combine (opt.rev ls) (opt.map f ls'))
      | [ |- context G[snd (pcMethods ?x ?y ?z ?w ?v)] ]
        => change (snd (pcMethods x y z w v))
           with (opt.snd (pcMethods x y z w v))
      | [ |- context G[List.hd ?d (opt.uniquize ?beq ?ls)] ]
        => change (List.hd d (opt.uniquize beq ls))
           with (opt.hd d (opt.uniquize beq ls))
    end.

  Ltac change_opt ls nt str := repeat change_opt' ls nt str.
End local_opt.


Class change_snd {A} (x : A) := dummy_change_snd : A.
Hint Extern 0 (change_snd _) => change @snd with @Common.opt.snd; match goal with |- change_snd ?x => exact x end : typeclass_instances.

Local Ltac do_change_snd h impl :=
  idtac;
  let term := match goal with
                | [ |- appcontext[h ?x ?y impl] ]
                  => constr:(h x y impl)
              end in
  let v := (eval cbv beta iota zeta delta [h BuildComputationalADT.callcADTMethod ibound indexb cMethods cRep] in term) in
  let v := constr:(_ : change_snd v) in
  let v := (eval cbv beta in v) in
  change term with v; cbv beta.

Definition parser
           {HSLM : StringLikeMin Ascii.ascii}
           {HSL : StringLike Ascii.ascii}
           {HSLP : StringLikeProperties Ascii.ascii}
           {G : pregrammar Ascii.ascii}
           (Hvalid : is_true (grammar_rvalid G))
           (splitter_impl : FullySharpened (string_spec G HSL))
: Parser G HSL.
Proof.
  let term := (eval cbv beta delta [parser''] in (@parser'' HSLM HSL HSLP G Hvalid splitter_impl)) in
  refine (term _ _ _ _);
    cbv beta iota zeta delta [split_dataProj' has_parse parse parser' pdata' ParserImplementation.parser_data parser' parser transfer_parser RDPList.rdp_list_predata new_string_of_string proj adtProj proj1_sig new_string_of_base_string cConstructors StringLike.length adt_based_StringLikeMin adt_based_StringLikeMin_lite adt_based_StringLike_lite pdata BaseTypes.split_string_for_production split_dataProj adt_based_splitter BuildComputationalADT.callcADTMethod ibound indexb cMethods cRep BaseTypes.predata ParserImplementation.parser_data adt_based_StringLike RDPList.rdp_list_predata RDPList.rdp_list_nonterminals_listT list_to_grammar Valid_nonterminals RDPList.rdp_list_is_valid_nonterminal RDPList.rdp_list_remove_nonterminal string_type_min list_to_productions newS Fin.R mto_string msplits drop take is_char String length get bool_eq beq mlength mchar_at_matches mdrop mtake mget RDPList.rdp_list_initial_nonterminals_data default_nonterminal_carrierT production_carrierT default_production_carrierT char_at_matches unsafe_get RDPList.rdp_list_of_nonterminal production_tl split_data to_production RDPList.rdp_list_nonterminal_to_production ParserImplementation.parser_split_data RecognizerPreOptimized.optsplitdata RDPList.rdp_list_production_tl default_production_tl split_string_for_production RDPList.rdp_list_to_production RDPList.rdp_list_to_nonterminal Lookup grammar_of_pregrammar default_to_nonterminal default_to_production splits_for Lookup_idx Lookup_string];
    change_opt (pregrammar_productions G) nt str.
  { lazymatch goal with
    | [ |- appcontext[BooleanRecognizerOptimized.opt.opt.id
                        (BooleanRecognizerOptimized.opt.opt.first_index_default
                           ?a ?b
                           (BooleanRecognizerOptimized.opt.opt.map
                              BooleanRecognizerOptimized.opt.opt.fst (pregrammar_productions G)))] ]
      => replace (BooleanRecognizerOptimized.opt.opt.id
                    (BooleanRecognizerOptimized.opt.opt.first_index_default
                       a
                       b
                       (BooleanRecognizerOptimized.opt.opt.map
                          BooleanRecognizerOptimized.opt.opt.fst (pregrammar_productions G))))
         with (BooleanRecognizerOptimized.opt.opt.list_caset
                 (fun _ => _)
                 b
                 (fun _ _ => 0)
                 (pregrammar_productions G))
    end.
    { match goal with
      | [ |- _ = ?x :> ?T ] => instantiate (1 := x); exact_no_check (@eq_refl T x)
      end. }
    { abstract (
          clear;
          destruct (pregrammar_productions G); unfold BooleanRecognizerOptimized.opt.opt.first_index_default, BooleanRecognizerOptimized.opt.opt.id; simpl;
          [ reflexivity | ];
          change @BooleanRecognizerOptimized.opt.opt.string_beq with Equality.string_beq;
          rewrite Equality.string_lb by reflexivity;
          reflexivity
        ). } }
  { reflexivity. }
Defined.

Global Arguments parser {HSLM HSL HSLP} {G} Hvalid splitter_impl / .
