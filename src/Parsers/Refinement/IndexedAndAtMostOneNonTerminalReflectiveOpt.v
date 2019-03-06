(** First step of a splitter refinement; indexed representation, and handle all rules with at most one nonterminal; leave a reflective goal *)
Require Import Coq.Strings.String.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.ADTNotation.BuildADT Fiat.ADTNotation.BuildADTSig.
Require Import Fiat.ADT.ComputationalADT.
Require Import Fiat.ADTRefinement.
Require Import Fiat.ADTRefinement.BuildADTRefinements.HoneRepresentation.
Require Import Fiat.Parsers.ParserADTSpecification.
Require Import Fiat.Parsers.Refinement.IndexedAndAtMostOneNonTerminalReflective.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Precompute.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.

Local Open Scope string_scope.

(* TODO: find a better place for this *)
Instance match_item_Proper {Char A}
  : Proper (eq ==> pointwise_relation _ eq ==> pointwise_relation _ eq ==> eq)
           (fun (it : Core.item Char) T NT
            => match it return A with
               | Core.Terminal t => T t
               | Core.NonTerminal nt => NT nt
               end).
Proof.
  intros []; repeat intro; subst; auto.
Qed.

Instance option_rect_Proper {A P}
  : Proper (pointwise_relation _ eq ==> eq ==> eq ==> eq)
           (@option_rect A (fun _ => P)).
Proof.
  intros ?????? []; repeat intro; subst; simpl; auto.
Qed.

Module opt0.
  Definition fst {A B} := Eval compute in @fst A B.
  Definition snd {A B} := Eval compute in @snd A B.
End opt0.
Global Arguments opt0.fst : simpl never.
Global Arguments opt0.snd : simpl never.

Module opt2.
  Definition id {A} := Eval compute in @id A.
  Definition fold_right {A B} := Eval compute in @List.fold_right A B.
  Definition uniquize_sig {A} : { v : _ | v = @Operations.List.uniquize A }.
  Proof.
    eexists.
    cbv [Operations.List.uniquize Equality.list_bin orb].
    change @List.fold_right with @fold_right.
    reflexivity.
  Defined.
  Definition uniquize {A} := Eval cbv [proj1_sig uniquize_sig] in proj1_sig (@uniquize_sig A).
  Definition ret_cases_BoolDecR := Eval compute in ret_cases_BoolDecR.
End opt2.

Module opt3.
  Definition fold_right {A B} := Eval compute in @List.fold_right A B.
End opt3.

Module opt.
  Definition map {A B} := Eval compute in @List.map A B.
  Definition flat_map {A B} := Eval compute in @List.flat_map A B.
  Definition up_to := Eval compute in @Operations.List.up_to.
  Definition length {A} := Eval compute in @List.length A.
  Definition nth {A} := Eval compute in @List.nth A.
  Definition id {A} := Eval compute in @id A.
  Definition combine {A B} := Eval compute in @List.combine A B.
  Definition string_beq := Eval compute in Equality.string_beq.
  Definition first_index_default {A} := Eval compute in @Operations.List.first_index_default A.
  Definition list_bin_eq := Eval compute in list_bin_eq.
  Definition filter_out_eq := Eval compute in filter_out_eq.
  Definition find {A} := Eval compute in @List.find A.
  Definition leb := Eval compute in Compare_dec.leb.
  Definition minus := Eval compute in minus.
  Definition drop {A} := Eval compute in @Operations.List.drop A.
  Definition andb := Eval compute in andb.
  Definition nat_rect {A} := Eval compute in @nat_rect A.
  Definition option_rect {A} := Eval compute in @option_rect A.
  Definition has_only_terminals {Char} := Eval compute in @has_only_terminals Char.
  Definition sumbool_of_bool := Eval compute in Sumbool.sumbool_of_bool.
  Local Declare Reduction red_fp := cbv [FromAbstractInterpretationDefinitions.fixedpoint_by_abstract_interpretation Fix.aggregate_state Definitions.prestate Definitions.lattice_data Definitions.state FromAbstractInterpretation.fold_grammar initial_nonterminals_data rdp_list_predata rdp_list_initial_nonterminals_data pregrammar_productions FromAbstractInterpretationDefinitions.fold_constraints FromAbstractInterpretationDefinitions.fold_productions' FromAbstractInterpretationDefinitions.fold_production' FromAbstractInterpretationDefinitions.fold_item' of_nonterminal rdp_list_of_nonterminal default_of_nonterminal Lookup_idx FromAbstractInterpretationDefinitions.fold_constraints_Proper FromAbstractInterpretationDefinitions.fold_constraints_ext FromAbstractInterpretationDefinitions.fold_productions'_ext FromAbstractInterpretationDefinitions.fold_production'_ext FromAbstractInterpretationDefinitions.fold_item'_ext FromAbstractInterpretationDefinitions.fold_constraints_extR FromAbstractInterpretationDefinitions.fold_productions'_extR FromAbstractInterpretationDefinitions.fold_production'_extR FromAbstractInterpretationDefinitions.fold_item'_extR Fix.lookup_state FromAbstractInterpretationDefinitions.fold_constraints_Proper_state_beq FromAbstractInterpretationDefinitions.fold_constraints_ProperR].
  Definition lookup_state' {G} compiled_productions :=
    Eval red_fp in
      @Fix.lookup_state
        (@FromAbstractInterpretationDefinitions.fixedpoint_by_abstract_interpretation
           Ascii.ascii nat FixedLengthLemmas.length_result_lattice
           (@FixedLengthLemmas.length_result_aidata Ascii.ascii) G
           compiled_productions).
  Definition fold_grammar' pp unix
    := Eval red_fp in
        let G := {| pregrammar_productions := pp ; nonterminals_unique := unix |} in
        (@FromAbstractInterpretation.fold_grammar
           Ascii.ascii nat
           FixedLengthLemmas.length_result_lattice
           (@FixedLengthLemmas.length_result_aidata Ascii.ascii) G).
  Definition lookup_state : FMapPositive.PositiveMap.tree (Definitions.lattice_for nat) -> nat -> Definitions.lattice_for nat.
  Proof.
    let term := match (eval cbv [lookup_state'] in @lookup_state') with
                | fun _ _ => ?term => term
                end in
    exact term.
  Defined.
  Definition fold_grammar (pp : list (string * Core.productions Ascii.ascii)) : list (opt.productions (Definitions.lattice_for nat)) -> FMapPositive.PositiveMap.t (Definitions.lattice_for nat).
  Proof.
    let term := match (eval cbv [fold_grammar'] in (@fold_grammar' pp)) with
                | fun _ => ?term => term
                end in
    exact term.
  Defined.
  Definition collapse_length_result := Eval compute in FixedLengthLemmas.collapse_length_result.
  Definition expanded_fallback_list'_body_sig {G} : { b : _ | b = @expanded_fallback_list'_body G }.
  Proof.
    eexists.
    cbv [id
           expanded_fallback_list'_body to_production_opt production_carrier_valid production_carrierT rdp_list_predata default_production_carrierT default_nonterminal_carrierT rdp_list_production_carrier_valid default_production_carrier_valid Lookup_idx FixedLengthLemmas.length_of_any FixedLengthLemmas.length_of_any nonterminals_listT rdp_list_nonterminals_listT nonterminals_length initial_nonterminals_data rdp_list_initial_nonterminals_data is_valid_nonterminal of_nonterminal remove_nonterminal ContextFreeGrammar.Core.Lookup rdp_list_of_nonterminal default_of_nonterminal grammar_of_pregrammar rdp_list_remove_nonterminal Lookup_string list_to_productions rdp_list_is_valid_nonterminal If_Then_Else
           opt.compile_productions opt.compile_production opt.compile_item opt.compile_nonterminal opt.nonterminal_names FromAbstractInterpretationDefinitions.compile_item_data_of_abstract_interpretation opt.compile_grammar
           pregrammar_nonterminals
           opt.on_terminal FromAbstractInterpretationDefinitions.on_terminal FixedLengthLemmas.length_result_aidata].
    change (@Fix.lookup_state ?v) with (@lookup_state).
    change (FromAbstractInterpretation.fold_grammar G) with (fold_grammar (pregrammar_productions G)).
    change @fst with @opt.fst.
    change @snd with @opt.snd.
    change @List.map with @map.
    change @List.length with @length.
    change Equality.string_beq with string_beq.
    change @Operations.List.first_index_default with @first_index_default.
    change RDPList.list_bin_eq with list_bin_eq.
    change RDPList.filter_out_eq with filter_out_eq.
    change @Operations.List.up_to with @up_to.
    change @List.find with @find.
    change @List.nth with @nth.
    change Compare_dec.leb with leb.
    change Datatypes.andb with andb.
    change (?x - ?y) with (minus x y).
    change @Operations.List.drop with @drop.
    change @Datatypes.nat_rect with @nat_rect.
    change @Datatypes.option_rect with @option_rect.
    change @Sumbool.sumbool_of_bool with sumbool_of_bool.
    change @FixedLengthLemmas.collapse_length_result with collapse_length_result.
    change @IndexedAndAtMostOneNonTerminalReflective.has_only_terminals with @has_only_terminals.
    reflexivity.
  Defined.
  Definition expanded_fallback_list'_body' (ps : list (String.string * Core.productions Ascii.ascii)) : default_production_carrierT -> ret_cases.
  Proof.
    let term := constr:(fun H : NoDupR _ _ => proj1_sig (@expanded_fallback_list'_body_sig {| pregrammar_productions := ps |})) in
    let term := (eval cbv [proj1_sig expanded_fallback_list'_body_sig pregrammar_productions] in term) in
    let term := match term with
                  | (fun _ => ?term) => term
                end in
    exact term.
  Defined.
  Definition expanded_fallback_list'_body (ps : list (String.string * Core.productions Ascii.ascii))
    : FMapPositive.PositiveMap.t (Definitions.lattice_for nat) -> default_production_carrierT -> ret_cases.
  Proof.
    let term := (eval cbv [expanded_fallback_list'_body'] in (@expanded_fallback_list'_body' ps)) in
    let fg := lazymatch term with context[fold_grammar ps ?v] => constr:(fold_grammar ps v) end in
    let term := match (eval pattern fg in term) with
                | ?term _ => term
                end in
    exact term.
  Defined.
  Definition ret_cases_to_comp_sig {HSLM G} : { r : _ | r = @ret_cases_to_comp HSLM G }.
  Proof.
    eexists.
    cbv [ret_cases_to_comp to_production rdp_list_predata rdp_list_to_production default_to_production Lookup_idx].
    change @Operations.List.drop with @drop.
    change @snd with @opt.snd.
    change @fst with @opt.fst.
    change @List.nth with @nth.
    change (?x - ?y) with (minus x y).
    change @List.length with @length.
    change @List.map with @map.
    reflexivity.
  Defined.
  Definition ret_cases_to_comp {HSLM G}
    := Eval cbv [proj1_sig ret_cases_to_comp_sig] in proj1_sig (@ret_cases_to_comp_sig HSLM G).

  Definition premap_expanded_fallback_list'_body (G : pregrammar' Ascii.ascii) : list (nat * (nat * nat)).
  Proof.
    let term := match (eval cbv [rindexed_spec rindexed_spec' default_production_carrierT default_nonterminal_carrierT expanded_fallback_list' forall_reachable_productions_if_eq] in (fun HSLM HSL => @rindexed_spec HSLM HSL G)) with
                | context[List.map (fun x => (x, ?f x)) ?ls] => ls
                end in
    exact term.
  Defined.
  Definition Let_In {A B} (x : A) (f : A -> B) := let y := x in f y.
  Definition map_expanded_fallback_list'_body (G : pregrammar' Ascii.ascii) fg : list ((nat * (nat * nat)) * ret_cases)
    := map (fun x => (x, @expanded_fallback_list'_body G fg x)) (premap_expanded_fallback_list'_body G).
  Local Hint Immediate FromAbstractInterpretationDefinitions.compile_item_data_of_abstract_interpretation : typeclass_instances.
  Definition expanded_fallback_list_body (G : pregrammar' Ascii.ascii) : list ((nat * (nat * nat)) * ret_cases)
    := Let_In (opt.compile_grammar G)
              (fun compiled_productions
               => Let_In
                    (fold_grammar G compiled_productions)
                    (map_expanded_fallback_list'_body G)).
End opt.

Class opt_of {T} (term : T) := mk_opt_of : T.
(*Class do_idtac {T} (x : T) := dummy_idtac : True.
Local Hint Extern 0 (do_idtac ?msg) => idtac "<infomsg>" msg "</infomsg>"; exact I : typeclass_instances.
Local Ltac cidtac term := constr:(_ : do_idtac term).
Local Ltac opt_of_context term :=
  match (eval cbv beta iota zeta in term) with
  | context G[map snd (opt.id ?ls)]
    => let G' := context G[opt.id (opt.map opt.snd ls)] in
       opt_of_context G'
  | context G[List.length (opt.id ?ls)]
    => let G' := context G[opt.id (opt.length ls)] in
       opt_of_context G'
  | context G[minus (opt.id ?x) (opt.id ?y)]
    => let G' := context G[opt.id (opt.minus x y)] in
       opt_of_context G'
  | context G[Operations.List.up_to (opt.id ?n)]
    => let G' := context G[opt.id (opt.up_to n)] in
       opt_of_context G'
  | context G[S (opt.id ?n)]
    => let G' := context G[opt.id (S n)] in
       opt_of_context G'
  | context G[ret (opt.id ?n)]
    => let G' := context G[opt.id (ret n)] in
       opt_of_context G'
  | context G[pair (opt.id ?x) (opt.id ?y)]
    => let G' := context G[opt.id (pair x y)] in
       opt_of_context G'
  | context G[cons (opt.id ?x) (opt.id ?y)]
    => let G' := context G[opt.id (cons x y)] in
       opt_of_context G'
  | context G[Operations.List.uniquize (opt.id ?beq) (opt.id ?ls)]
    => let G' := context G[opt.id (opt.uniquize beq ls)] in
       opt_of_context G'
  | context G[nth (opt.id ?n) (opt.id ?ls) (opt.id ?d)]
    => let G' := context G[opt.id (opt.nth n ls d)] in
       opt_of_context G'
  | context G[List.combine (opt.id ?a) (opt.id ?b)]
    => let G' := context G[opt.id (opt.combine a b)] in
       opt_of_context G'
  | context G[map (opt.id ?f) (opt.id ?ls)]
    => let G' := context G[opt.id (opt.map f ls)] in
       let G' := (eval cbv beta in G') in
       opt_of_context G'
  | context G[flat_map (opt.id ?f) (opt.id ?ls)]
    => let G' := context G[opt.id (opt.flat_map f ls)] in
       let G' := (eval cbv beta in G') in
       opt_of_context G'
  | context G[opt.flat_map (opt.id ?f) ?ls]
    => let G' := context G[opt.flat_map f ls] in
       opt_of_context G'
  | context G[opt.map (opt.id ?f) ?ls]
    => let G' := context G[opt.map f ls] in
       opt_of_context G'
  | context G[fun x => opt.id (@?f x)]
    => let G' := context G[opt.id f] in
       opt_of_context G'
  | context G[flat_map ?f (opt.id ?ls)]
    => let f' := constr:(fun x => _ : opt_of (f (opt.id x))) in
       let G' := context G[opt.id (opt.flat_map f' ls)] in
       let G' := (eval cbv beta in G') in
       opt_of_context G'
  | context G[map ?f (opt.id ?ls)]
    => let f' := constr:(fun x => _ : opt_of (f (opt.id x))) in
       let G' := context G[opt.id (opt.map f' ls)] in
       let G' := (eval cbv beta in G') in
       opt_of_context G'
  | context G[fold_right ?f (opt.id ?d) (opt.id ?ls)]
    => let f' := constr:(fun x => _ : opt_of (f (opt.id x))) in
       let G' := context G[opt.id (opt.fold_right f' d ls)] in
       let G' := (eval cbv beta in G') in
       opt_of_context G'
  | ?term' => term'
  end.*)
Class constr_eq {A} {B} (x : A) (y : B) := make_constr_eq : True.
Local Hint Extern 0 (constr_eq ?x ?y) => constr_eq x y; exact I : typeclass_instances.
Local Ltac opt_of term :=
  let retv :=
      lazymatch (eval cbv beta iota zeta in term) with
      | List.map snd (opt.id ?ls)
        => constr:(opt.id (opt.map opt.snd ls))
      | List.length (opt.id ?ls)
        => constr:(opt.id (opt.length ls))
      | minus (opt.id ?x) (opt.id ?y)
        => constr:(opt.id (opt.minus x y))
      | Operations.List.up_to (opt.id ?n)
        => constr:(opt.id (opt.up_to n))
      | @fst ?A ?B (opt.id ?n)
        => constr:(opt.id (@opt.fst A B n))
      | @snd ?A ?B (opt.id ?n)
        => constr:(opt.id (@opt.snd A B n))
      | S (opt.id ?n)
        => constr:(opt.id (S n))
      | Core.ret (opt.id ?n)
        => constr:(opt.id (Core.ret n))
      | pair (opt.id ?x) (opt.id ?y)
        => constr:(opt.id (pair x y))
      | cons (opt.id ?x) (opt.id ?y)
        => constr:(opt.id (cons x y))
      | Operations.List.uniquize (opt2.id ?beq) (opt.id ?ls)
        => constr:(opt2.id (opt2.uniquize beq ls))
      | Operations.List.uniquize (opt.id ?beq) (opt.id ?ls)
        => constr:(opt2.id (opt2.uniquize beq ls))
      | List.nth (opt.id ?n) (opt.id ?ls) (opt.id ?d)
        => constr:(opt.id (opt.nth n ls d))
      | List.combine (opt.id ?a) (opt.id ?b)
        => constr:(opt.id (opt.combine a b))
      | List.map (fun x : ?T => opt.id ?f) (opt.id ?ls)
        => constr:(opt.id (opt.map (fun x : T => f) ls))
      | List.map (opt.id ?f) (opt.id ?ls)
        => constr:(opt.id (opt.map f ls))
      | List.flat_map (opt.id ?f) (opt.id ?ls)
        => constr:(opt.id (opt.flat_map f ls))
      | opt.flat_map (opt.id ?f) ?ls
        => constr:(opt.flat_map f ls)
      | opt.map (opt.id ?f) ?ls
        => constr:(opt.map f ls)
      | fun x => opt.id (@?f x)
        => constr:(opt.id f)
      | List.flat_map ?f (opt.id ?ls)
        => let f' := constr:(fun x => _ : opt_of (f (opt.id x))) in
           let G' := constr:(opt.id (opt.flat_map f' ls)) in
           (eval cbv beta in G')
      | @List.map ?A ?B ?f (opt.id ?ls)
        => let f' := constr:(fun x => _ : opt_of (f (opt.id x))) in
           let G' := constr:(opt.id (@opt.map A B f' ls)) in
           let G' := (eval cbv beta in G') in
           G'
      | List.fold_right orb false (opt.id ?ls)
        => constr:(opt2.fold_right orb false ls)
      | List.fold_right orb false (opt2.id ?ls)
        => constr:(opt2.fold_right orb false ls)
      | List.fold_right ?f (opt.id ?d) (opt.id ?ls)
        => let f' := constr:(fun x => _ : opt_of (f (opt2.id x))) in
           let G' := constr:(opt2.id (opt2.fold_right f' d ls)) in
           (eval cbv beta in G')
      | List.fold_right ?f (opt.id ?d) (opt2.id ?ls)
        => let f' := constr:(fun x => _ : opt_of (f (opt2.id x))) in
           let G' := constr:(opt2.id (opt2.fold_right f' d ls)) in
           (eval cbv beta in G')
      | opt.id ?f ?x
        => constr:(opt.id (f x))
      | opt2.id ?f ?x
        => constr:(opt2.id (f x))
      | ?f (opt.id ?x)
        => let f' := opt_of f in
           let term' := (eval cbv beta iota zeta in (f' (opt.id x))) in
           match constr:(Set) with
           | _
             => let dummy := constr:(_ : constr_eq term' (f (opt.id x))) in
                term'
           | _
             => opt_of term'
           end
      | ?f (opt2.id ?x)
        => let f' := opt_of f in
           let term' := (eval cbv beta iota zeta in (f' (opt2.id x))) in
           match constr:(Set) with
           | _
             => let dummy := constr:(_ : constr_eq term' (f (opt2.id x))) in
                term'
           | _
             => opt_of term'
           end
      | ?f ?x => let f' := opt_of f in
                 let x' := opt_of x in
                 let term' := (eval cbv beta iota zeta in (f' x')) in
                 lazymatch x' with
                 | opt.id ?x''
                   => opt_of term'
                 | _ => term'
                 end(*
                 match term' with
                 | f x => term'
                 | ?term'' => opt_of term''
                 end*)
      | (fun x : ?T => ?f)
        => (eval cbv beta iota zeta in (fun x : T => _ : opt_of f))
      | if ?b then ?x else ?y
        => let b' := opt_of b in
           let x' := opt_of x in
           let y' := opt_of y in
           constr:(if b' then x' else y')
      | ?term'
        => term'
      end in
  (*let term' := (eval cbv beta iota zeta in term) in
  let dummy := match constr:(Set) with
               | _ => let dummy := constr:(_ : constr_eq retv term') in constr:(Set)
               | _ => cidtac retv
               end in*)
  retv.
Local Hint Extern 0 (opt_of ?term) => (let x := opt_of term in exact x) : typeclass_instances.

Section IndexedImpl_opt.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii} {HSIP : StringIsoProperties Ascii.ascii}
          {HSEP : StringEqProperties Ascii.ascii}.
  Context (G : pregrammar' Ascii.ascii).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Definition opt_rindexed_spec_sig : { a : ADT (string_rep Ascii.ascii String default_production_carrierT) | a = rindexed_spec G }.
  Proof.
    eexists.
    cbv [rindexed_spec rindexed_spec' default_production_carrierT default_nonterminal_carrierT expanded_fallback_list' forall_reachable_productions_if_eq].
    simpl @production_carrierT.
    cbv [default_production_carrierT default_nonterminal_carrierT].
    lazymatch goal with
    | [ |- context g[List.map (fun x => (x, expanded_fallback_list'_body x))?ls] ]
      => idtac;
           let G' := context g[opt.id (opt.expanded_fallback_list_body G)] in
           change G'
    end.
    change (@nil ?A) with (opt.id (@nil A)).
    do 2 (idtac;
          let G := match goal with |- ?G => G end in
          let G' := opt_of G in
          change G').
    unfold ret_cases_to_comp.
    reflexivity.
  Defined.

  Definition opt_rindexed_spec'
    := Eval cbv [proj1_sig opt_rindexed_spec_sig] in proj1_sig opt_rindexed_spec_sig.
  Lemma opt_rindexed_spec'_correct
  : opt_rindexed_spec' = rindexed_spec G.
  Proof.
    exact (proj2_sig opt_rindexed_spec_sig).
  Qed.

  Lemma FirstStep'
  : refineADT (string_spec G HSL) opt_rindexed_spec'.
  Proof.
    rewrite opt_rindexed_spec'_correct.
    apply FirstStep_preopt.
  Qed.

  Local Arguments opt.leb !_ !_.
  Local Arguments opt.minus !_ !_.

  Definition FirstStep0_sig
  : { sp : _ & refineADT (string_spec G HSL) sp }.
  Proof.
    eexists.
    eapply transitivityT; [ apply FirstStep' | ].
    unfold opt_rindexed_spec'.
    hone method "splits".
    {
      setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.
      simpl; subst_body; subst.
      eapply refine_under_bind_both; [ | solve [ intros; higher_order_reflexivity ] ].
      match goal with
      | [ |- ?R ?x ?y ]
        => cut (x = y);
             [ let H := fresh in
               generalize y;
               let y' := fresh in
               intros y' H; subst y'; reflexivity
             | ]
      end.
      etransitivity.
      { unfold opt.id, opt2.id.
        repeat match goal with
               | [ |- opt.length (opt.nth ?n ?ls nil) = _ ]
                 => etransitivity;
                      [ symmetry;
                        eexact (List.map_nth opt.length ls nil n
                                : opt.nth _ (opt.map _ _) 0 = opt.length (opt.nth _ _ _))
                      | ]
               | [ |- opt.map (fun x : ?T => opt.minus (opt.length (opt.snd x)) ?v) (pregrammar_productions G) = _ ]
                 => transitivity (opt.map (fun x => opt.minus x v) (opt.map opt.length (opt.map opt.snd (pregrammar_productions G))));
                      [ change @opt.map with @List.map;
                        rewrite !List.map_map;
                        reflexivity
                      | reflexivity ]
               | [ |- context[opt.length (opt.map ?f ?ls)] ]
                 => replace (opt.length (opt.map f ls)) with (opt.length ls)
                   by (change @opt.length with @List.length;
                       change @opt.map with @List.map;
                       rewrite List.map_length;
                       reflexivity)
               | [ |- context[opt.length (opt.up_to ?n)] ]
                 => replace (opt.length (opt.up_to n)) with n
                   by (change @opt.length with @List.length;
                       change @opt.up_to with @Operations.List.up_to;
                       rewrite length_up_to; reflexivity)
               | [ |- opt.map opt.length (opt.nth ?n ?ls nil) = _ ]
                 => etransitivity;
                      [ symmetry;
                        eexact (List.map_nth (opt.map opt.length) ls nil n
                                : opt.nth _ (opt.map _ _) nil = opt.map opt.length (opt.nth _ _ _))
                      | ]
               (*| [ |- opt.id _ = _ ] => apply f_equal*)
               | [ |- ret _ = _ ] => apply f_equal
               | [ |- fst _ = _ ] => apply f_equal
               | [ |- snd _ = _ ] => apply f_equal
               | [ |- opt.fst _ = _ ] => apply f_equal
               | [ |- opt.snd _ = _ ] => apply f_equal
               | [ |- S _ = _ ] => apply f_equal
               | [ |- opt.collapse_length_result _ = _ ] => apply f_equal
               | [ |- ret_length_less _ = _ ] => apply f_equal
               | [ |- ret_nat _ = _ ] => apply f_equal
               | [ |- ret_nat _ = _ ] => eapply (f_equal ret_nat)
               | [ |- ret_pick _ = _ ] => eapply (f_equal ret_pick)
               | [ |- opt.has_only_terminals _ = _ ] => apply f_equal
               | [ |- opt.up_to _ = _ ] => apply f_equal
               | [ |- cons _ _ = _ ] => apply f_equal2
               | [ |- pair _ _ = _ ] => apply f_equal2
               | [ |- cons _ _ = _ ] => eapply (f_equal2 cons)
               | [ |- pair _ _ = _ ] => eapply (f_equal2 pair)
               | [ |- orb _ _ = _ ] => apply f_equal2
               | [ |- andb _ _ = _ ] => apply f_equal2
               | [ |- opt.andb _ _ = _ ] => apply f_equal2
               | [ |- opt.drop _ _ = _ ] => apply f_equal2
               | [ |- opt.leb _ _ = _ ] => apply f_equal2
               | [ |- opt.minus _ _ = _ ] => apply f_equal2
               | [ |- opt.combine _ _ = _ ] => apply f_equal2
               | [ |- opt2.ret_cases_BoolDecR _ _ = _ ] => apply f_equal2
               | [ |- EqNat.beq_nat _ _ = _ ] => apply f_equal2
               | [ |- opt.nth _ _ _ = _ ] => apply f_equal3
               | [ |- 0 = _ ] => reflexivity
               | [ |- opt.length (pregrammar_productions G) = _ ] => reflexivity
               | [ |- opt.length ?x = _ ] => is_var x; reflexivity
               | [ |- opt.map opt.length ?x = _ ] => is_var x; reflexivity
               | [ |- nil = _ ] => reflexivity
               | [ |- false = _ ] => reflexivity
               | [ |- ret_dummy = _ ] => reflexivity
               | [ |- invalid = _ ] => reflexivity
               | [ |- ?x = _ ] => is_var x; reflexivity
               | [ |- opt.map opt.snd (pregrammar_productions G) = _ ] => reflexivity
               | [ |- opt.map opt.length (opt.map opt.snd (pregrammar_productions G)) = _ ] => reflexivity
               | [ |- opt2.uniquize opt2.ret_cases_BoolDecR _ = _ ] => apply f_equal
               | [ |- (If _ Then _ Else _) = _ ] => apply (f_equal3 If_Then_Else)
               | [ |- (match _ with true => _ | false => _ end) = _ ]
                 => apply (f_equal3 (fun (b : bool) A B => if b then A else B))
               | [ |- match ?v with nil => _ | cons x xs => _ end = _ :> ?P ]
                 => let T := type of v in
                    let A := match (eval hnf in T) with list ?A => A end in
                    etransitivity;
                      [ refine (@ListMorphisms.list_caset_Proper' A P _ _ _ _ _ _ _ _ _
                                : _ = match _ with nil => _ | cons x xs => _ end);
                        [ | intros ?? | ]
                      | reflexivity ]
               | [ |- @opt2.fold_right ?A ?B _ _ _ = _ ]
                 => refine (((_ : Proper (pointwise_relation _ _ ==> _ ==> _ ==> eq) (@List.fold_right A B)) : Proper _ (@opt2.fold_right A B)) _ _ _ _ _ _ _ _ _);
                      [ intros ?? | | ]
               | [ |- @opt.map ?A ?B ?f ?v = _ ]
                 => not constr_eq v (pregrammar_productions G);
                      let f' := head f in
                      not constr_eq f' (@opt.length);
                        refine (((_ : Proper (pointwise_relation _ _ ==> _ ==> eq) (@List.map A B)) : Proper _ (@opt.map A B)) _ _ _ _ _ _);
                        [ intro | ]
               | [ |- @opt.flat_map ?A ?B _ ?v = _ ]
                 => not constr_eq v (pregrammar_productions G);
                      refine (((_ : Proper (pointwise_relation _ _ ==> _ ==> eq) (@List.flat_map A B)) : Proper _ (@opt.flat_map A B)) _ _ _ _ _ _);
                      [ intro | ]
               | [ |- match ?v with Core.Terminal t => _ | Core.NonTerminal nt => _ end = _ :> ?P ]
                 => apply match_item_Proper; [ | intro | intro ]
               | [ |- opt.option_rect _ _ _ _ = _ ]
                 => eapply (option_rect_Proper : Proper _ (opt.option_rect _));
                      [ intro | | ]
               | _ => progress cbv beta
               end.
        reflexivity.
        reflexivity. }
      change orb with Common.opt2.orb.
      let d := match goal with d : (nat * (nat * nat))%type |- _ => d end in
      change (fst d) with (Common.opt2.fst d);
      change (snd d) with (Common.opt2.snd d);
      change (fst (Common.opt2.snd d)) with (Common.opt2.fst (Common.opt2.snd d));
      change (snd (Common.opt2.snd d)) with (Common.opt2.snd (Common.opt2.snd d)).
      change EqNat.beq_nat with Common.opt2.beq_nat.
      change andb with Common.opt2.andb.
      reflexivity.
    }
    cbv beta.
    apply reflexivityT.
  Defined.

  Definition opt_rindexed_spec0
    := Eval cbv [projT1 FirstStep0_sig] in projT1 FirstStep0_sig.

  Lemma FirstStep0
    : refineADT (string_spec G HSL) opt_rindexed_spec0.
  Proof.
    apply (projT2 FirstStep0_sig).
  Qed.

  Definition opt_rindexed_spec_method_default : String -> nat * (nat * nat) -> nat -> nat -> Comp (String * list nat).
  Proof.
    let c := (eval cbv [opt_rindexed_spec0] in opt_rindexed_spec0) in
    let c := lazymatch c with
             | context[fun r_n d d0 d1 => Bind (opt2.fold_right (@?f r_n d d0 d1) ?init ?ls) (fun a => @?retv r_n d d0 d1 a)]
               => (eval cbv beta in (fun r_n d d0 d1 => Bind (opt2.fold_right (f r_n d d0 d1) init ls) (fun a => retv r_n d d0 d1 a)))
             end in
    exact c.
  Defined.

  Section gen.
    Context c
            (Href : forall str d d0 d1, refine (opt_rindexed_spec_method_default str d d0 d1) (c str d d0 d1)).

    Definition FirstStep_sig_gen
      : { sp : _ & refineADT (string_spec G HSL) sp }.
    Proof.
      eexists.
      eapply transitivityT; [ apply FirstStep0 | ].
      unfold opt_rindexed_spec0.
      hone method "splits".
      {
        setoid_rewrite refineEquiv_pick_eq'.
        simplify with monad laws.
        simpl; subst_body; subst.
        cbv [opt_rindexed_spec_method_default] in Href.
        apply Href.
      }
      cbv beta.
      apply reflexivityT.
    Defined.

    Definition opt_rindexed_spec_gen
      := Eval cbv [projT1 FirstStep_sig_gen] in projT1 FirstStep_sig_gen.

    Lemma FirstStep_gen
      : refineADT (string_spec G HSL) opt_rindexed_spec_gen.
    Proof.
      apply (projT2 FirstStep_sig_gen).
    Qed.
  End gen.

  Definition FirstStep_sig
    : { sp : _ & refineADT (string_spec G HSL) sp }
    := FirstStep_sig_gen _ (fun _ _ _ _ => reflexivity _).

  Definition opt_rindexed_spec
    := Eval cbv [projT1 FirstStep_sig FirstStep_sig_gen opt_rindexed_spec_method_default] in projT1 FirstStep_sig.

  Lemma FirstStep
    : refineADT (string_spec G HSL) opt_rindexed_spec.
  Proof.
    apply (projT2 FirstStep_sig).
  Qed.
End IndexedImpl_opt.

Declare Reduction opt_red_FirstStep := cbv [opt_rindexed_spec opt.map opt.flat_map opt.up_to opt.length opt.nth opt.id opt.combine opt.expanded_fallback_list'_body opt.minus opt.drop opt.string_beq opt.first_index_default opt.list_bin_eq opt.filter_out_eq opt.find opt.leb opt.andb opt.nat_rect opt.option_rect opt.has_only_terminals opt.sumbool_of_bool opt.collapse_length_result opt.fst opt.snd].

Ltac opt_red_FirstStep :=
  cbv [opt_rindexed_spec opt.map opt.flat_map opt.up_to opt.length opt.nth opt.id opt.combine opt.expanded_fallback_list'_body opt.minus opt.drop opt.string_beq opt.first_index_default opt.list_bin_eq opt.filter_out_eq opt.find opt.leb opt.andb opt.nat_rect opt.option_rect opt.has_only_terminals opt.sumbool_of_bool opt.collapse_length_result opt.fst opt.snd].

Section tower.
  Context {A B}
          (proj : A -> ret_cases)
          (r_o : list nat -> Comp B)
          (retv : Comp B)
          (test : A -> bool)
          (test_true : A -> Comp (list nat)).

  Fixpoint make_tower base (ls : list A) new_comp old_comp
    := match ls with
       | nil => refine (x0 <- new_comp base; r_o x0) retv
                -> refine (x0 <- old_comp base; r_o x0) retv
       | cons x xs
         => match proj x with
            | ret_pick _
              => forall part_retv,
                (test x -> refine (test_true x) part_retv)
                -> make_tower
                     base
                     xs
                     (fun new_comp' => new_comp (If test x Then part_retv Else new_comp'))
                     (fun old_comp' => old_comp (If test x Then test_true x Else old_comp'))
            | _
              => make_tower
                   base
                   xs
                   (fun new_comp' => new_comp (If test x Then test_true x Else new_comp'))
                   (fun old_comp' => old_comp (If test x Then test_true x Else old_comp'))
            end
       end.

  Lemma refine_opt2_fold_right' base ls new_comp old_comp
        (H : forall base base',
            refine base' base
            -> refine (x0 <- new_comp base; r_o x0) retv
            -> refine (x0 <- old_comp base'; r_o x0) retv)
    : make_tower base ls new_comp old_comp.
  Proof.
    revert base new_comp old_comp H; induction ls as [|x xs IHxs]; simpl; intros.
    { eapply H; [ | eassumption ].
      reflexivity. }
    { destruct (proj x); simpl; intros;
      apply IHxs; clear IHxs; try intros ?? H';
      apply H;
      edestruct test; specialize_by (exact eq_refl); simpl;
      try setoid_rewrite_hyp'; reflexivity. }
  Qed.

  Lemma refine_opt2_fold_right base ls
    : make_tower base ls (fun x => x) (fun x => x).
  Proof.
    apply refine_opt2_fold_right'.
    intros.
    setoid_rewrite_hyp; reflexivity.
  Qed.

  Fixpoint make_tower_no_unif base (ls : list A) new_comp concl
    := match ls with
       | nil => refine (x0 <- new_comp base; r_o x0) retv
                -> concl
       | cons x xs
         => match proj x with
            | ret_pick _
              => forall part_retv,
                (test x -> refine (test_true x) part_retv)
                -> make_tower_no_unif
                     base
                     xs
                     (fun new_comp' => new_comp (If test x Then part_retv Else new_comp'))
                     concl
            | _
              => make_tower_no_unif
                   base
                   xs
                   (fun new_comp' => new_comp (If test x Then test_true x Else new_comp'))
                   concl
            end
       end.

  Lemma make_tower_const base ls v v'
        (H : refine v' v)
    : make_tower base ls (fun _ => v) (fun _ => v').
  Proof.
    induction ls as [|x xs IHxs]; simpl.
    { rewrite H; intro; assumption. }
    { destruct (proj x); intros; assumption. }
  Qed.

  Lemma make_tower_no_unif_const base ls v v'
        (H : refine v' v)
    : make_tower_no_unif base ls (fun _ => v) (refine (x0 <- v'; r_o x0) retv).
  Proof.
    induction ls as [|x xs IHxs]; simpl.
    { rewrite H; intro; assumption. }
    { destruct (proj x); intros; assumption. }
  Qed.

  Lemma refine_opt2_fold_right_no_unif base ls
    : make_tower_no_unif base ls (fun x => x) (refine (x0 <- opt2.fold_right (fun x else_case => If test x Then test_true x Else else_case) base ls; r_o x0) retv).
  Proof.
    pose proof (refine_opt2_fold_right base ls) as H.
    induction ls as [|x xs IHxs].
    { exact H. }
    { simpl in *.
      repeat match goal with
             | _ => assumption
             | [ |- context[If test ?x Then _ Else _] ] => destruct (test x) eqn:?
             | _ => progress simpl in *
             | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
             | _ => apply make_tower_const; reflexivity
             | _ => apply make_tower_no_unif_const; first [ reflexivity | assumption ]
             | _ => progress intros
             | _ => progress specialize_by (exact eq_refl)
             | _ => progress specialize_by assumption
             | _ => solve [ eauto with nocore ]
             end. }
  Qed.
End tower.

Section step_tower.
  Context {G' : pregrammar' Ascii.ascii}
          {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSEP : StringEqProperties Ascii.ascii}.
  Let A := (nat * (nat * nat) * ret_cases)%type.
  Let B := (@StringLike.String Ascii.ascii HSLM * list nat)%type.
  Let proj : A -> ret_cases := @opt0.snd _ _.
  Let pre_r_o : String -> list nat -> Comp B
    := fun str => (fun x0 : list nat => ret (str, x0)).
  Context (pre_retv : String -> nat * (nat * nat) -> nat -> nat -> Comp (String * list nat)).
  Let test_test_true : String -> nat * (nat * nat) -> nat -> nat
                       -> (A -> bool) * (A -> Comp (list nat)).
  Proof.
    intros r_o d d0 d1.
    lazymatch (eval cbv [opt_rindexed_spec_method_default] in (opt_rindexed_spec_method_default G' r_o d d0 d1)) with
    | context[opt2.fold_right
                   (fun a a0 => If @?test a Then @?test_true a Else a0)
                   ?base
                   ?ls]
      => exact (test, test_true)
    end.
  Defined.
  Let pre_test : String -> nat * (nat * nat) -> nat -> nat -> A -> bool
    := fun r_o d d0 d1 => let '(test, test_true) := test_test_true r_o d d0 d1 in test.
  Let pre_test_true : String -> nat * (nat * nat) -> nat -> nat -> A -> Comp (list nat)
    := fun r_o d d0 d1 => let '(test, test_true) := test_test_true r_o d d0 d1 in test_true.

  Lemma FirstStep_splits
        (H : forall r_o d d0 d1,
            refine (x0 <- opt2.fold_right (fun x else_case => If pre_test r_o d d0 d1 x Then pre_test_true r_o d d0 d1 x Else else_case) (ret nil) (opt.expanded_fallback_list_body G'); ret (r_o, x0)) (pre_retv r_o d d0 d1))
        res
        (Hres : refineADT (opt_rindexed_spec_gen pre_retv) (ComputationalADT.LiftcADT res))
    : FullySharpened (@string_spec G' G' eq_refl HSLM HSL).
  Proof.
    eexists.
    eapply transitivityT; [ | exact Hres ].
    eapply transitivityT; [ apply (@FirstStep _ _ _ _) | ].
    cbv [opt_rindexed_spec opt_rindexed_spec_gen].
    hone method "splits".
    2:apply reflexivityT.
    {
      setoid_rewrite General.refineEquiv_pick_eq'.
      simplify with monad laws.
      simpl; subst_body; subst.
      move H at bottom.
      cbv beta in H.
      apply H.
    }
  Defined.
End step_tower.
