Require Import Coq.Sets.Ensembles.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Precompute.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Fix.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Properties.
Require Import Fiat.Common.

Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope grammar_fixedpoint_scope.

Section fold_correctness.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {T : Type}.
  Context {fpdata : @grammar_fixedpoint_lattice_data T}
          {aidata : @AbstractInterpretation Char T fpdata}
          (prerelated : Ensemble String -> T -> Prop)
          {aicdata : AbstractInterpretationCorrectness prerelated}.
  Context (G : pregrammar' Char).
  Local Hint Immediate (compile_item_data_of_abstract_interpretation G) : typeclass_instances.
  Context (compiled_productions : list (opt.productions state))
          (Hcompiled_productions : List.map opt.compile_productions (List.map snd (pregrammar_productions G)) = compiled_productions).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Definition fold_grammar : aggregate_state (fixedpoint_by_abstract_interpretation G compiled_productions)
    := pre_Fix_grammar _ initial_nonterminals_data.

  Record ensemble_result (str : String) (fold_state : state) :=
    { er_ensemble :> Ensemble String;
      er_state :> state;
      er_related :> related er_ensemble er_state;
      er_correct :> Ensembles.In _ er_ensemble str;
      er_state_le :> er_state <= fold_state }.

  Definition er_lift {str st1 st2}
             (v : ensemble_result str st1)
             (Hle : st1 <= st2)
    : ensemble_result str st2
    := {| er_ensemble := v;
          er_state := v;
          er_related := er_related v;
          er_correct := er_correct v;
          er_state_le := transitivity (R := state_le) (er_state_le v) Hle |}.

  Definition er_combine_production n str st1 st2 (it : ensemble_result (take n str) st1) (its : ensemble_result (drop n str) st2)
    : ensemble_result str (combine_production st1 st2)
    := {| er_ensemble := ensemble_combine_production it its;
          er_state := combine_production (T := T) (it : state) (its : state);
          er_related := combine_production_correct it it (er_related it) its its (er_related its);
          er_correct := ex_intro _ n (conj (er_correct it) (er_correct its));
          er_state_le := combine_production_Proper_le (er_state_le it) (er_state_le its) |}.

  Lemma fold_le nt st
        (H : st <= fold_productions' (lookup_state fold_grammar) (opt.compile_productions (Lookup_string G nt)))
    : st <= lookup_state fold_grammar (of_nonterminal nt).
  Proof.
    unfold fold_grammar.
    rewrite pre_Fix_grammar_fixedpoint.
    unfold aggregate_step.
    rewrite lookup_state_aggregate_state_lub, <- least_upper_bound_correct_r.
    rewrite lookup_state_aggregate_prestep, (find_pre_Fix_grammar_to_lookup_state _ G).
    let v := match goal with |- context[if ?v then _ else _] => v end in
    destruct v eqn:Hvalid; unfold option_rect; [ | apply top_top ].
    unfold step_constraints.
    unfold fixedpoint_by_abstract_interpretation at 3.
    unfold fold_constraints.
    erewrite eq_opt_Lookup_idx by (eassumption || reflexivity).
    rewrite <- list_to_productions_to_nonterminal.
    change (default_to_nonterminal ?nt) with (to_nonterminal nt).
    rewrite to_of_nonterminal by (eapply initial_nonterminals_correct; assumption).
    assumption.
  Qed.

  Definition lift_ensemble_result {str nt}
             (res : ensemble_result str (fold_productions' (lookup_state fold_grammar) (opt.compile_productions (G nt))))
    : ensemble_result str (lookup_state fold_grammar (of_nonterminal nt))
    := {| er_ensemble := er_ensemble res;
          er_state := er_state res;
          er_related := er_related res;
          er_correct := er_correct res;
          er_state_le := fold_le _ _ (er_state_le res) |}.

  Section step.
    Context (state_of_parse : forall str pats, parse_of G str pats -> ensemble_result str (fold_productions' (lookup_state fold_grammar) (opt.compile_productions pats)))
            (state_of_parse_production : forall str pat, parse_of_production G str pat -> ensemble_result str (fold_production' (lookup_state fold_grammar) (opt.compile_production pat)))
            (state_of_parse_item : forall str it, parse_of_item G str it -> ensemble_result str (fold_item' (lookup_state fold_grammar) (opt.compile_item it))).

    Definition state_of_parse_item'
               str it (p : parse_of_item G str it)
      : ensemble_result str (fold_item' (lookup_state fold_grammar) (opt.compile_item it))
      := match p in parse_of_item _ _ it return ensemble_result _ (fold_item' _ (opt.compile_item it)) with
         | ParseTerminal ch P Hch Hstr
           => {| er_state := on_terminal P;
                 er_ensemble := ensemble_on_terminal P;
                 er_related := on_terminal_correct P;
                 er_correct := ex_intro _ ch (conj Hch Hstr);
                 er_state_le := reflexivity (R := state_le) _ |}
         | ParseNonTerminal nt Hvalid p' => lift_ensemble_result (state_of_parse p')
         end.

    Definition state_of_parse_production'
               str pat (p : parse_of_production G str pat)
      : ensemble_result str (fold_production' (lookup_state fold_grammar) (opt.compile_production pat))
      := match p with
         | ParseProductionNil Hlen
           => {| er_state := on_nil_production;
                 er_ensemble := ensemble_on_nil_production;
                 er_related := on_nil_production_correct (prerelated := prerelated);
                 er_correct := Hlen;
                 er_state_le := reflexivity (R := state_le) _ |}
         | ParseProductionCons n pat pats p' p's
           => er_combine_production
                n
                str
                (state_of_parse_item p')
                (state_of_parse_production p's)
         end.

    Definition state_of_parse'
               str pats (p : parse_of G str pats)
      : ensemble_result str (fold_productions' (lookup_state fold_grammar) (opt.compile_productions pats))
      := match p in parse_of _ _ pats return ensemble_result _ (fold_productions' _ (opt.compile_productions pats)) with
         | ParseHead pat pats p' => er_lift (state_of_parse_production p') (least_upper_bound_correct_l _ _)
         | ParseTail pat pats p' => er_lift (state_of_parse p') (least_upper_bound_correct_r _ _)
         end.
  End step.

  Fixpoint state_of_parse str pats (p : parse_of G str pats)
    := @state_of_parse' (@state_of_parse) (@state_of_parse_production) str pats p
  with state_of_parse_production str pat (p : parse_of_production G str pat)
    := @state_of_parse_production' (@state_of_parse_production) (@state_of_parse_item) str pat p
  with state_of_parse_item str it (p : parse_of_item G str it)
    := @state_of_parse_item' (@state_of_parse) str it p.

  Lemma fold_grammar_correct_item str nt
        (p : parse_of_item G str (NonTerminal nt))
    : exists P, P str /\ related P (lookup_state fold_grammar (opt.compile_nonterminal nt)).
  Proof.
    pose proof (@state_of_parse_item _ _ p) as p'.
    unfold fold_item' in p'.
    exists (er_ensemble p').
    split; [ apply p' | ].
    eapply (related_monotonic _); apply p'.
  Qed.

  Lemma fold_grammar_correct_item' str it
        (p : parse_of_item G str it)
    : exists P, P str /\ related P (fold_item' (lookup_state fold_grammar) (opt.compile_item it)).
  Proof.
    destruct p as [ch P Ppf Hch|] eqn:Hp.
    { simpl.
      eexists; split; [ | apply on_terminal_correct ].
      eexists; split; eassumption. }
    { apply fold_grammar_correct_item; assumption. }
  Qed.

  Lemma fold_grammar_correct_production str ps
        (p : parse_of_production G str ps)
    : exists P, P str /\ related P (fold_production' (lookup_state fold_grammar) (opt.compile_production ps)).
  Proof.
    unfold fold_production'.
    induction p as [|str n pat pats p ps IHps].
    { eexists; split; [ | apply on_nil_production_correct ]; assumption. }
    { simpl.
      apply fold_grammar_correct_item' in p.
      destruct IHps as [P [IHps0 IHps1]], p as [Ps [IHp0 IHp1]].
      eexists; split; [ | apply combine_production_correct ];
        hnf; eauto using ex_intro, conj with nocore. }
  Qed.

  Lemma fold_grammar_correct str nt
        (p : parse_of G str (Lookup G nt))
    : exists P, P str /\ related P (lookup_state fold_grammar (of_nonterminal nt)).
  Proof.
    destruct (is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt)) eqn:Hvalid.
    { apply fold_grammar_correct_item; constructor.
      { apply initial_nonterminals_correct; assumption. }
      { assumption. } }
    { unfold fold_grammar.
      rewrite (lookup_state_invalid_pre_Fix_grammar _ G) by assumption.
      do 2 esplit; [ | eapply top_related ].
      constructor. }
  Qed.
End fold_correctness.

Global Arguments fold_grammar_correct {_ HSLM HSL HSLP _ _ _ _ _} [_] {_} _ [_ _] _.
Global Arguments fold_grammar_correct_item {_ HSLM HSL HSLP _ _ _ _ _} [_] {_} _ [_ _] _.

Local Hint Immediate compile_item_data_of_abstract_interpretation : typeclass_instances.
Local Notation compiled_productions G
  := (List.map opt.compile_productions (List.map snd (pregrammar_productions G))).

Class fold_grammar_data {Char T} {fpdata : grammar_fixedpoint_lattice_data T}
      {aidata : AbstractInterpretation}
      (G : pregrammar' Char) :=
  { fgd_fold_grammar : aggregate_state (fixedpoint_by_abstract_interpretation G (compiled_productions G));
    fgd_fold_grammar_correct : pointwise_relation _ eq (lookup_state fgd_fold_grammar) (lookup_state (fold_grammar G (compiled_productions G))) }.
Coercion fgd_fold_grammar : fold_grammar_data >-> aggregate_state.

Local Definition fold_grammar_retyped {Char T} {fpdata : grammar_fixedpoint_lattice_data T}
      {aidata : AbstractInterpretation}
      (G : pregrammar' Char)
  : FMapPositive.PositiveMap.t (lattice_for T)
  := fold_grammar G (compiled_productions G).

Definition Build_fold_grammar_data' {Char T} {fpdata : grammar_fixedpoint_lattice_data T}
           {aidata : AbstractInterpretation}
           (G : pregrammar' Char)
           (fgd_fold_grammar : FMapPositive.PositiveMap.t (lattice_for T))
           (correctness : fgd_fold_grammar
                          = fold_grammar_retyped G)
  : @fold_grammar_data Char T fpdata aidata G
  := @Build_fold_grammar_data
       Char T fpdata aidata G
       fgd_fold_grammar
       (fun nt
        => f_equal
             (fun g
              => @lookup_state
                   (@fixedpoint_by_abstract_interpretation Char T fpdata aidata G (compiled_productions G))
                   g nt)
             correctness).

Ltac make_fold_grammar_data_from v :=
  let lem := lazymatch v with
             | @fold_grammar ?Char ?T ?fpdata ?aidata ?G
               => constr:(@Build_fold_grammar_data' Char T fpdata aidata G)
             end in
  let compiled_ps := lazymatch v with
                     | @fold_grammar ?Char ?T ?fpdata ?aidata ?G
                       => constr:(@opt.compile_grammar _ _ (@compile_item_data_of_abstract_interpretation _ _ fpdata aidata G) G)
                     end in
  let v := constr:(v compiled_ps) in
  let v' := (eval vm_compute in v) in
  constr:(lem v' ltac:(vm_cast_no_check (eq_refl v'))).

Ltac make_fold_grammar_data G :=
  let v := constr:(fold_grammar G) in
  make_fold_grammar_data_from v.
