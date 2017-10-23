Require Import Coq.MSets.MSetPositive.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.StringLike.FirstChar Fiat.Parsers.StringLike.LastChar Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Precompute.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Fix.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.AsciiLattice.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.ProdAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretation.
Require Import Fiat.Parsers.Refinement.EmptyLemmas.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.LogicFacts.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.

Set Implicit Arguments.

Local Open Scope grammar_fixedpoint_scope.

Definition all_possible_ascii' : PositiveSet.t
  := List.fold_right
       PositiveSet.add
       PositiveSet.empty
       (List.map (fun x => BinPos.Pos.of_nat (S x))
                 (Operations.List.up_to (S (Ascii.nat_of_ascii (Ascii.Ascii true true true true true true true true))))).

Definition all_possible_ascii : PositiveSet.t
  := Eval compute in all_possible_ascii'.

Definition pos_of_ascii (x : Ascii.ascii) : BinNums.positive
  := match Ascii.N_of_ascii x with
     | BinNums.N0 => max_ascii
     | BinNums.Npos x => x
     end.

Lemma ascii_of_pos_of_ascii x : Ascii.ascii_of_pos (pos_of_ascii x) = x.
Proof.
  destruct x; destruct_head bool; vm_compute; reflexivity.
Qed.

Lemma ascii_mem v
      (H : MSetPositive.PositiveSet.cardinal v = 1)
      ch'
      (H' : MSetPositive.PositiveSet.choose v = Some ch')
      (Hch' : pos_of_ascii (Ascii.ascii_of_pos ch') = ch')
      ch''
      (Hch'' : Ascii.ascii_of_pos ch' = ch'')
      ch
  : MSetPositive.PositiveSet.mem (pos_of_ascii ch) v = Equality.ascii_beq ch'' ch.
Proof.
  apply MSetPositive.PositiveSet.choose_spec1 in H'.
  destruct (Equality.ascii_beq ch'' ch) eqn:Hch; subst ch''.
  { apply Equality.ascii_bl in Hch; instantiate; subst ch.
    AsciiLattice.PositiveSetExtensions.BasicDec.fsetdec. }
  { AsciiLattice.PositiveSetExtensions.to_caps.
    intro; apply Hch; clear Hch.
    apply Equality.ascii_beq_true_iff.
    rewrite <- ascii_of_pos_of_ascii; apply f_equal.
    eapply AsciiLattice.PositiveSetExtensions.cardinal_one_In_same; eassumption. }
Qed.

Lemma In_all ch
  : PositiveSet.In (pos_of_ascii ch) all_possible_ascii.
Proof.
  destruct ch; destruct_head bool; vm_compute; reflexivity.
Qed.

Definition all_but (P : Ascii.ascii -> bool) : PositiveSet.t
  := PositiveSet.filter (fun n => negb (P (Ascii.ascii_of_pos n))) all_possible_ascii.

Lemma not_In_all_but P ch
  : (~PositiveSet.In (pos_of_ascii ch) (all_but P)) <-> P ch.
Proof.
  unfold all_but.
  setoid_rewrite PositiveSet.filter_spec; [ | congruence.. ].
  setoid_rewrite (LogicFacts.True_iff (In_all ch)).
  rewrite ascii_of_pos_of_ascii.
  destruct (P ch); intuition.
Qed.

Section with_empty.
  Context (G : pregrammar' Ascii.ascii).

  Definition possible_terminals_prestate
    := (@state _ might_be_empty_lattice (* is_empty? *)
        * lattice_for
            (lattice_for
               (@state _ positive_set_fpdata (* possible first terminals *)
                * @state _ positive_set_fpdata (* possible last terminals *))
             * @state _ positive_set_fpdata (* all possible terminals *)))%type.

  Global Instance possible_terminals_prestate_lattice : grammar_fixedpoint_lattice_data possible_terminals_prestate
    := _.

  Global Instance possible_terminals_aidata : @AbstractInterpretation Ascii.ascii possible_terminals_prestate _.
  Proof.
    refine (@prod_aidata_dep
              _ _ _ _ _
              on_terminal
              (@on_nil_production Ascii.ascii _ _ might_be_empty_aidata)
              (@precombine_production Ascii.ascii _ _ might_be_empty_aidata)
              (prod_on_terminal
                 (prod_on_terminal
                    (fun P => constant (all_but P))
                    (fun P => constant (all_but P)))
                 (fun P => constant (all_but P)))
              (prod_on_nil_production
                 (prod_on_nil_production
                    (constant all_possible_ascii)
                    (constant all_possible_ascii))
                 (constant all_possible_ascii))
              (fun xmbe ymbe
               => prod_precombine_production_nondep
                    (prod_precombine_production_nondep
                       (fun x' y'
                        => constant (if collapse_might_be_empty xmbe
                                     then PositiveSet.inter x' y'
                                     else x'))
                       (fun x' y'
                        => constant (if collapse_might_be_empty ymbe
                                     then PositiveSet.inter x' y'
                                     else y')))
                    (fun x' y'
                     => constant (PositiveSet.inter x' y')))
              _ _).
    intros x0 y0 H0 x1 y1 H1 x2 y2 H2 x3 y3 H3.
    repeat match goal with
           | [ H : is_true (state_beq ?x ?y) |- context[collapse_might_be_empty ?x] ]
             => replace (collapse_might_be_empty x)
                with (collapse_might_be_empty y)
               by (rewrite H; reflexivity);
                  clear x H
           end.
    repeat first [ eapply @prod_precombine_production_nondep_Proper
                 | eassumption
                 | match goal with
                   | [ |- context[collapse_might_be_empty ?v] ]
                     => destruct (collapse_might_be_empty v)
                   end ];
      clear;
      abstract (
          repeat intro; simpl in *;
          PositiveSetExtensions.to_caps;
          PositiveSetExtensions.simplify_sets; reflexivity
        ).
  Defined.
End with_empty.

Section correctness.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}.

  Definition possible_accurate
    : forall (P : String -> Prop) (st : possible_terminals_prestate), Prop
    := prod_prerelated
         might_be_empty_accurate
         (prod_prerelated
            (prod_prerelated
               (fun P st
                => forall str, P str -> for_first_char str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st))
               (fun P st
                => forall str, P str -> for_last_char str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st)))
            (fun P st
             => forall str, P str -> forall_chars str (fun ch => ~PositiveSet.In (pos_of_ascii ch) st))).

  Local Ltac pull_lattice_for_rect :=
    repeat lazymatch goal with
           | [ |- context G[match ?v with ⊤ => ?T | ⊥ => ?B | constant x => @?C x end] ]
             => let RT := type of T in
                let G' := context G[lattice_for_rect (fun _ => RT) T C B v] in
                change G'
           | [ |- context G[fun k : ?KT => match @?v k with ⊤ => @?T k | ⊥ => @?B k | constant x => @?C k x end] ]
             => let RT := match type of T with forall k, @?RT k => RT end in
                let G' := context G[fun k : KT => lattice_for_rect (fun _ => RT k) (T k) (C k) (B k) (v k)] in
                change G'; cbv beta
           | [ |- context G[fun k : ?KT => ?f match @?v k with ⊤ => @?T k | ⊥ => @?B k | constant x => @?C k x end (@?arg k)] ]
             => let RT := match type of T with forall k, @?RT k => RT end in
                let G' := context G[fun k : KT => f (lattice_for_rect (fun _ => RT k) (T k) (C k) (B k) (v k)) (arg k)] in
                change G'; cbv beta
           | [ |- context G[fun k : ?KT => ?f (@?arg k) match @?v k with ⊤ => @?T k | ⊥ => @?B k | constant x => @?C k x end] ]
             => let RT := match type of T with forall k, @?RT k => RT end in
                let G' := context G[fun k : KT => f (arg k) (lattice_for_rect (fun _ => RT k) (T k) (C k) (B k) (v k))] in
                change G'; cbv beta
           end;
    rewrite !(fun A T T' x y z => lattice_for_rect_pull (A := A) (lattice_for_rect (T := T) (fun _ => T') x y z));
    setoid_rewrite (fun A T T' x y z => lattice_for_rect_pull (A := A) (lattice_for_rect (T := T) (fun _ => T') x y z)).

  Local Ltac handle_match_two_lattice_either_bottom_same :=
    idtac;
    lazymatch goal with
    | [ |- match ?l1 with ⊤ => match ?l2 with _ => _ end | ⊥ => ?P | _ => _ end ]
      => let H := fresh in
         assert (H : (l1 = ⊥ \/ l2 = ⊥) \/ (l1 <> ⊥ /\ l2 <> ⊥))
           by (destruct l1;
               [ destruct l2; [ right; split; congruence.. | left; right; reflexivity ]..
               | left; left; reflexivity ]);
         destruct H as [H|H];
         [ cut P; [ destruct l1, l2; trivial; destruct H; congruence | ]
         | destruct l1, l2, H; try exact I; try congruence; [] ]
    end.

  Local Ltac clear_unused_T T :=
    repeat match goal with
           | [ x : T |- _ ]
             => lazymatch goal with
                | [ |- context[x] ] => fail
                | _ => clear dependent x
                end
           end.

  Local Ltac t_step :=
    idtac;
    match goal with
    | [ |- ?R ?x ?x ] => reflexivity
    | _ => assumption
    | _ => congruence
    | _ => tauto
    | _ => progress unfold Proper, respectful, possible_accurate, flip, PositiveSetBoundedLattice.lift_ltb, ensemble_least_upper_bound, ensemble_on_terminal, ensemble_on_nil_production, prestate_le, ensemble_combine_production, Equality.prod_beq, might_be_empty_accurate in *
    | _ => progress intros
    | _ => progress simpl in *
    | [ H : is_true (?a || (?b && negb ?a)) |- _ ]
      => apply simplify_bool_expr' in H;
         [ | clear; unfold state_le; simpl; bool_congr_setoid; tauto ]
    | [ |- context[(?a || (?b && negb ?a))%bool] ]
      => rewrite (@simplify_bool_expr a b) by (clear; unfold state_le; simpl; bool_congr_setoid; tauto)
    | [ H : forall x y, _ -> (?f x <-> ?g y) |- _ ]
      => setoid_rewrite (fun x => H x x (reflexivity _));
         clear f H
    | [ H : lattice_for_related _ _ ?x |- _ ] => is_var x; destruct x
    | [ |- lattice_for_related _ _ ?x ] => is_var x; destruct x
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | _ => progress destruct_head ex
    | _ => progress destruct_head and
    | _ => progress subst
    | _ => progress bool_congr_setoid
    | _ => progress PositiveSetExtensions.simplify_sets
    | _ => progress PositiveSetExtensions.to_caps
    | [ H : is_true (is_char ?str _) |- forall_chars ?str _ ]
      => setoid_rewrite <- (forall_chars_singleton _ _ _ H)
    | [ H : is_true (is_char ?str _) |- for_first_char ?str _ ]
      => setoid_rewrite <- (for_first_char_singleton _ _ _ H)
    | [ H : is_true (is_char ?str _) |- for_last_char ?str _ ]
      => setoid_rewrite <- (for_last_char_singleton _ _ _ H)
    | _ => progress autorewrite with sets in *
    | [ H : PositiveSet.Subset ?x _ |- forall_chars _ (fun ch => ~PositiveSet.In _ ?x) ]
      => setoid_subst x
    | [ H : PositiveSet.Subset ?x _ |- for_first_char _ (fun ch => ~PositiveSet.In _ ?x) ]
      => setoid_subst x
    | [ H : PositiveSet.Subset ?x _ |- for_last_char _ (fun ch => ~PositiveSet.In _ ?x) ]
      => setoid_subst x
    | _ => solve [ eauto using forall_chars_nil, for_first_char_nil, for_last_char_nil with nocore
                 | auto with sets
                 | exfalso; unfold not in *; eauto with nocore ]
    | _ => progress PositiveSetExtensions.push_In
    | [ H : forall str, ?P str -> forall_chars str _, H' : ?P _ |- _ ]
      => unique pose proof (H _ H')
    | [ H : forall str, ?P str -> for_first_char str _, H' : ?P _ |- _ ]
      => unique pose proof (H _ H')
    | [ H : forall str, ?P str -> for_last_char str _, H' : ?P _ |- _ ]
      => unique pose proof (H _ H')
    | _ => eapply forall_chars_Proper; [ reflexivity | intros ?? | eassumption ];
           cbv beta in *; tauto
    | _ => progress destruct_head or
    | _ => progress destruct_head nonemptyT
    | [ |- ~(or _ _) ] => intro
    | _ => setoid_rewrite not_In_all_but
    | [ H : forall v, ~?P v |- context[?P _] ]
      => setoid_rewrite (fun v => False_iff (H v))
    | _ => progress setoid_rewrite_logic
    | [ H : forall_chars (take ?n ?str) (fun ch => ~@?P ch),
            H' : forall_chars (drop ?n ?str) (fun ch => ~@?P' ch)
        |- forall_chars ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => setoid_rewrite (forall_chars__split str _ n); split
    | [ H : for_first_char ?str (fun ch => ~@?P ch) |- for_first_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_first_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_first_char ?str (fun ch => ~@?P' ch) |- for_first_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_first_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_last_char ?str (fun ch => ~@?P ch) |- for_last_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_last_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_last_char ?str (fun ch => ~@?P' ch) |- for_last_char ?str (fun ch => ~(@?P ch /\ @?P' ch)) ]
      => eapply for_last_char_Proper; [ reflexivity | intros ?? | eexact H ]
    | [ H : for_first_char (drop ?x ?str) _, H' : for_first_char (take ?x ?str) _ |- for_first_char ?str _ ]
      => rewrite (for_first_char__split str _ x); destruct x; [ left | right ]; (split; [ omega | ])
    | [ H : for_last_char (drop ?x ?str) _, H' : for_last_char (take ?x ?str) _ |- for_last_char ?str _ ]
      => rewrite (for_last_char__split str _ x); destruct (Compare_dec.le_lt_dec (length str) x); [ right | left ]; (split; [ assumption | ])
    | [ H : forall str, ?P str -> length str <> 0, H' : ?P (take 0 ?str') |- _ ]
      => exfalso; apply (H _ H'); rewrite take_length; omega_with_min_max
    | [ H : forall str, ?P str -> length str <> 0, Hlt : (length ?str' <= ?x)%nat, H' : ?P (drop ?x ?str') |- _ ]
      => exfalso; apply (H _ H'); rewrite drop_length; omega_with_min_max
    | [ |- context[collapse_might_be_empty ?st] ]
      => is_var st; destruct st
    | [ H : PositiveSet.Subset ?x _ |- PositiveSet.Subset (PositiveSet.inter _ _) _ ]
      => progress setoid_subst_rel PositiveSet.Subset; auto with sets
    | _ => rewrite ascii_of_pos_of_ascii
    end.

  Local Ltac t := repeat t_step.

  Global Instance constant_inter_Proper
    : Proper (prestate_le ==> prestate_le ==> state_le) (fun x' y' => constant (PositiveSet.inter x' y')).
  Proof. t. Qed.

  Local Ltac t_combine_pre :=
    repeat first [ assumption
                 | progress intros
                 | progress subst
                 | progress cbv [prod_prerelated ensemble_combine_production lattice_for_related might_be_empty_accurate lattice_for_combine_production] in *
                 | progress simpl in *
                 | progress destruct_head prod
                 | progress destruct_head and
                 | progress clear_unused_T (lattice_for PositiveSet.t) ].
  Local Ltac t_combine :=
    t_combine_pre;
    pull_lattice_for_rect;
    unfold lattice_for_rect; simpl; handle_match_two_lattice_either_bottom_same;
    t.

  Global Instance possible_aicdata
    : AbstractInterpretationCorrectness possible_accurate
    := { prerelated_ext
         := prod_prerelated_ext
              (@prerelated_ext Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_prerelated_ext (prod_prerelated_ext _ _) _);
         related_monotonic
         := prod_related_monotonic
              (@related_monotonic Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_related_monotonic (prod_related_monotonic _ _) _);
         lub_correct
         := prod_lub_correct
              (@lub_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_lub_correct (prod_lub_correct _ _) _);
         on_terminal_correct
         := prod_on_terminal_correct
              (@on_terminal_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_on_terminal_correct (prod_on_terminal_correct _ _) _);
         on_nil_production_correct
         := prod_on_nil_production_correct
              (@on_nil_production_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_on_nil_production_correct (prod_on_nil_production_correct _ _) _);
         precombine_production_Proper_le
         := prod_precombine_production_dep_Proper_le
              (@precombine_production_Proper_le Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (prod_precombine_production_nondep_dep_Proper_le (prod_precombine_production_nondep_dep_Proper_le _ _) _);
         combine_production_correct
         := prod_combine_production_dep_correct
              (@combine_production_correct Ascii.ascii _ _ _ _ _ _ _ might_be_empty_aicdata)
              (fun P1 st1 st10 R10 R1 P2 st2 st20 R20 R2
               => prod_combine_production_nondep_correct_specific
                    _ _ _ _ _ _ _ _
                    (fun st1v Hst1v st2v Hst2v
                     => prod_combine_production_nondep_correct_specific
                          _ _ _ _ _ _ _ _ _ _)
                    _)
       }.
  Proof.
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { t. }
    { auto with nocore. }
    { auto with nocore. }
    { subst; destruct_head_hnf and; assumption. }
    { subst; destruct_head_hnf and; assumption. }
    { t_combine. }
    { t_combine. }
    { t_combine. }
  Qed.
End correctness.

Definition possible_data (G : pregrammar' Ascii.ascii)
  := @fold_grammar_data _ _ _ possible_terminals_aidata G.
Existing Class possible_data.

Definition possible_characters_result := PositiveSet.t.
Record possible_result :=
  { might_be_empty_of_pr : bool;
    possible_first_characters_of_pr : possible_characters_result;
    possible_last_characters_of_pr : possible_characters_result;
    all_possible_characters_of_pr : possible_characters_result }.

Definition make_all_possible_result (negated_set : lattice_for PositiveSet.t) : possible_characters_result
  := match negated_set with
     | ⊤ => all_possible_ascii
     | constant v' => PositiveSet.filter (fun ch => negb (PositiveSet.mem ch v')) all_possible_ascii
     | ⊥ => PositiveSet.empty
     end.

Definition norm_lattice_prod {A B} (x : lattice_for (lattice_for A * lattice_for B)) : lattice_for A * lattice_for B
  := match x with
     | ⊤ => (⊤, ⊤)
     | constant v => v
     | ⊥ => (⊥, ⊥)
     end.

Definition collapse_to_possible_result (x : lattice_for possible_terminals_prestate) : possible_result
  := let x := norm_lattice_prod x in
     let x0 := fst x in
     let x123 := norm_lattice_prod (snd x) in
     let '(x12, x3) := (fst x123, snd x123) in
     let x12 := norm_lattice_prod x12 in
     let '(x1, x2) := (fst x12, snd x12) in
     {| might_be_empty_of_pr := collapse_might_be_empty x0;
        possible_first_characters_of_pr := make_all_possible_result x1;
        possible_last_characters_of_pr := make_all_possible_result x2;
        all_possible_characters_of_pr := make_all_possible_result x3 |}.

Definition is_possible_character_of (v : possible_characters_result) (ch : Ascii.ascii) : bool
  := PositiveSet.mem (pos_of_ascii ch) v.
Coercion is_possible_character_of : possible_characters_result >-> Funclass.

Local Declare Reduction opt_possible :=
  cbv [FromAbstractInterpretationDefinitions.fixedpoint_by_abstract_interpretation Definitions.prestate Definitions.lattice_data Fix.lookup_state].

Section defs.
  Context (G : pregrammar' Ascii.ascii)
          {pdata : possible_data G}.
  Local Hint Immediate (compile_item_data_of_abstract_interpretation G) : typeclass_instances.

  Definition characters_set_to_ascii_list (s : PositiveSet.t)
    : list Ascii.ascii
    := List.map Ascii.ascii_of_pos (PositiveSet.elements s).

  Definition all_possible_characters_of_nt
    : String.string -> possible_characters_result
    := Eval opt_possible in fun nt => all_possible_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).
  Definition unfold_all_possible_characters_of_nt
    : all_possible_characters_of_nt = fun nt => all_possible_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt)))
    := eq_refl.

  Definition all_possible_ascii_of_nt (nt : String.string)
    : list Ascii.ascii
    := characters_set_to_ascii_list (all_possible_characters_of_nt nt).

  Definition might_be_empty_of_pr_nt
    : String.string -> bool
    := Eval opt_possible in fun nt => might_be_empty_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).
  Definition unfold_might_be_empty_of_pr_nt
    : might_be_empty_of_pr_nt = fun nt => might_be_empty_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt)))
    := eq_refl.

  Definition possible_first_characters_of_nt
    : String.string -> possible_characters_result
    := Eval opt_possible in fun nt => possible_first_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).
  Definition unfold_possible_first_characters_of_nt
    : possible_first_characters_of_nt = fun nt => possible_first_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt)))
    := eq_refl.

  Definition possible_first_ascii_of_nt (nt : String.string)
    : list Ascii.ascii
    := characters_set_to_ascii_list (possible_first_characters_of_nt nt).

  Definition possible_last_characters_of_nt
    : String.string -> possible_characters_result
    := Eval opt_possible in fun nt => possible_last_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt))).
  Definition unfold_possible_last_characters_of_nt
    : possible_last_characters_of_nt = fun nt => possible_last_characters_of_pr (collapse_to_possible_result (lookup_state pdata (@of_nonterminal _ (@rdp_list_predata _ G) nt)))
    := eq_refl.

  Definition possible_last_ascii_of_nt (nt : String.string)
    : list Ascii.ascii
    := characters_set_to_ascii_list (possible_last_characters_of_nt nt).

  Definition all_possible_characters_of_production
    : production Ascii.ascii -> possible_characters_result
    := Eval opt_possible in fun ps => all_possible_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps))).
  Definition unfold_all_possible_characters_of_production
    : all_possible_characters_of_production = fun ps => all_possible_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps)))
    := eq_refl.

  Definition all_possible_ascii_of_production (ps : production Ascii.ascii)
    : list Ascii.ascii
    := characters_set_to_ascii_list (all_possible_characters_of_production ps).

  Definition might_be_empty_of_pr_production
    : production Ascii.ascii -> bool
    := Eval opt_possible in fun ps => might_be_empty_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps))).
  Definition unfold_might_be_empty_of_pr_production
    : might_be_empty_of_pr_production = fun ps => might_be_empty_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps)))
    := eq_refl.

  Definition possible_first_characters_of_production
    : production Ascii.ascii -> possible_characters_result
    := Eval opt_possible in fun ps => possible_first_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps))).
  Definition unfold_possible_first_characters_of_production
    : possible_first_characters_of_production = fun ps => possible_first_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps)))
    := eq_refl.

  Definition possible_first_ascii_of_production (ps : production Ascii.ascii)
    : list Ascii.ascii
    := characters_set_to_ascii_list (possible_first_characters_of_production ps).

  Definition possible_last_characters_of_production
    : production Ascii.ascii -> possible_characters_result
    := Eval opt_possible in fun ps => possible_last_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps))).
  Definition unfold_possible_last_characters_of_production
    : possible_last_characters_of_production = fun ps => possible_last_characters_of_pr (collapse_to_possible_result (fold_production' (lookup_state pdata) (opt.compile_production ps)))
    := eq_refl.

  Definition possible_last_ascii_of_production (ps : production Ascii.ascii)
    : list Ascii.ascii
    := characters_set_to_ascii_list (possible_last_characters_of_production ps).
End defs.
Global Arguments all_possible_characters_of_nt G {_} _.
Global Arguments all_possible_ascii_of_nt G {_} _.
Global Arguments might_be_empty_of_pr_nt G {_} _.
Global Arguments possible_first_characters_of_nt G {_} _.
Global Arguments possible_first_ascii_of_nt G {_} _.
Global Arguments possible_last_characters_of_nt G {_} _.
Global Arguments possible_last_ascii_of_nt G {_} _.
Global Arguments all_possible_characters_of_production G {_} _.
Global Arguments all_possible_ascii_of_production G {_} _.
Global Arguments might_be_empty_of_pr_production G {_} _.
Global Arguments possible_first_characters_of_production G {_} _.
Global Arguments possible_first_ascii_of_production G {_} _.
Global Arguments possible_last_characters_of_production G {_} _.
Global Arguments possible_last_ascii_of_production G {_} _.

Section correctness_lemmas.
  Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          (G : pregrammar' Ascii.ascii)
          {pdata : possible_data G}
          (nt : String.string)
          (ps : production Ascii.ascii)
          (str : String).

  Local Ltac pre_correct_t :=
    rewrite
      ?unfold_all_possible_characters_of_nt,
    ?unfold_might_be_empty_of_pr_nt,
    ?unfold_possible_first_characters_of_nt,
    ?unfold_possible_last_characters_of_nt,
    ?unfold_all_possible_characters_of_production,
    ?unfold_might_be_empty_of_pr_production,
    ?unfold_possible_first_characters_of_production,
    ?unfold_possible_last_characters_of_production;
    try (let x := match goal with
                  | [ |- ?v = _ ] => head v
                  end in
         unfold x).

  Local Ltac correct_t_step :=
    idtac;
    match goal with
    | _ => assumption
    | _ => tauto
    | [ |- ?R ?x ?x ] => reflexivity
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | [ |- context[fold_production' (lookup_state fgd_fold_grammar) _] ]
      => setoid_rewrite fgd_fold_grammar_correct
    | _ => rewrite fgd_fold_grammar_correct
    | [ p : parse_of_item _ _ _ |- context[@fixedpoint_by_abstract_interpretation _ _ _ ?aidata ?G] ]
      => apply (@fold_grammar_correct_item _ _ _ _ _ _ aidata _ _ _ _ eq_refl) in p
    | [ p : parse_of_production _ _ _ |- context[@fixedpoint_by_abstract_interpretation _ _ _ ?aidata ?G] ]
      => apply (@fold_grammar_correct_production _ _ _ _ _ _ aidata _ _ _ _ eq_refl) in p
    | [ p : parse_of _ _ _ |- context[@fixedpoint_by_abstract_interpretation _ _ _ ?aidata ?G] ]
      => apply (@fold_grammar_correct _ _ _ _ _ _ aidata _ _ _ _ eq_refl) in p
    | [ H : context[lookup_state _ ?nt] |- context[lookup_state _ ?nt'] ]
      => lazymatch constr:((nt, nt')) with
         | (opt.compile_nonterminal _, of_nonterminal _)
           => change nt with nt' in *
         end
    | [ |- context G[lookup_state ?g ?nt] ]
      => (* fix implicits *)
      let G' := context G[lookup_state g nt] in
      change G';
      destruct (lookup_state g nt) eqn:?
    | [ |- context[fold_production' ?f ?ps] ]
      => destruct (fold_production' f ps) eqn:?
    | _ => progress simpl in *
    | _ => progress destruct_head ex
    | _ => progress destruct_head and
    | _ => progress destruct_head prod
    | _ => progress unfold possible_accurate, possible_terminals_prestate, state, prod_prerelated, lattice_for_related, collapse_might_be_empty, might_be_empty_accurate, related, norm_lattice_prod, make_all_possible_result in *
    | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
    | [ |- context[match ?x with _ => _ end] ] => is_var x; destruct x
    | _ => solve [ exfalso; unfold not in *; eauto with nocore ]
    | [ |- context[PositiveSet.In _ all_possible_ascii] ]
      => first [ rewrite forall_chars_get | apply for_first_char_True | apply for_last_char_True ];
         setoid_rewrite (fun v => True_iff (In_all v)); constructor
    | [ |- context[PositiveSet.In _ all_possible_ascii] ]
      => setoid_rewrite (fun v => True_iff (In_all v))
    | [ H : ?P _, H' : forall str, ?P str -> _ |- _ ] => unique pose proof (H' _ H)
    | _ => progress PositiveSetExtensions.push_In
    | _ => progress PositiveSetExtensions.to_caps
    | _ => progress setoid_rewrite_logic
    end.
  Local Ltac correct_t := try pre_correct_t; repeat correct_t_step.

  Local Ltac t_ascii lem :=
    lazymatch goal with
    | [ |- forall_chars__char_in _ ?s ]
      => let s' := head s in
         unfold s';
         eapply forall_chars__impl__forall_chars__char_in
    | [ |- first_char_in _ ?s ]
      => let s' := head s in
         unfold s';
           eapply for_first_char__impl__first_char_in
    | [ |- last_char_in _ ?s ]
      => let s' := head s in
         unfold s';
           eapply for_last_char__impl__last_char_in
    end;
    [ intro | apply lem; assumption ];
    unfold characters_set_to_ascii_list;
    rewrite PositiveSetExtensions.BasicProperties.FM.elements_iff, InA_In_eq, List.in_map_iff;
    eexists; split; [ | eassumption ];
    rewrite ascii_of_pos_of_ascii; reflexivity.

  Lemma all_possible_characters_of_item_nt
        (p : parse_of_item G str (NonTerminal nt))
    : forall_chars str (fun ch => PositiveSet.In (pos_of_ascii ch) (all_possible_characters_of_nt G nt)).
  Proof.
    correct_t.
    eapply forall_chars_Proper; [ reflexivity | intros ?? | try eassumption ].
    correct_t.
  Qed.

  Lemma all_possible_characters_of
        (p : parse_of G str (Lookup G nt))
    : forall_chars str (fun ch => PositiveSet.In (pos_of_ascii ch) (all_possible_characters_of_nt G nt)).
  Proof.
    correct_t.
    eapply forall_chars_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma all_possible_ascii_of_item_nt
        (p : parse_of_item G str (NonTerminal nt))
    : forall_chars__char_in str (all_possible_ascii_of_nt G nt).
  Proof. t_ascii @all_possible_characters_of_item_nt. Qed.

  Lemma all_possible_ascii_of
        (p : parse_of G str (Lookup G nt))
    : forall_chars__char_in str (all_possible_ascii_of_nt G nt).
  Proof. t_ascii @all_possible_characters_of. Qed.

  Lemma might_be_empty_pr_parse_of_item_nt
        (Hlen : length str = 0)
        (p : parse_of_item G str (NonTerminal nt))
    : might_be_empty_of_pr_nt G nt = true.
  Proof. correct_t. Qed.

  Lemma might_be_empty_pr_parse_of
        (Hlen : length str = 0)
        (p : parse_of G str (Lookup G nt))
    : might_be_empty_of_pr_nt G nt = true.
  Proof. correct_t. Qed.

  Lemma possible_first_characters_parse_of_item_nt
        (p : parse_of_item G str (NonTerminal nt))
    : for_first_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_first_characters_of_nt G nt)).
  Proof.
    correct_t.
    eapply for_first_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma possible_first_characters_parse_of
        (p : parse_of G str (Lookup G nt))
    : for_first_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_first_characters_of_nt G nt)).
  Proof.
    correct_t.
    eapply for_first_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma possible_last_characters_parse_of_item_nt
        (p : parse_of_item G str (NonTerminal nt))
    : for_last_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_last_characters_of_nt G nt)).
  Proof.
    correct_t.
    eapply for_last_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma possible_last_characters_parse_of
        (p : parse_of G str (Lookup G nt))
    : for_last_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_last_characters_of_nt G nt)).
  Proof.
    correct_t.
    eapply for_last_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma possible_first_ascii_parse_of_item_nt
        (p : parse_of_item G str (NonTerminal nt))
    : first_char_in str (possible_first_ascii_of_nt G nt).
  Proof. t_ascii possible_first_characters_parse_of_item_nt. Qed.

  Lemma possible_first_ascii_parse_of
        (p : parse_of G str (Lookup G nt))
    : first_char_in str (possible_first_ascii_of_nt G nt).
  Proof. t_ascii possible_first_characters_parse_of. Qed.

  Lemma possible_last_ascii_parse_of_item_nt
        (p : parse_of_item G str (NonTerminal nt))
    : last_char_in str (possible_last_ascii_of_nt G nt).
  Proof. t_ascii possible_last_characters_parse_of_item_nt. Qed.

  Lemma possible_last_ascii_parse_of
        (p : parse_of G str (Lookup G nt))
    : last_char_in str (possible_last_ascii_of_nt G nt).
  Proof. t_ascii possible_last_characters_parse_of. Qed.

  Lemma all_possible_characters_of_parse_of_production
        (p : parse_of_production G str ps)
    : forall_chars str (fun ch => PositiveSet.In (pos_of_ascii ch) (all_possible_characters_of_production G ps)).
  Proof.
    correct_t.
    eapply forall_chars_Proper; [ reflexivity | intros ?? | try eassumption ].
    correct_t.
  Qed.

  Lemma all_possible_ascii_of_parse_of_production
        (p : parse_of_production G str ps)
    : forall_chars__char_in str (all_possible_ascii_of_production G ps).
  Proof. t_ascii all_possible_characters_of_parse_of_production. Qed.

  Lemma might_be_empty_pr_parse_of_production
        (Hlen : length str = 0)
        (p : parse_of_production G str ps)
    : might_be_empty_of_pr_production G ps = true.
  Proof. correct_t. Qed.


  Lemma possible_first_characters_parse_of_production
        (p : parse_of_production G str ps)
    : for_first_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_first_characters_of_production G ps)).
  Proof.
    correct_t.
    eapply for_first_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma possible_last_characters_parse_of_production
        (p : parse_of_production G str ps)
    : for_last_char str (fun ch => PositiveSet.In (pos_of_ascii ch) (possible_last_characters_of_production G ps)).
  Proof.
    correct_t.
    eapply for_last_char_Proper; [ reflexivity | intros ?? | eassumption ].
    correct_t.
  Qed.

  Lemma possible_first_ascii_parse_of_production
        (p : parse_of_production G str ps)
    : first_char_in str (possible_first_ascii_of_production G ps).
  Proof. t_ascii possible_first_characters_parse_of_production. Qed.

  Lemma possible_last_ascii_parse_of_production
        (p : parse_of_production G str ps)
    : last_char_in str (possible_last_ascii_of_production G ps).
  Proof. t_ascii possible_last_characters_parse_of_production. Qed.
End correctness_lemmas.

Ltac make_possible_data G :=
  let v := constr:(@fold_grammar _ _ _ possible_terminals_aidata G) in
  let v := make_fold_grammar_data_from v in
  constr:(v : possible_data G).

Ltac pose_possible_data_for G :=
  lazymatch goal with
  | [ H : possible_data G |- _ ] => idtac
  | _ => let Hpossible_data := fresh "Hpossible_terminals_data" in
         let val := make_possible_data G in
         pose val as Hpossible_data;
         cbv beta in Hpossible_data
  end.
