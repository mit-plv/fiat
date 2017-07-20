Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Precompute.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Definitions.
Require Import Fiat.Common.List.ListMorphisms.

Set Implicit Arguments.
Local Coercion is_true : bool >-> Sortclass.
Local Open Scope list_scope.
Local Open Scope grammar_fixedpoint_scope.

Section general_fold.
  Context {Char : Type}
          {T : Type}.

  Definition lattice_for_combine_production combine_production
    : lattice_for T -> lattice_for T -> lattice_for T
    := fun x y => match x, y with
                  | ⊥, _
                  | _, ⊥
                    => ⊥
                  | ⊤, _
                  | _, ⊤
                    => ⊤
                  | constant x', constant y'
                    => combine_production x' y'
                  end.

  Global Instance lattice_for_combine_production_Proper_gen
         {prestate_beq : T -> T -> bool}
    : Proper ((prestate_beq ==> prestate_beq ==> lattice_for_beq prestate_beq) ==> lattice_for_beq prestate_beq ==> lattice_for_beq prestate_beq ==> lattice_for_beq prestate_beq) lattice_for_combine_production.
  Proof.
    intros ?? Hfg [|?|] [|?|] H0 [|?|] [|?|] H1; simpl in *;
      try congruence.
    apply Hfg; assumption.
  Defined.

  Global Instance lattice_for_combine_production_Proper
         {prestate_beq : T -> T -> bool}
         {precombine_production}
         {H : Proper (prestate_beq ==> prestate_beq ==> lattice_for_beq prestate_beq) precombine_production}
    : Proper (lattice_for_beq prestate_beq ==> lattice_for_beq prestate_beq ==> lattice_for_beq prestate_beq) (lattice_for_combine_production precombine_production).
  Proof.
    apply lattice_for_combine_production_Proper_gen, H.
  Defined.

  Context {fpdata : @grammar_fixedpoint_lattice_data T}.

  Class AbstractInterpretation :=
    { on_terminal : (Char -> bool) -> lattice_for T;
      on_nil_production : lattice_for T;
      precombine_production : T -> T -> lattice_for T;
      combine_production : lattice_for T -> lattice_for T -> lattice_for T
      := lattice_for_combine_production precombine_production;
      precombine_production_Proper : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production;
      combine_production_Proper : Proper (state_beq ==> state_beq ==> state_beq) combine_production
      := lattice_for_combine_production_Proper }.

  Global Existing Instance precombine_production_Proper.
  Global Existing Instance combine_production_Proper.

  Context {aidata : AbstractInterpretation}.

  Context (G : pregrammar' Char).

  Global Instance compile_item_data_of_abstract_interpretation : opt.compile_item_data Char state
    := {| opt.on_terminal := on_terminal;
          opt.nonterminal_names := pregrammar_nonterminals G;
          opt.invalid_nonterminal := Gensym.gensym (pregrammar_nonterminals G) |}.

  Section with_compiled_productions.
    Context (compiled_productions : list (opt.productions state)).

    Definition opt_Lookup_idx (n : nat) : opt.productions state
      := List.nth n compiled_productions nil.
    Lemma eq_opt_Lookup_idx
          (Hcompiled_productions : List.map opt.compile_productions (List.map snd (pregrammar_productions G)) = compiled_productions)
          n
      : opt_Lookup_idx n = opt.compile_productions (Lookup_idx G n).
    Proof.
      unfold opt_Lookup_idx, Lookup_idx; subst compiled_productions.
      change nil with (opt.compile_productions nil) at 1.
      rewrite List.map_nth.
      reflexivity.
    Qed.

    Definition fold_item'
               (fold_nt : default_nonterminal_carrierT -> state)
               (it : opt.item state)
      : state
      := match it with
         | opt.Terminal tv => tv
         | opt.NonTerminal nt nt_idx => fold_nt nt_idx
         end.

    Global Instance fold_item'_ProperR {R}
           {R_Reflexive : Reflexive R}
      : Proper (pointwise_relation _ R ==> eq ==> R) fold_item' | 20.
    Proof.
      intros ?? H [?|?] ??; subst; simpl; [ reflexivity | apply H ].
    Qed.

    Global Instance fold_item'_Proper
      : Proper (pointwise_relation _ eq ==> eq ==> eq) fold_item' | 20
      := _.

    Definition fold_production'
               (fold_nt : default_nonterminal_carrierT -> state)
               (its : opt.production state)
      := List.fold_right
           combine_production
           on_nil_production
           (List.map
              (fold_item' fold_nt)
              its).

    Global Instance fold_production'_ProperR {R}
           {R_Reflexive : Reflexive R}
           {combine_production_ProperR : Proper (R ==> R ==> R) combine_production}
      : Proper (pointwise_relation _ R ==> eq ==> R) fold_production' | 20.
    Proof.
      unfold fold_production'.
      repeat intro.
      apply (_ : Proper (_ ==> _ ==> SetoidList.eqlistA R ==> _) (@List.fold_right _ _));
        trivial.
      subst; apply map_eqlistA_Proper; try reflexivity.
      repeat intro; apply fold_item'_ProperR; trivial.
    Qed.

    Global Instance fold_production'_Proper
      : Proper (pointwise_relation _ eq ==> eq ==> eq) fold_production' | 2
      := _.

    Global Instance: Params (@fold_production') 5.

    Definition fold_productions'
               (fold_nt : default_nonterminal_carrierT -> state)
               (its : opt.productions state)
      := List.fold_right
           least_upper_bound
           ⊥
           (List.map
              (fold_production' fold_nt)
              its).

    Global Instance fold_productions'_ProperR {R}
           {R_Reflexive : Reflexive R}
           {least_upper_bound_ProperR : Proper (R ==> R ==> R) least_upper_bound}
           {combine_production_ProperR : Proper (R ==> R ==> R) combine_production}
      : Proper (pointwise_relation _ R ==> eq ==> R) fold_productions' | 20.
    Proof.
      unfold fold_production'.
      repeat intro.
      apply (_ : Proper (_ ==> _ ==> SetoidList.eqlistA R ==> _) (@List.fold_right _ _));
        trivial.
      subst; apply map_eqlistA_Proper; try reflexivity.
      repeat intro; apply fold_production'_ProperR; trivial.
    Qed.

    Global Instance fold_productions'_Proper_eq
      : Proper (pointwise_relation _ eq ==> eq ==> eq) fold_productions' | 20
      := _.

    Definition fold_constraints
               (fold_nt : default_nonterminal_carrierT -> state)
               (nt : default_nonterminal_carrierT)
      : state
      := fold_productions'
           fold_nt
           (opt_Lookup_idx nt).

    Section extR.
      Context (R : state -> state -> Prop)
              (combine_production_Proper : Proper (R ==> R ==> R) combine_production)
              (lub_Proper : Proper (R ==> R ==> R) least_upper_bound)
              (R_Reflexive : Reflexive R).

      Lemma fold_item'_extR {f g} (ext : forall b, R (f b) (g b)) b
        : R (fold_item' f b) (fold_item' g b).
      Proof.
        unfold fold_item'.
        generalize (@of_nonterminal _ (@rdp_list_predata _ G)); simpl; intro.
        generalize on_terminal; intro.
        unfold state in *.
        simpl in *.
        clear -ext R_Reflexive.
        abstract (destruct b; try apply ext; reflexivity).
      Defined.

      Lemma fold_production'_extR {f g} (ext : forall b, R (f b) (g b)) b
        : R (fold_production' f b) (fold_production' g b).
      Proof.
        unfold fold_production'.
        induction b as [ | x ]; try reflexivity; simpl.
        apply combine_production_Proper; [ apply (fold_item'_extR ext) | apply IHb ].
      Defined.

      Lemma fold_productions'_extR {f g} (ext : forall b, R (f b) (g b)) b
        : R (fold_productions' f b) (fold_productions' g b).
      Proof.
        unfold fold_productions'.
        induction b as [ | x ]; try reflexivity; simpl.
        apply lub_Proper; [ apply (fold_production'_extR ext) | apply IHb ].
      Defined.

      Lemma fold_constraints_extR f g (H : forall x, R (f x) (g x)) nt
        : R (fold_constraints f nt) (fold_constraints g nt).
      Proof.
        unfold fold_constraints.
        apply fold_productions'_extR.
        intro; apply H.
      Defined.
    End extR.

    Definition fold_item'_ext {f g} (ext : forall b, f b = g b) b
      : fold_item' f b = fold_item' g b
      := fold_item'_extR (R := eq) _ ext b.
    Definition fold_production'_ext {f g} (ext : forall b, f b = g b) b
      : fold_production' f b = fold_production' g b
      := fold_production'_extR (R := eq) _ _ ext b.
    Definition fold_productions'_ext {f g} (ext : forall b, f b = g b) b
      : fold_productions' f b = fold_productions' g b
      := fold_productions'_extR (R := eq) _ _ _ ext b.
    Definition fold_constraints_ext f g (H : forall x, f x = g x) nt
      : fold_constraints f nt = fold_constraints g nt
      := fold_constraints_extR (R := eq) _ _ _ _ _ H nt.

    Definition fold_item'_ext_beq {f g} (ext : forall b, f b =b g b) b
      : fold_item' f b =b fold_item' g b
      := fold_item'_extR (R := state_beq) _ ext b.
    Definition fold_production'_ext_beq
               {f g} (ext : forall b, f b =b g b) b
      : fold_production' f b =b fold_production' g b
      := fold_production'_extR (R := state_beq) _ _ ext b.
    Definition fold_productions'_ext_beq
               {f g} (ext : forall b, f b =b g b) b
      : fold_productions' f b =b fold_productions' g b
      := fold_productions'_extR (R := state_beq) _ _ _ ext b.
    Definition fold_constraints_ext_beq
               f g (H : forall x, f x =b g x) nt
      : fold_constraints f nt =b fold_constraints g nt
      := fold_constraints_extR (R := state_beq) _ _ _ _ _ H nt.

    Global Instance fold_constraints_ProperR
           {R : state -> state -> Prop}
           {combine_production_Proper : Proper (R ==> R ==> R) combine_production}
           {lub_Proper : Proper (R ==> R ==> R) least_upper_bound}
           {R_Reflexive : Reflexive R}
      : Proper (pointwise_relation default_nonterminal_carrierT R ==> eq ==> R)
               fold_constraints
    | 10.
    Proof.
      intros f g H; repeat intro; subst.
      apply fold_constraints_extR; assumption.
    Defined.

    Global Instance fold_constraints_Proper
      : Proper (pointwise_relation default_nonterminal_carrierT eq ==> eq ==> eq)
               fold_constraints
      := _.

    Global Instance fold_constraints_Proper_state_beq
      : Proper (pointwise_relation default_nonterminal_carrierT state_beq ==> eq ==> state_beq)
               fold_constraints
      := _.

    Definition fixedpoint_by_abstract_interpretation : grammar_fixedpoint_data.
    Proof.
      refine {| prestate := T;
                step_constraints folder nt st := fold_constraints folder nt;
                lattice_data := fpdata |}.
      { repeat intro; apply fold_constraints_Proper_state_beq; assumption. }
    Defined.
  End with_compiled_productions.
End general_fold.

Section on_ensembles.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char}.
  Context (G : pregrammar Char).

  Definition ensemble_on_terminal (P : Char -> bool) : Ensemble String
    := (fun str => exists ch, is_true (P ch) /\ str ~= [ ch ])%string_like.

  Definition ensemble_on_nil_production : Ensemble String
    := (fun str => length str = 0).

  Definition ensemble_combine_production : Ensemble String -> Ensemble String -> Ensemble String
    := fun P1 P2 => fun str => exists n, P1 (take n str) /\ P2 (drop n str).

  Definition ensemble_bottom : Ensemble String
    := Empty_set _.

  Definition ensemble_top : Ensemble String
    := Full_set _.

  Definition ensemble_least_upper_bound : Ensemble String -> Ensemble String -> Ensemble String
    := fun P1 P2 => fun str => P1 str \/ P2 str.

  Definition ensemble_le : Ensemble String -> Ensemble String -> Prop
    := fun s0 s1 => forall v, s0 v -> s1 v.

  Definition ensemble_fold_production'
             (fold_nt : default_nonterminal_carrierT -> Ensemble String)
             (its : production Char)
    := List.fold_right
         ensemble_combine_production
         ensemble_on_nil_production
         (List.map
            (fun it =>
               match it with
               | Terminal ch => ensemble_on_terminal ch
               | NonTerminal nt => fold_nt (@of_nonterminal _ (@rdp_list_predata _ G) nt)
               end)
            its).

  Lemma ensemble_fold_production'_ext {f g} (ext : forall b, f b = g b) b
  : ensemble_fold_production' f b = ensemble_fold_production' g b.
  Proof.
    unfold ensemble_fold_production'.
    induction b as [ | x ]; try reflexivity; simpl in *; [].
    rewrite IHb; destruct x; rewrite ?ext; reflexivity.
  Qed.

  Definition ensemble_fold_productions'
             (fold_nt : default_nonterminal_carrierT -> Ensemble String)
             (its : productions Char)
    := List.fold_right
         ensemble_least_upper_bound
         ensemble_bottom
         (List.map
            (ensemble_fold_production' fold_nt)
            its).

  Lemma ensemble_fold_productions'_ext {f g} (ext : forall b, f b = g b) b
  : ensemble_fold_productions' f b = ensemble_fold_productions' g b.
  Proof.
    unfold ensemble_fold_productions'.
    induction b as [ | x ]; try reflexivity; simpl.
    rewrite IHb, (ensemble_fold_production'_ext ext); reflexivity.
  Qed.

  Definition ensemble_fold_constraints
             (fold_nt : default_nonterminal_carrierT -> Ensemble String)
             (nt : default_nonterminal_carrierT)
    : Ensemble String
    := ensemble_fold_productions'
         fold_nt
         (Lookup_idx G nt).

  Lemma ensemble_fold_constraints_ext f g (H : forall x, f x = g x) nt
    : ensemble_fold_constraints f nt = ensemble_fold_constraints g nt.
  Proof.
    unfold ensemble_fold_constraints.
    apply ensemble_fold_productions'_ext.
    intro; apply H.
  Qed.
End on_ensembles.

Section fold_correctness.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {T : Type}.
  Context {fpdata : @grammar_fixedpoint_lattice_data T}
          {aidata : @AbstractInterpretation Char T fpdata}.
  Context (G : pregrammar Char)
          (prerelated : Ensemble String -> T -> Prop).

  Definition lattice_for_related (P : Ensemble String) (st : lattice_for T) : Prop
    := match st with
       | ⊤ => True
       | ⊥ => forall str, ~P str
       | constant n => prerelated P n
       end.

  Lemma top_related : lattice_for_related ensemble_top ⊤.
  Proof. constructor. Qed.

  Lemma bottom_related : lattice_for_related ensemble_bottom ⊥.
  Proof. intros ? H; destruct H. Qed.

  Section related.
    Local Notation related := lattice_for_related.

    Global Instance lattice_for_related_ext {_ : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated}
      : Proper ((beq ==> iff) ==> state_beq ==> iff) related | 2.
    Proof.
      intros ?? H' [|?|] [|?|] ?; simpl in *;
        try tauto;
        try congruence;
        try (apply H; assumption);
        try setoid_rewrite H';
        try setoid_rewrite (fun x => H' x x (reflexivity _));
        try reflexivity.
    Qed.

    Global Instance lattice_for_related_eq_Proper
      : Proper (eq ==> eq ==> eq) related | 0 := _.

    Global Instance lattice_for_combine_production_Proper_le
           {precombine_production'}
           {H : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production'}
      : Proper (state_le ==> state_le ==> state_le) (lattice_for_combine_production precombine_production').
    Proof.
      clear aidata.
      intros [|?|] [|?|] ? [|?|] [|?|] ?; simpl in *;
        try solve [ trivial
                  | congruence
                  | edestruct precombine_production'; reflexivity ].
      apply H; assumption.
    Qed.
  End related.

  Class AbstractInterpretationCorrectness :=
    { prerelated_ext : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated;
      related : Ensemble String -> state -> Prop
      := lattice_for_related;
      related_ext : Proper ((beq ==> iff) ==> state_beq ==> iff) related
      := lattice_for_related_ext;
      related_monotonic : forall s0 s1, s0 <= s1 -> (forall v, related v s0 -> related v s1);
      lub_correct
      : forall P1 st1,
          related P1 st1
          -> forall P2 st2,
            related P2 st2
            -> related (ensemble_least_upper_bound P1 P2) (least_upper_bound st1 st2);
      on_terminal_correct
      : forall P,
          related (ensemble_on_terminal P) (on_terminal P);
      on_nil_production_correct
      : related ensemble_on_nil_production on_nil_production;
      precombine_production_Proper_le
      : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production;
      combine_production_Proper_le
      : Proper (state_le ==> state_le ==> state_le) combine_production
      := _;
      combine_production_correct
      : forall P1 st1,
          related P1 st1
          -> forall P2 st2,
            related P2 st2
            -> related (ensemble_combine_production P1 P2) (combine_production st1 st2)
    }.

  Context {aicdata : AbstractInterpretationCorrectness}.
  Local Hint Immediate (compile_item_data_of_abstract_interpretation G) : typeclass_instances.
  Context (compiled_productions : list (opt.productions state))
          (Hcompiled_productions : List.map opt.compile_productions (List.map snd (pregrammar_productions G)) = compiled_productions).

  Lemma fold_production_related
        (mapping : default_nonterminal_carrierT -> Ensemble String)
        st
        (Hmapping : forall nt, related (mapping nt) (st nt))
    : forall pat, related (ensemble_fold_production' G mapping pat) (fold_production' st (opt.compile_production pat)).
  Proof.
    unfold ensemble_fold_production', fold_production' in *.
    induction pat as [|[|] xs IHxs];
      simpl;
      eauto using on_nil_production_correct, combine_production_correct, on_terminal_correct.
  Qed.

  Lemma fold_productions_related
        (mapping : default_nonterminal_carrierT -> Ensemble String)
        st
        (Hmapping : forall nt, related (mapping nt) (st nt))
    : forall pats, related (ensemble_fold_productions' G mapping pats) (fold_productions' st (opt.compile_productions pats)).
  Proof.
    unfold ensemble_fold_productions', fold_productions' in *.
    induction pats as [|[|] xs IHxs];
      simpl;
      repeat match goal with
             | _ => solve [ eauto using top_related, bottom_related, lub_correct, fold_production_related ]
             | [ |- related (ensemble_least_upper_bound _ _) _ ]
               => apply lub_correct
             | [ |- related (ensemble_fold_production' _ _ _) _ ]
               => apply fold_production_related
             end.
  Qed.

  Lemma fold_constraints_related
        (mapping : default_nonterminal_carrierT -> Ensemble String)
        st
        (Hmapping : forall nt, related (mapping nt) (st nt))
    : forall nt, related (ensemble_fold_constraints G mapping nt) (fold_constraints compiled_productions st nt).
  Proof.
    intro nt.
    unfold ensemble_fold_constraints, fold_constraints.
    erewrite eq_opt_Lookup_idx by eassumption.
    apply fold_productions_related; assumption.
  Qed.
End fold_correctness.
