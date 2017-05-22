(** * Leamms for reflective notations for context free grammars *)
Require Import Coq.Strings.Ascii Coq.Classes.Morphisms Coq.Relations.Relation_Definitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Import Fiat.Parsers.ContextFreeGrammar.ReflectiveOpt.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Tactics.BreakMatch.

Lemma ritem_rect_interp {C A T NT} {_ : opt.interp_ritem_data} it
  : ritem_rect (fun _ : ritem C => A) T NT (opt.interp_ritem it)
    = opt.ritem_rect (fun _ => A) (fun f => T f) (fun nt => NT (opt.interp_nonterminal nt)) it.
Proof.
  destruct it; reflexivity.
Qed.

Module opt.
  Section compile_interp.
    Context {Char : Type}
            {iidata : opt.interp_ritem_data}.

    Lemma compile_interp_nonterminal nt
          (HNoDup : uniquize string_beq opt.irnonterminal_names = opt.irnonterminal_names)
          (Hfresh : ~List.In opt.irinvalid_nonterminal opt.irnonterminal_names)
          (Hnt : nt <= List.length opt.irnonterminal_names)
      : opt.compile_nonterminal (opt.interp_nonterminal nt) = nt.
    Proof.
      unfold opt.compile_nonterminal, opt.interp_nonterminal.
      destruct iidata; simpl in *.
      rewrite List.nth_default_eq.
      revert dependent irnonterminal_names.
      induction nt as [|nt IHnt], irnonterminal_names;
        try solve [ reflexivity
                  | simpl; tauto
                  | simpl; intros; omega ].
      { simpl @List.nth; simpl @List.length.
        rewrite first_index_default_S_cons.
        rewrite string_lb by reflexivity; reflexivity. }
      { simpl @List.length; simpl @uniquize; simpl @List.nth; simpl @List.In.
        break_innermost_match.
        { intro Hbad; exfalso.
          pose proof (f_equal (@List.length _) Hbad) as Hbad'.
          pose proof (uniquize_shorter irnonterminal_names string_beq).
          simpl List.length in *.
          omega. }
        intros HNoDup Hfresh Hnt.
        apply Decidable.not_or in Hfresh.
        inversion HNoDup as [HNoDup']; clear HNoDup.
        rewrite first_index_default_S_cons, IHnt
          by first [ congruence
                   | rewrite HNoDup'; (tauto || omega) ].
        break_innermost_match; [ | reflexivity ].
        exfalso.
        repeat match goal with
               | [ H : list_bin _ _ _ = false |- _ ]
                 => rewrite list_in_lb in H; [ congruence | apply @string_lb | clear H ]
               | [ H : string_beq _ ?s = true |- _ ] => apply string_bl in H; try subst s
               | [ |- List.In (List.nth ?n ?l ?d) ?l ]
                 => destruct (@List.nth_in_or_default _ n l d); [ assumption | exfalso ]
               | _ => tauto
               end. }
    Qed.
  End compile_interp.

  Global Instance ritem_rect_Proper {C P}
  : Proper (forall_relation (fun _ => eq) ==> forall_relation (fun _ => eq) ==> forall_relation (fun _ => eq))
           (@opt.ritem_rect C P).
  Proof.
    lazy.
    intros ?????? [?|?]; congruence.
  Qed.

  Global Instance ritem_rect_Proper_nd {C P}
    : Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> pointwise_relation _ eq)
             (@opt.ritem_rect C (fun _ => P)).
  Proof.
    lazy.
    intros ?????? [?|?]; congruence.
  Qed.

  Global Instance ritem_rect_Proper_nd' {C P}
    : Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> eq ==> eq)
             (@opt.ritem_rect C (fun _ => P)).
  Proof.
    lazy.
    intros ?????? [?|?]; intros; subst; congruence.
  Qed.

  Global Instance ritem_rect_Proper_forall_R {C A} {R : relation A}
    : Proper
        ((pointwise_relation _ R)
           ==> (pointwise_relation _ R)
           ==> forall_relation (fun _ => R))
        (opt.ritem_rect (fun _ : opt.ritem C => A)).
  Proof.
    lazy; intros ?????? [?|?]; trivial.
  Qed.

  Hint Extern 0 (Proper (_ ==> pointwise_relation _ _ ==> forall_relation _) (opt.ritem_rect _))
  => refine opt.ritem_rect_Proper_forall_R : typeclass_instances.
End opt.
