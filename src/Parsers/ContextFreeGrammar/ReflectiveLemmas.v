(** * Leamms for reflective notations for context free grammars *)
Require Import Coq.Strings.Ascii Coq.Classes.Morphisms Coq.Relations.Relation_Definitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.

Lemma item_rect_ritem_rect {C A T NT} {_ : Reflective.interp_RCharExpr_data C} it
  : item_rect (fun _ : item C => A) T NT (Reflective.interp_ritem it)
    = ritem_rect (fun _ => A) (fun f => T (Reflective.interp_RCharExpr f)) NT it.
Proof.
  destruct it; reflexivity.
Qed.

Global Instance ritem_rect_Proper {C P}
  : Proper (forall_relation (fun _ => eq) ==> forall_relation (fun _ => eq) ==> forall_relation (fun _ => eq))
           (@ritem_rect C P).
Proof.
  lazy.
  intros ?????? [?|?]; congruence.
Qed.

Global Instance ritem_rect_Proper_nd {C P}
  : Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> pointwise_relation _ eq)
           (@ritem_rect C (fun _ => P)).
Proof.
  lazy.
  intros ?????? [?|?]; congruence.
Qed.

Global Instance ritem_rect_Proper_nd' {C P}
  : Proper (pointwise_relation _ eq ==> pointwise_relation _ eq ==> eq ==> eq)
           (@ritem_rect C (fun _ => P)).
Proof.
  lazy.
  intros ?????? [?|?]; intros; subst; congruence.
Qed.

Global Instance ritem_rect_Proper_forall_R {C A} {R : relation A}
  : Proper
      ((pointwise_relation _ R)
         ==> (pointwise_relation _ R)
         ==> forall_relation (fun _ => R))
      (ritem_rect (fun _ : ritem C => A)).
Proof.
  lazy; intros ?????? [?|?]; trivial.
Qed.

Hint Extern 0 (Proper (_ ==> pointwise_relation _ _ ==> forall_relation _) (ritem_rect _))
=> refine ritem_rect_Proper_forall_R : typeclass_instances.
