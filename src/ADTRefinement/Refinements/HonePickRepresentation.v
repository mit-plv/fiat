Require Import Common Computation ADT Ensembles.
Require Import ADTRefinement.Core ADTRefinement.SetoidMorphisms ADTRefinement.GeneralRefinements.

(* A generic refinement and honing tactic for switching the
    representation of an ADT built from [pickImpl]. *)

Section HonePickRepresentation.
(* Given an abstraction function, we can transform the rep of a pickImpl ADT. *)

  Variable oldRep : Type. (* The old representation type. *)
  Variable newRep : Type. (* The new representation type. *)

  (* The abstraction function from the old to new representations. *)
  Variable abs : newRep -> oldRep.

  Theorem refines_rep_pickImpl Sig
          ObserverSpec MutatorSpec :
    refineADT
      (@pickImpl Sig oldRep MutatorSpec ObserverSpec)
      (@pickImpl Sig newRep
                 (fun idx nm n nm' => MutatorSpec idx (abs nm) n (abs nm'))
                 (fun idx nm => ObserverSpec idx (abs nm))).
  Proof.
    unfold pickImpl.
    let B' := match goal with |- refineADT ?A ?B => constr:(B) end in
    econstructor 1 with
    (B := B')
      (SiR := fun om nm => om = (abs nm));
    compute; intros; subst.
    apply computes_to_inv in H0; repeat econstructor; eauto.
    apply computes_to_inv in H0; repeat econstructor; eauto.
  Qed.

End HonePickRepresentation.
