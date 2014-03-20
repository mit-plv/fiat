Require Import Common Computation ADT Ensembles.
Require Import ADTRefinement.Core ADTRefinement.SetoidMorphisms.

Section SimplifyRep.

  (* If a representation has extraneous information (perhaps intermediate
     data introduced during refinement), simplifying the representation
     is a valid refinement. *)

  Variable oldRep : Type. (* The old representation type. *)
  Variable newRep : Type. (* The new representation type. *)

  Variable simplifyf : oldRep -> newRep. (* The simplification function. *)
  Variable concretize : newRep -> oldRep. (* A map to the enriched representation. *)

  (* The simulation relation between old and new representations. *)
  Variable SiR : oldRep -> newRep -> Prop.
  Notation "ro ≃ rn" := (SiR ro rn) (at level 70).

  Definition simplifyMutatorMethod
             (Dom : Type)
             (oldMuts : mutatorMethodType oldRep Dom)
             r_n n : Comp newRep :=
    (r_o' <- (oldMuts (concretize r_n) n);
     ret (simplifyf r_o'))%comp.

  Definition simplifyObserverMethod
             (Dom Cod : Type)
             (oldObs : observerMethodType oldRep Dom Cod)
             nr n : Comp Cod :=
    oldObs (concretize nr) n.

  Variable Sig : ADTSig. (* The signature of the ADT being simplified. *)

  Definition simplifyRep
             oldMuts oldObs :
    (forall r_n r_o,
       (r_o ≃ r_n) ->
       forall idx n,
         refineEquiv (r_o'' <- oldMuts idx r_o n;
                      {r_n' | r_o'' ≃ r_n'})
                     (r_o'' <- oldMuts idx (concretize r_n) n;
                      ret (simplifyf r_o''))) ->
    (forall r_n r_o,
       (r_o ≃ r_n) ->
       forall idx n,
         refineEquiv (oldObs idx r_o n)
                     (oldObs idx (concretize r_n) n)) ->
    refineADT
      (@Build_ADT Sig oldRep oldMuts oldObs)
      (@Build_ADT Sig newRep
                  (fun idx => simplifyMutatorMethod (oldMuts idx))
                  (fun idx => simplifyObserverMethod (oldObs idx))).
  Proof.
    econstructor 1 with
    (SiR := SiR); simpl; eauto.
    - unfold simplifyMutatorMethod; intros; eapply H; eauto.
    - unfold simplifyObserverMethod; intros; eapply H0; eauto.
  Qed.

End SimplifyRep.
