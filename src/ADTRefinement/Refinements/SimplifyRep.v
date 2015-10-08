Require Import Fiat.Common Fiat.Computation
        Fiat.ADT.ADTSig Fiat.ADT.Core
        Fiat.ADTRefinement.Core Fiat.ADTRefinement.SetoidMorphisms.

Section SimplifyRep.

  (* If a representation has extraneous information (perhaps intermediate
     data introduced during refinement), simplifying the representation
     is a valid refinement. *)

  Variable oldRep : Type. (* The old representation type. *)
  Variable newRep : Type. (* The new representation type. *)

  Variable simplifyf : oldRep -> newRep. (* The simplification function. *)
  Variable concretize : newRep -> oldRep. (* A map to the enriched representation. *)

  (* The abstraction relation between old and new representations. *)
  Variable AbsR : oldRep -> newRep -> Prop.
  Notation "ro ≃ rn" := (AbsR ro rn) (at level 70).

  (*Definition simplifyMethod
             (Dom : list Type)
             (Cod : Type)
             (oldMeth : methodType oldRep Dom Cod)
             r_n n : Comp (newRep * Cod) :=
    (r_o' <- (oldMeth (concretize r_n) n);
     ret (simplifyf (fst r_o'), snd r_o'))%comp.

  Definition simplifyConstructor
             (Dom : Type)
             (oldConstr : constructorType oldRep Dom)
             n : Comp newRep :=
    (or <- oldConstr n;
     ret (simplifyf or))%comp.

  Variable Sig : ADTSig. (* The signature of the ADT being simplified. *)

  Definition simplifyRep oldConstr oldMeths :
    (forall r_o, r_o ≃ simplifyf r_o) ->
    (forall r_n r_o,
       (r_o ≃ r_n) ->
       forall idx n,
         refineEquiv (r_o'' <- oldMeths idx r_o n;
                      r_n' <- {r_n' | fst r_o'' ≃ r_n'};
                      ret (r_n', snd r_o''))
                     (r_o'' <- oldMeths idx (concretize r_n) n;
                      ret (simplifyf (fst r_o''), snd r_o''))) ->
    refineADT
      (@Build_ADT Sig oldRep oldConstr oldMeths)
      (@Build_ADT Sig newRep
                  (fun idx => simplifyConstructor (oldConstr idx))
                  (fun idx => simplifyMethod (oldMeths idx))).
  Proof.
    econstructor 1 with
    (AbsR := AbsR); simpl; eauto.
    - unfold simplifyConstructor, refine; intros;
      computes_to_inv; repeat computes_to_econstructor; try subst; eauto.
    - unfold simplifyMethod; intros.
      eapply H0; eauto.
  Qed. *)

End SimplifyRep.
