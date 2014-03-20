Require Import Common Computation ADT Ensembles BuildADT ADTNotation.
Require Import ADTRefinement.Core ADTRefinement.SetoidMorphisms ADTRefinement.Refinements.SimplifyRep.

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

  Definition simplifyMutDef
             (Sig : mutSig)
             (oldMut : @mutDef oldRep Sig)
  : @mutDef newRep Sig :=
    {| mutBody := simplifyMutatorMethod simplifyf concretize (mutBody oldMut) |}.

  Definition simplifyObsDef
             (Sig : obsSig)
             (oldMut : @obsDef oldRep Sig)
  : @obsDef newRep Sig :=
    {| obsBody := simplifyObserverMethod concretize (obsBody oldMut) |}.

  Lemma refineADT_BuildADT_Rep_default
            (mutSigs : list mutSig)
            (obsSigs : list obsSig)
            (mutDefs : ilist (@mutDef oldRep) mutSigs)
            (obsDefs : ilist (@obsDef oldRep) obsSigs) :
    (forall r_n r_o,
       (r_o ≃ r_n) ->
       forall idx n,
         refineEquiv (r_o'' <- getMutDef mutDefs idx r_o n;
                      {r_n' | r_o'' ≃ r_n'})
                     (r_o'' <- getMutDef mutDefs idx (concretize r_n) n;
                      ret (simplifyf r_o''))) ->
    (forall r_n r_o,
       (r_o ≃ r_n) ->
       forall idx n,
         refineEquiv (getObsDef obsDefs idx r_o n)
                     (getObsDef obsDefs idx (concretize r_n) n)) ->
    refineADT
      (BuildADT mutDefs obsDefs)
      (BuildADT (imap _ simplifyMutDef mutDefs)
                (imap _ simplifyObsDef obsDefs)).
  Proof.
    econstructor 1 with (SiR := SiR); simpl in *; eauto; intros.
    - destruct (In_mutIdx _ idx) as [dom In_mutIdx].
      rewrite In_ith with (a := {| mutID := idx;
                                   mutDom := dom |})
                            (default_B :=
                               simplifyMutDef (def mut "null" (r : rep, _ : ()) : rep :=
                                                 ret r )%mutDef); eauto.
      rewrite <- ith_imap; simpl; eauto.
      rewrite H; eauto; reflexivity.
      unfold mutSig_eq; find_if_inside; simpl in *; congruence.
    - destruct (In_obsIdx _ idx) as [dom [cod In_obsIdx] ].
      rewrite In_ith with (a := {|obsID := idx;
                                obsDom := dom;
                                obsCod := cod |})
                          (default_B :=
                             simplifyObsDef (def obs "null" (r : rep, _ : () ) : () :=
                                              ret () )%obsDef); eauto.
    rewrite <- ith_imap; simpl; intros; eauto.
    rewrite H0; eauto; reflexivity.
    unfold obsSig_eq; find_if_inside; eauto.
  Qed.

End SimplifyRep.
