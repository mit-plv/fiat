Require Import Common ADT.Core
        ADTRefinement.Core ADTRefinement.SetoidMorphisms.

(* To derive an ADT interactively from a specification [spec], we can
   build a dependent product [ {adt : _ & refineADT spec adt} ]. The
   derivation flow has the form:

   1. Apply a refinement.
   2. Discharge any side conditions.
   3. Repeat steps 1-2 until adt is completely specialized.

   My (Ben's) current thought is that to make this as pleasant as
   possible, the refinements used in the first step should be
   implemented using tactics which present the user with 'nice' side
   conditions. (In particular, this lets us be careful about not
   having any dangling existential variables at the end of a
   derivation).

   Aside on notation:
   When naming these tactics, I wanted one which
   wasn't already used by a tactic- refine, specialize, and replace
   were taken. The thesaurus suggested 'hone'.  This kind of agrees
   with 'BedRock' (in as much as a WhetStone is used to sharpen
   knives), so I'm carrying on the naming convention with a
   'Sharpened' notation for the dependent products. *)

Notation Sharpened spec := {adt : _ & refineADT spec adt}.

(* A single refinement step. *)
Definition SharpenStep Sig adt :
  forall adt',
    refineADT (Sig := Sig) adt adt' ->
    Sharpened adt' ->
    Sharpened adt.
Proof.
  intros adt' refineA SpecA';
  eexists (projT1 SpecA').
  (* rewrite refineA. *)
  eapply transitivityT; [ eassumption | ].
  exact (projT2 SpecA').
Defined.

(* A tactic for finishing a derivation. Probably needs a better name.*)
Tactic Notation "finish" "sharpening" := eexists; solve [ reflexivity | eapply reflexivityT ].

(* Honing tactic for refining the observer method with the specified index.
     This version of the tactic takes the new implementation as an argument. *)

Tactic Notation "hone'" "method" constr(obsIdx) "using" constr(obsBody) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let ASig := match type of A with
                    ADT ?Sig => Sig
                end in
    let mutIdx_eq' := fresh in
    let Rep' := eval simpl in (Rep A) in
    let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
    let MethodIndex' := eval simpl in (MethodIndex ASig) in
    let Methods' := eval simpl in (Methods A) in
      assert (forall idx idx' : MethodIndex', {idx = idx'} + {idx <> idx'})
        as obsIdx_eq' by (decide equality);
      eapply SharpenStep;
      [eapply (@refineADT_Build_ADT_Method
                 Rep' _ _ _
                 (fun idx : MethodIndex ASig => if (obsIdx_eq' idx ()) then
                               obsBody
                             else
                               Methods' idx))
      | idtac]; cbv beta in *; simpl in *.

  (* Honing tactic for refining the constructor method with the specified index.
     This version of the tactic takes the new implementation as an argument. *)
  Tactic Notation "hone'" "constructor" constr(mutIdx) "using" constr(mutBody) :=
    let A :=
        match goal with
            |- Sharpened ?A => constr:(A) end in
    let ASig := match type of A with
                    ADT ?Sig => Sig
                end in
    let mutIdx_eq' := fresh in
    let Rep' := eval simpl in (Rep A) in
    let ConstructorIndex' := eval simpl in (ConstructorIndex ASig) in
    let MethodIndex' := eval simpl in (MethodIndex ASig) in
    let Constructors' := eval simpl in (Constructors A) in
      assert (forall idx idx' : ConstructorIndex', {idx = idx'} + {idx <> idx'})
        as mutIdx_eq' by (decide equality);
      eapply SharpenStep;
        [eapply (@refineADT_Build_ADT_Constructors Rep'
                   _
                   _
                   _
                   (fun idx : ConstructorIndex ASig => if (mutIdx_eq' idx mutIdx) then
                                 mutBody
                               else
                                 Constructors' idx))
        | idtac]; cbv beta in *; simpl in *.
