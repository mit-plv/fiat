(** * Some examples about dealing with finite sets *)
Require Import ADTSynthesis.FiniteSetADTs.
(*Require Import Coq.Strings.String Coq.Sets.Ensembles Coq.Sets.Finite_sets Coq.Lists.List Permutation.
Require Import ADT ADT.ComputationalADT ADTRefinement.Core ADTNotation ADTRefinement.GeneralRefinements QueryStructure.IndexedEnsembles.*)

(** Now we spec out two examples, the count of the unique elements in
    a list, and the sum of the unique elements in a list. *)
Require Export Computation.Core Computation.Notations ADTRefinement.GeneralRefinements ADTNotation.
Arguments FiniteSetOfList {_} _.
Global Open Scope comp_scope.
Definition countUniqueSpec (ls : list W) : Comp nat
  := cardinal ls.

Definition countUniqueSpec' (ls : list W) : Comp nat
  := (xs <- to_list (elements ls);
      ret (List.length xs)).

Definition sumUniqueSpec (ls : list W) : Comp W
  := Ensemble_fold_right wplus wzero (elements ls).

(** Now we refine the implementations. *)
Definition countUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (countUniqueSpec ls).
Proof.
  (** We turn the list into a finite set, and then call 'size' *)
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

(** And now we do the same for summing. *)

Definition sumUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (sumUniqueSpec ls).
Proof.
  (** We fold over the list, using a finite set to keep track of what
      we've seen, and every time we see something new, we update our
      running sum.  This should be compiled down to a for loop with an
      in-place update. *)
  begin sharpening computation.

  setoid_rewrite (@finite_set_handle_cardinal FiniteSetImpl).
  first [ setoid_rewrite (@finite_set_handle_cardinal FiniteSetImpl)
        | rewrite (@finite_set_handle_EnsembleListEquivalence FiniteSetImpl)
        | rewrite (@CallSize_FiniteSetOfListOfFiniteSetAndListOfList FiniteSetImpl)
        | rewrite (@fold_right_snd_FiniteSetAndListOfList FiniteSetImpl)
        | rewrite Ensemble_fold_right_simpl
        | rewrite Ensemble_fold_right_simpl'
        | progress autounfold with finite_sets
        | progress autorewrite with refine_monad ].


  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.
