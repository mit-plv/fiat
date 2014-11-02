(** * Some examples about dealing with finite sets *)
Require Import ADTSynthesis.FiniteSetADTs.

(** Now we spec out two examples, the count of the unique elements in
    a list, and the sum of the unique elements in a list. *)

Definition countUniqueSpec (ls : list W) : Comp nat
  := cardinal ls.

Definition countUniqueSpec' (ls : list W) : Comp nat
  := (xs <- to_list (elements ls);
      ret (List.length xs)).

Definition uniqueizeSpec (ls : list W) : Comp (list W)
  := to_list (elements ls).

Definition sumUniqueSpec (ls : list W) : Comp W
  := Ensemble_fold_right wplus wzero (elements ls).

Definition sumAllSpec (ls : list W) : Comp W
  := ret (List.fold_right wplus wzero ls).

Definition unionUniqueSpec1 (ls1 ls2 : list W) : Comp (list W)
  := to_list (elements (ls1 ++ ls2)).
Definition unionUniqueSpec2 (ls1 ls2 : list W) : Comp (list W)
  := to_list (Ensembles.Union _ (elements ls1) (elements ls2)).

Definition filterLtSpec (ls : list W) (x : W) : Comp (list W)
  := ret (List.filter (fun y => wlt y x) ls).

Definition filterLtUniqueSpec1 (ls : list W) (x : W) : Comp (list W)
  := to_list (Ensembles.Setminus _ (elements ls) (fun y => wlt y x = true)).

Definition filterLtUniqueSpec2 (ls : list W) (x : W) : Comp (list W)
  := to_list (Ensembles.Intersection _ (elements ls) (Ensembles.Complement _ (fun y => wlt y x = true))).

Definition intersectionUniqueSpec (ls1 ls2 : list W) : Comp (list W)
  := to_list (Ensembles.Intersection _ (elements ls1) (elements ls2)).

Definition differenceUniqueSpec (ls1 ls2 : list W) : Comp (list W)
  := to_list (Ensembles.Setminus _ (elements ls1) (elements ls2)).

Definition symmetricDifferenceUniqueSpec (ls1 ls2 : list W) : Comp (list W)
  := to_list (Ensembles.Union
                _
                (Ensembles.Setminus _ (elements ls1) (elements ls2))
                (Ensembles.Setminus _ (elements ls2) (elements ls1))).

Definition countUniqueLessThanSpec1 (ls : list W) (x : W) : Comp nat
  := (ls' <- to_list (Ensembles.Setminus _ (elements ls) (fun y => wlt y x = true));
      cardinal ls').

Definition countUniqueLessThanSpec2 (ls : list W) (x : W) : Comp nat
  := (n <- cardinal ls;
      n' <- cardinal (List.filter (fun y => negb (wlt y x)) ls);
      ret (n - n')).

(** Now we refine the implementations. *)
Definition countUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (countUniqueSpec ls).
Proof.
  (** We turn the list into a finite set, and then call 'size' *)
  begin sharpening computation.

  (** QUESTION: should we add an extra layer of non-determinism at the
                end, so that we can do things up to, e.g., [Same_set],
                and so that [Add] is associative and we can swap
                [fold_left] and [fold_right] without a [rev]? *)

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition countUniqueImpl' (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (countUniqueSpec' ls).
Proof.
  (** We turn the list into a finite set, then back into a list, and then call [Datatypes.length]. *)
  (** TODO: Do we care about optimizing this further at this stage? *)
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition uniqueizeImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (uniqueizeSpec ls).
Proof.
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

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition sumAllImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (sumAllSpec ls).
Proof.
  (** We see that the sharpening does the right thing when there's
      nothing to do. *)
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition unionUniqueImpl1 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls1 ls2 : list W)
: FullySharpenedComputation (unionUniqueSpec1 ls1 ls2).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition unionUniqueImpl2 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls1 ls2 : list W)
: FullySharpenedComputation (unionUniqueSpec2 ls1 ls2).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition filterLtImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W) (x : W)
: FullySharpenedComputation (filterLtSpec ls x).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition filterLtUniqueImpl1 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W) (x : W)
: FullySharpenedComputation (filterLtUniqueSpec1 ls x).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition filterLtUniqueImpl2 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W) (x : W)
: FullySharpenedComputation (filterLtUniqueSpec2 ls x).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Require Import Ensembles.
Require Import Coq.Strings.String Coq.Sets.Ensembles Coq.Sets.Finite_sets Coq.Lists.List Coq.Sorting.Permutation.
Require Import ADT ADT.ComputationalADT ADTRefinement.Core ADTNotation ADTRefinement.GeneralRefinements Common.AdditionalEnsembleDefinitions Common.AdditionalEnsembleLemmas Computation.
Require Export FiniteSetADTs.FiniteSetADT.
Require Import Common.

Definition intersectionUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls1 ls2 : list W)
: FullySharpenedComputation (intersectionUniqueSpec ls1 ls2).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  exfalso; admit;finish sharpening computation.
  Grab Existential Variables.
  admit.
Defined.


Definition differenceUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls1 ls2 : list W)
: FullySharpenedComputation (differenceUniqueSpec ls1 ls2).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition symmetricDifferenceUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls1 ls2 : list W)
: FullySharpenedComputation (symmetricDifferenceUniqueSpec ls1 ls2).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition countUniqueLessThanImpl1 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W) (x : W)
: FullySharpenedComputation (countUniqueLessThanSpec1 ls x).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition countUniqueLessThanImpl2 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W) (x : W)
: FullySharpenedComputation (countUniqueLessThanSpec2 ls x).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.
