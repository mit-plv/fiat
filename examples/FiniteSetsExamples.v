(** * Some examples about dealing with finite sets *)
Require Import Coq.Strings.String Coq.Sets.Ensembles Coq.Sets.Finite_sets Coq.Lists.List.
Require Import ADT ADT.ComputationalADT ADTRefinement.Core ADTNotation ADTRefinement.GeneralRefinements.

Set Implicit Arguments.

Local Open Scope string_scope.

(** TODO: Figure out where Facade words live, and use that *)
Definition word := nat.

(** We define the interface for finite sets *)
(** QUESTION: Does Facade give us any other methods?  Do we want to
    provide any other methods? *)
Definition FiniteSetSig : ADTSig :=
  ADTsignature {
      Constructor "Empty" : unit -> rep,
      Method "Add" : rep x word -> rep x unit,
      Method "Remove" : rep x word -> rep x unit,
      Method "In" : rep x word -> rep x bool,
      Method "Size" : rep x unit -> rep x nat
    }.

(** And now the spec *)
Definition FiniteSetSpec : ADT FiniteSetSig :=
  ADTRep (Ensemble word) {
    Def Constructor "Empty" (_ : unit) : rep := ret (Empty_set _),

    Def Method "Add" (xs : rep , x : word) : unit :=
      ret (Add _ xs x, tt),

    Def Method "Remove" (xs : rep , x : word) : unit :=
      ret (Subtract _ xs x, tt),

    Def Method "In" (xs : rep , x : word) : bool :=
        (b <- { b : bool | b = true <-> Ensembles.In _ xs x };
         ret (xs, b)),

    Def Method "Size" (xs : rep , _ : unit) : nat :=
          (n <- { n : nat | cardinal _ xs n };
           ret (xs, n))
  }.


(** Now we spec out two examples, the count of the unique elements in
    a list, and the sum of the unique elements in a list. *)

(** QUESTION: Do we want to start from [list]s?  From [Ensemble]s,
    somehow?  (But then how do we end up with computations not
    mentioning [Ensemble]s?)  Do we want to end up with something that
    takes in a [list], or something else? *)

Definition is_unique_list_of {T} (new orig : list T) : Prop
  := NoDup new /\ (forall x, List.In x orig <-> List.In x new).

(** QUESTION: Are these reasonable ways of specifying these specs? *)

Definition countUniqueSpec (ls : list word) : Comp nat
  := { n : nat | exists xs, is_unique_list_of xs ls /\ length xs = n }.

Definition sumUniqueSpec (ls : list word) : Comp word
  := xs <- { xs : list word | is_unique_list_of xs ls };
    ret (List.fold_right plus 0 xs).

Notation FullySharpenedComputation spec
  := { c : _ | refine spec (ret c) }%type.

(** Now we refine the implementations. *)
(** In a non-skeletal version, this would be done by a single
    monolithic tactic that gets passed the [FiniteSetImpl] (or picks
    it up from the context?).  (It would also, obviously, not use
    [admit].)  I feel reasonably comfortable figuring out how to write
    this tactic on my own, and am much more uncertain about how to set
    up the surrounding infrastruture for the statement of this
    definition/example, as demonstrated by my many QUESTIONs above. *)

(** QUESTION: Did I get the right target implementation that we want
    the tactics to find in the following two examples? *)

Definition countUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list word)
: FullySharpenedComputation (countUniqueSpec ls).
Proof.
  (** We turn the list into a finite set, and then call 'size' *)
  exists (snd (CallMethod (projT1 FiniteSetImpl) "Size"
                          (List.fold_right
                             (fun w xs => fst (CallMethod (projT1 FiniteSetImpl) "Add" xs w))
                             (CallConstructor (projT1 FiniteSetImpl) "Empty" tt)
                             ls)
                          tt)).
  admit.
Defined.

(** And now we do the same for summing. *)

Definition sumUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list word)
: FullySharpenedComputation (sumUniqueSpec ls).
Proof.
  (** We fold over the list, using a finite set to keep track of what
      we've seen, and every time we see something new, we update our
      running sum.  This should be compiled down to a for loop with an
      in-place update. *)
  exists (snd (List.fold_right
                 (fun w xs_sum =>
                    let xs := fst xs_sum in
                    let acc := snd xs_sum in
                    if (snd (CallMethod (projT1 FiniteSetImpl) "In" xs w) : bool)
                    then xs_sum
                    else (fst (CallMethod (projT1 FiniteSetImpl) "Add" xs w),
                          acc + w))
                 (CallConstructor (projT1 FiniteSetImpl) "Empty" tt,
                  0)
                 ls)).
  admit.
Defined.
