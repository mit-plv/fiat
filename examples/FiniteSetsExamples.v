(** * Some examples about dealing with finite sets *)
Require Import Coq.Strings.String Coq.Sets.Ensembles Coq.Sets.Finite_sets Coq.Lists.List.
Require Import ADT ADT.ComputationalADT ADTRefinement.Core ADTNotation ADTRefinement.GeneralRefinements QueryStructure.IndexedEnsembles.

Set Implicit Arguments.

Local Open Scope string_scope.

(** TODO: Figure out where Facade words live, and use that *)
Module Type BedrockWordT.
  Axiom W : Type.
  Axiom wzero : W.
  Axiom wplus : W -> W -> W.
End BedrockWordT.

Module Import BedrockWord : BedrockWordT.
  Definition W := nat.
  Definition wzero := 0.
  Definition wplus := plus.
End BedrockWord.

(** We define the interface for finite sets *)
(** QUESTION: Does Facade give us any other methods?  Do we want to
    provide any other methods? *)
Definition FiniteSetSig : ADTSig :=
  ADTsignature {
      Constructor "Empty" : unit -> rep,
      Method "Add" : rep x W -> rep x unit,
      Method "Remove" : rep x W -> rep x unit,
      Method "In" : rep x W -> rep x bool,
      Method "Size" : rep x unit -> rep x nat
    }.

(** And now the spec *)
Definition FiniteSetSpec : ADT FiniteSetSig :=
  ADTRep (Ensemble W) {
    Def Constructor "Empty" (_ : unit) : rep := ret (Empty_set _),

    Def Method "Add" (xs : rep , x : W) : unit :=
      ret (Add _ xs x, tt),

    Def Method "Remove" (xs : rep , x : W) : unit :=
      ret (Subtract _ xs x, tt),

    Def Method "In" (xs : rep , x : W) : bool :=
        (b <- { b : bool | b = true <-> Ensembles.In _ xs x };
         ret (xs, b)),

    Def Method "Size" (xs : rep , _ : unit) : nat :=
          (n <- { n : nat | cardinal _ xs n };
           ret (xs, n))
  }.


(** Now we spec out two examples, the count of the unique elements in
    a list, and the sum of the unique elements in a list. *)

(** QUESTION: Are these reasonable ways of specifying these specs? *)

Definition countUniqueSpec (ls : list W) : Comp nat
  := (S <- { S : Ensemble W | forall x, Ensembles.In _ S x <-> List.In x ls  };
      { n : nat | cardinal _ S n }).

Definition countUniqueSpec' (ls : list W) : Comp nat
  := (S <- { S : Ensemble W | forall x, Ensembles.In _ S x <-> List.In x ls  };
      xs <- { ls' : list W | EnsembleListEquivalence S ls' };
      ret (List.length xs)).

Definition sumUniqueSpec (ls : list W) : Comp W
  := (S <- { S : Ensemble W | forall x, Ensembles.In _ S x <-> List.In x ls };
      xs <- { ls' : list W | EnsembleListEquivalence S ls' };
      ret (List.fold_right wplus wzero xs)).

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

(*Lemma cardinal_to_list {T} (S : Ensemble T)
: refineEquiv { n : nat | cardinal _ S n }
              (xs <- { ls : list T | EnsembleListEquivalence S ls };
               ret (length xs)).
  *)
(** We prove equivalences to handle various operations on ensembles,
    and on lists equivalent to ensembles. *)
Section FiniteSetHelpers.
  Context (FiniteSetImpl : FullySharpened FiniteSetSpec).

  Local Hint Extern 0 =>
  match goal with
    | [ H : False |- _ ] => destruct H
  end.
  Local Hint Extern 0 => apply Constructive_sets.Noone_in_empty.
  Local Hint Resolve Constructive_sets.Add_intro2 Constructive_sets.Add_intro1.

  Definition FiniteSetOfList (ls : list W) : cRep (projT1 FiniteSetImpl)
    := List.fold_right
         (fun w xs => fst (CallMethod (projT1 FiniteSetImpl) "Add" xs w))
         (CallConstructor (projT1 FiniteSetImpl) "Empty" tt)
         ls.

  Definition EnsembleOfList {T} (ls : list T) : Ensemble T
    := List.fold_right
         (fun w xs => Ensembles.Add _ xs w)
         (Ensembles.Empty_set _)
         ls.

  Lemma EnsembleOfList_In {T} (ls : list T)
  : forall x, Ensembles.In _ (EnsembleOfList ls) x <-> In x ls.
  Proof.
    induction ls;
    repeat match goal with
             | _ => split
             | _ => progress split_iff
             | [ H : Ensembles.In _ (Ensembles.Add _ _ _) _ |- _ ] => apply Constructive_sets.Add_inv in H
             | [ H : Ensembles.In _ (Empty_set _) _ |- _ ] => apply Constructive_sets.Noone_in_empty in H
             | _ => progress destruct_head or
             | _ => intro
             | _ => progress subst
             | _ => progress simpl in *
             | _ => solve [ eauto ]
             | _ => solve [ right; eauto ]
             | _ => left; reflexivity
           end.
  Qed.

  (*Lemma EnsembleOfList_FiniteSetOfList ls
  : AbsR (projT2 FiniteSetImpl) (EnsembleOfList ls) (FiniteSetOfList ls).
  Proof.
    unfold EnsembleOfList, FiniteSetOfList;
    induction ls; simpl.
    Set Printing Coercions.
    lazymatch goal with
      | [ |- context[CallConstructor (projT1 ?impl) ?idx ?arg] ]
        => idtac;
          let lem := constr:(ADTRefinementPreservesConstructors (projT2 impl) {| bindex := idx |} arg) in
           pose proof lem; simpl in *
    end.
    hnf in H.

    *)

  Lemma comp_split_snd {A B} (x : A * B)
  : refineEquiv (ret (snd x))
                (ab <- ret x;
                 ret (snd ab)).
  Proof.
    autorewrite with refine_monad; reflexivity.
  Qed.

  Lemma refine_skip {A B C} (c : Comp A) (f : A -> Comp B) (dummy : A -> Comp C)
  : refine (Bind c f)
           (a <- c;
            dummy a;;
                  f a).
  Proof.
    repeat first [ intro
                 | inversion_by computes_to_inv
                 | econstructor; eassumption
                 | econstructor; try eassumption; [] ].
  Qed.

  Ltac handle_calls :=
    repeat match goal with
             | [ |- context[ret ((CallMethod (projT1 ?impl) ?idx) ?rep ?arg)] ]
               => let lem := constr:(fun rep' => ADTRefinementPreservesMethods (projT2 impl) {| bindex := idx |} rep' rep arg) in
                  simpl rewrite <- lem
             | [ |- context[ret ((CallConstructor (projT1 ?impl) ?idx) ?arg)] ]
               => let lem := constr:(ADTRefinementPreservesConstructors (projT2 impl) {| bindex := idx |} arg) in
                  simpl rewrite <- lem
           end.

  Lemma finite_set_handle_cardinal (ls : list W)
  : refine (S <- { S : Ensemble W | forall x, Ensembles.In _ S x <-> List.In x ls  };
            { n : nat | cardinal _ S n })
           (ret (snd (CallMethod (projT1 FiniteSetImpl) "Size"
                                 (FiniteSetOfList ls)
                                 tt))).
  Proof.
    etransitivity; [ | apply comp_split_snd ].
    handle_calls.
    repeat first [ progress simpl
                 | rewrite <- refine_skip
                 | autosetoid_rewrite with refine_monad ].
    instantiate (1 := EnsembleOfList ls).
    { repeat intro.
      econstructor; try eassumption; [].
      inversion_by computes_to_inv.
      constructor.
      apply EnsembleOfList_In. }
    { (** HELP: How can I prove this?  It seems false, if, e.g.,
          [FiniteSetImpl] decides to use [False] as it's
          representation.  But if this is unprovable, then
          [ADTRefinementPreservesConstructors] seems utterly
          useless. *)
      admit. }
  Qed.
End FiniteSetHelpers.

Definition countUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
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

Definition sumUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
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
                          wplus acc w))
                 (CallConstructor (projT1 FiniteSetImpl) "Empty" tt,
                  wzero)
                 ls)).
  admit.
Defined.
