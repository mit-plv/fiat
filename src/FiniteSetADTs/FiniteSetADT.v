(** * Definition of the finite set spec *)
Require Import Coq.Strings.String Coq.Sets.Ensembles Coq.Sets.Finite_sets Coq.Lists.List Permutation.
Require Import ADT ADT.ComputationalADT ADTRefinement.Core ADTNotation ADTRefinement.GeneralRefinements Common.AdditionalEnsembleDefinitions Common.AdditionalEnsembleLemmas.

Set Implicit Arguments.

Local Open Scope string_scope.

(** TODO: Figure out where Facade words live, and use that *)
Module Type BedrockWordT.
  Axiom W : Type.
  Axiom wzero : W.
  Axiom wplus : W -> W -> W.
End BedrockWordT.

Module Export BedrockWord : BedrockWordT.
  Definition W := nat.
  Definition wzero := 0.
  Definition wplus := plus.
End BedrockWord.

(** TODO: Test: Do we get a speedup if we replace these definitions
    with [{| bindex := "$STRING-HERE" |}]? *)
Definition sEmpty := "Empty".
Definition sAdd := "Add".
Definition sRemove := "Remove".
Definition sIn := "In".
Definition sSize := "Size".

(** We define the interface for finite sets *)
(** QUESTION: Does Facade give us any other methods?  Do we want to
    provide any other methods? *)
Definition FiniteSetSig : ADTSig :=
  ADTsignature {
      Constructor sEmpty : unit -> rep,
      Method sAdd : rep x W -> rep x unit,
      Method sRemove : rep x W -> rep x unit,
      Method sIn : rep x W -> rep x bool,
      Method sSize : rep x unit -> rep x nat
    }.

(** And now the spec *)
Definition FiniteSetSpec : ADT FiniteSetSig :=
  ADTRep (Ensemble W) {
    Def Constructor sEmpty (_ : unit) : rep := ret (Empty_set _),

    Def Method sAdd (xs : rep , x : W) : unit :=
      ret (Add _ xs x, tt),

    Def Method sRemove (xs : rep , x : W) : unit :=
      ret (Subtract _ xs x, tt),

    Def Method sIn (xs : rep , x : W) : bool :=
        (b <- { b : bool | b = true <-> Ensembles.In _ xs x };
         ret (xs, b)),

    Def Method sSize (xs : rep , _ : unit) : nat :=
          (n <- { n : nat | cardinal _ xs n };
           ret (xs, n))
  }.


(** Now we spec out two examples, the count of the unique elements in
    a list, and the sum of the unique elements in a list. *)

Definition elements {A} (ls : list A) : Ensemble A := fun x => List.In x ls.

Definition cardinal {A} (ls : list A) : Comp nat
  := Pick (cardinal _ (elements ls)).

Definition to_list {A} (S : Ensemble A) : Comp (list A) :=
  { ls : list _ | EnsembleListEquivalence S ls }.

(** QUESTION: Should I switch [fold_right] and [Ensemble_fold_right]?
    Which is more common? *)
Definition fold_right {A B}
           (f : A -> B -> Comp B) (b : Comp B) (S : Ensemble A)
: Comp B
  := (ls <- to_list S;
      List.fold_right (fun a b' => Bind b' (f a)) b ls).

Definition Ensemble_fold_right {A B}
           (f : A -> B -> B) (b : B) (S : Ensemble A)
: Comp B
  := fold_right (fun a b => ret (f a b)) (ret b) S.

Lemma Ensemble_fold_right_simpl {A B} (f : A -> B -> B) b S
: refineEquiv (@fold_right A B (fun a b' => ret (f a b')) (ret b) S)
              (ls <- to_list S;
               ret (List.fold_right f b ls)).
Proof.
  unfold fold_right.
  f_equiv; intro ls; simpl.
  induction ls; simpl; try reflexivity.
  rewrite IHls.
  autorewrite with refine_monad.
  reflexivity.
Qed.

Lemma Ensemble_fold_right_simpl' {A B} f b S
: refineEquiv (@Ensemble_fold_right A B f b S)
              (ls <- to_list S;
               ret (List.fold_right f b ls)).
Proof.
  exact (Ensemble_fold_right_simpl f b S).
Qed.
