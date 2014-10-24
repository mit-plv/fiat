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

  Lemma AbsR_EnsembleOfList_FiniteSetOfList ls
  : AbsR (projT2 FiniteSetImpl) (EnsembleOfList ls) (FiniteSetOfList ls).
  Proof.
    induction ls; simpl;
    let lem := match goal with
                 | [ |- context[CallConstructor (projT1 ?impl) ?idx ?arg] ]
                   => constr:(ADTRefinementPreservesConstructors (projT2 impl) {| bindex := idx |} arg)
                 | [ IHls : AbsR _ _ _ |- context[CallMethod (projT1 ?impl) ?idx ?rep ?arg] ]
                   => constr:(ADTRefinementPreservesMethods (projT2 impl) {| bindex := idx |} _ rep arg IHls)
               end in
    let lem' := constr:(lem  _ (ReturnComputes _)) in
    pose proof lem' as H; simpl in *;
    repeat match goal with
             | _ => progress inversion_by computes_to_inv
             | _ => progress subst
             | _ => progress simpl in *
             | _ => assumption
             | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
             | [ H : (_, _) = ?x |- _ ] => destruct x
           end.
  Qed.

  Local Hint Immediate EnsembleOfList_In AbsR_EnsembleOfList_FiniteSetOfList.

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

  Lemma refine_skip2 {A B} (a : Comp A) (dummy : Comp B)
  : refine a
           (dummy;;
            a).
  Proof.
    repeat first [ intro
                 | inversion_by computes_to_inv
                 | assumption
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

  Lemma finite_set_handle_cardinal_helper (ls : list W)
  : refine (S <- { S : Ensemble W | forall x, Ensembles.In _ S x <-> List.In x ls  };
            { n : nat | cardinal _ S n })
           (ret (snd (CallMethod (projT1 FiniteSetImpl) "Size"
                                 (FiniteSetOfList ls)
                                 tt))).
  Proof.
    etransitivity; [ | apply comp_split_snd ].
    handle_calls; [ | apply AbsR_EnsembleOfList_FiniteSetOfList ].
    repeat first [ progress simpl
                 | rewrite <- refine_skip
                 | autosetoid_rewrite with refine_monad ].
    repeat intro; eauto.
  Qed.

  Lemma reverse_ensemble_list_equivalence (S : Ensemble W)
  : refineEquiv (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 {S0 : Ensemble W | forall x : W, Ensembles.In W S0 x <-> In x ls})
                (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 { S' : _ | Same_set _ S' S }).
  Proof.
    split; repeat intro;
    inversion_by computes_to_inv;
    subst;
    repeat constructor;
    let x := match goal with H : EnsembleListEquivalence _ ?x |- _ => constr:x end in
    apply BindComputes with (comp_a_value := x);
      destruct_head_hnf and;
      split_iff;
      repeat constructor;
      hnf;
      auto.
  Qed.

  Lemma reverse_ensemble_list_equivalence' {B} (S : Ensemble W) (f : _ -> Comp B)
  : refineEquiv (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 Bind {S0 : Ensemble W | forall x : W, Ensembles.In W S0 x <-> In x ls} f)
                (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 Bind { S' : _ | Same_set _ S' S } f).
  Proof.
    etransitivity; [ symmetry; apply refineEquiv_bind_bind | ].
    rewrite reverse_ensemble_list_equivalence.
    apply refineEquiv_bind_bind.
  Qed.

  Lemma reverse_ensemble_list_equivalence'' {B} (S : Ensemble W) (f : _ -> Comp B)
  : refine (ls <- {ls : list W | EnsembleListEquivalence S ls};
            Bind {S0 : Ensemble W | forall x : W, Ensembles.In W S0 x <-> In x ls} f)
           ({ls : list W | EnsembleListEquivalence S ls};;
            Bind { S' : _ | Same_set _ S' S } f).
  Proof.
    rewrite reverse_ensemble_list_equivalence'.
    reflexivity.
  Qed.

  Lemma finite_set_handle_cardinal (S : Ensemble W)
  : refine { n : nat | cardinal _ S n }
           (ls <- { ls : _ | EnsembleListEquivalence S ls };
            ret (snd (CallMethod (projT1 FiniteSetImpl) "Size"
                                 (FiniteSetOfList ls)
                                 tt))).
  Proof.
    setoid_rewrite <- finite_set_handle_cardinal_helper.
    rewrite reverse_ensemble_list_equivalence'.
    rewrite <- refine_skip2.
    repeat intro;
      inversion_by computes_to_inv;
      constructor.
    (** TODO: redefine [cardinal] so that it says that [fun _ => False] has cardinality 0 *)
    match goal with
      | [ H : _ |- _ ] => apply Extensionality_Ensembles in H
    end.
    subst; assumption.
  Qed.

  Lemma finite_set_handle_EnsembleListEquivalence (ls : list W)
  : refine (S <- { S : Ensemble W | forall x, Ensembles.In _ S x <-> List.In x ls };
            { ls' : _ | EnsembleListEquivalence S ls' })
           (ret (snd (List.fold_right
                        (fun w xs_ls' =>
                           let xs := fst xs_ls' in
                           let ls' := snd xs_ls' in
                           if (snd (CallMethod (projT1 FiniteSetImpl) "In" xs w) : bool)
                           then xs_ls'
                           else (fst (CallMethod (projT1 FiniteSetImpl) "Add" xs w),
                                 w::ls'))
                        (CallConstructor (projT1 FiniteSetImpl) "Empty" tt,
                         nil)
                        ls))).
  Proof.
    induction ls; simpl.
    { autosetoid_rewrite with refine_monad.
      repeat first [ intro
                   | progress simpl
                   | rewrite <- refine_skip
                   | progress autosetoid_rewrite with refine_monad
                   | progress inversion_by computes_to_inv
                   | progress subst ].
      econstructor; repeat constructor; eauto; simpl; eauto. }
    { admit. }
  Qed.

  Lemma finite_set_handle_EnsembleListEquivalence' {A} (ls : list W) (f : _ -> Comp A)
  : refine (S <- { S : Ensemble W | forall x, Ensembles.In _ S x <-> List.In x ls };
            Bind { ls' : _ | EnsembleListEquivalence S ls' } f)
           (f (snd (List.fold_right
                      (fun w xs_ls' =>
                         let xs := fst xs_ls' in
                         let ls' := snd xs_ls' in
                         if (snd (CallMethod (projT1 FiniteSetImpl) "In" xs w) : bool)
                         then xs_ls'
                         else (fst (CallMethod (projT1 FiniteSetImpl) "Add" xs w),
                               w::ls'))
                      (CallConstructor (projT1 FiniteSetImpl) "Empty" tt,
                       nil)
                      ls))).
  Proof.
    rewrite <- refineEquiv_bind_bind.
    rewrite finite_set_handle_EnsembleListEquivalence.
    match goal with
      | [ |- context[ret ?x] ] => generalize x; intro
    end.
    autorewrite with refine_monad.
    reflexivity.
  Qed.
End FiniteSetHelpers.

Definition countUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (countUniqueSpec ls).
Proof.
  (** We turn the list into a finite set, and then call 'size' *)
  eexists.
  match goal with
    | [ |- refine ?a ?b ] => let a' := eval hnf in a in change (refine a' b)
  end.
  setoid_rewrite (@finite_set_handle_cardinal FiniteSetImpl).
  rewrite (@finite_set_handle_EnsembleListEquivalence' FiniteSetImpl).
  reflexivity. (*
  exists (snd (CallMethod (projT1 FiniteSetImpl) "Size"
                          (List.fold_right
                             (fun w xs => fst (CallMethod (projT1 FiniteSetImpl) "Add" xs w))
                             (CallConstructor (projT1 FiniteSetImpl) "Empty" tt)
                             ls)
                          tt)).
  admit. *)
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
