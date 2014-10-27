(** * Refinement of computations involving ensembles, to ones using finite sets *)
Require Import Coq.Strings.String Coq.Sets.Ensembles Coq.Sets.Finite_sets Coq.Lists.List Coq.Sorting.Permutation.
Require Import ADT ADT.ComputationalADT ADTRefinement.Core ADTNotation ADTRefinement.GeneralRefinements Common.AdditionalEnsembleDefinitions Common.AdditionalEnsembleLemmas Computation.
Require Export FiniteSetADTs.FiniteSetADT.
Require Import Common.

(** TODO: Move this elsewhere *)
Notation FullySharpenedComputation spec
  := { c : _ | refine spec (ret c) }%type.

(** We prove equivalences to handle various operations on ensembles,
    and on lists equivalent to ensembles. *)
Section FiniteSetHelpers.
  Context (FiniteSetImpl : FullySharpened FiniteSetSpec).

  Local Hint Extern 0 =>
  match goal with
    | [ H : False |- _ ] => destruct H
    | [ H : false = true |- _ ] => solve [ inversion H ]
    | [ H : true = false |- _ ] => solve [ inversion H ]
  end.
  Local Hint Extern 0 => apply Constructive_sets.Noone_in_empty.
  Local Hint Resolve Constructive_sets.Add_intro2 Constructive_sets.Add_intro1.

  Definition FiniteSetAndFunctionOfList {A} (f : W -> A -> A) (a : A)
             (ls : list W)
    := List.fold_right
         (fun w xs_acc =>
            let xs := fst xs_acc in
            let acc := snd xs_acc in
            ((if (snd (CallMethod (projT1 FiniteSetImpl) sIn xs w) : bool)
             then xs
             else fst (CallMethod (projT1 FiniteSetImpl) sAdd xs w)),
             (if (snd (CallMethod (projT1 FiniteSetImpl) sIn xs w) : bool)
              then acc
              else f w acc)))
         (CallConstructor (projT1 FiniteSetImpl) sEmpty tt,
          a)
         ls.

  Definition FiniteSetAndListOfList (ls : list W)
    := FiniteSetAndFunctionOfList (@cons _) nil ls.

  Definition EnsembleOfList (ls : list W) : Ensemble W
    := snd (FiniteSetAndFunctionOfList
              (fun w xs => Ensembles.Add _ xs w)
              (Ensembles.Empty_set _)
              ls).

  Definition FiniteSetOfList (ls : list W) : cRep (projT1 FiniteSetImpl)
    := List.fold_right
         (fun w xs =>
            if (snd (CallMethod (projT1 FiniteSetImpl) sIn xs w) : bool)
            then xs
            else fst (CallMethod (projT1 FiniteSetImpl) sAdd xs w))
         (CallConstructor (projT1 FiniteSetImpl) sEmpty tt)
         ls.

  Lemma NoFunctionJustFiniteSetOfFunction {A} f a ls
  : fst (@FiniteSetAndFunctionOfList A f a ls) = FiniteSetOfList ls.
  Proof.
    unfold FiniteSetOfList.
    unfold FiniteSetAndFunctionOfList.
    simpl.
    etransitivity; [ | eapply fst_fold_right ].
    reflexivity.
  Qed.

  Definition NoListJustFiniteSetOfList ls
  : fst (FiniteSetAndListOfList ls) = FiniteSetOfList ls
    := NoFunctionJustFiniteSetOfFunction _ _ _.

  Ltac handle_calls_then' tac :=
    idtac;
    let lem := match goal with
                 | [ |- context[(CallMethod (projT1 ?impl) ?idx) ?rep ?arg] ]
                   => constr:(fun rep' => ADTRefinementPreservesMethods (projT2 impl) {| bindex := idx |} rep' rep arg)
                 | [ |- context[(CallConstructor (projT1 ?impl) ?idx) ?arg] ]
                   => constr:(ADTRefinementPreservesConstructors (projT2 impl) {| bindex := idx |} arg)
                 | [ H : context[(CallMethod (projT1 ?impl) ?idx) ?rep ?arg] |- _ ]
                   => constr:(fun rep' => ADTRefinementPreservesMethods (projT2 impl) {| bindex := idx |} rep' rep arg)
                 | [ H : context[(CallConstructor (projT1 ?impl) ?idx) ?arg] |- _ ]
                   => constr:(ADTRefinementPreservesConstructors (projT2 impl) {| bindex := idx |} arg)
               end in
    let H' := fresh in
    first [ pose proof (fun rep' H => lem rep' H _ (ReturnComputes _)) as H'
          | pose proof (lem _ (ReturnComputes _)) as H' ];
      simpl in H';
      tac H'.

  Local Ltac pre_t :=
    repeat match goal with
             | _ => progress inversion_by computes_to_inv
             | _ => progress subst
             | _ => progress simpl in *
             | _ => progress split_iff
             | _ => progress destruct_head bool
             | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
             | _ => assumption
             | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
             | [ H : (_, _) = ?x |- _ ] => destruct x
           end.

  Lemma AbsR_EnsembleOfList_FiniteSetOfList ls
  : AbsR (projT2 FiniteSetImpl) (EnsembleOfList ls) (FiniteSetOfList ls).
  Proof.
    induction ls; simpl;
    handle_calls_then' ltac:(fun H => try specialize (H _ IHls));
    pre_t;
    unfold EnsembleOfList in *; simpl;
    rewrite NoFunctionJustFiniteSetOfFunction;
    handle_calls_then' ltac:(fun H => try specialize (H _ IHls));
    pre_t.
    { specialize_all_ways; auto. }
    { specialize_all_ways; auto. }
    { handle_calls_then' ltac:(fun H => try specialize (H _ IHls));
      pre_t. }
  Qed.

  Lemma EnsembleOfList_In (ls : list W)
  : forall x, Ensembles.In _ (EnsembleOfList ls) x <-> In x ls.
  Proof.
    induction ls;
    repeat match goal with
             | _ => split
             | _ => progress split_iff
             | [ H : Ensembles.In _ (Ensembles.Add _ _ _) _ |- _ ] => apply Constructive_sets.Add_inv in H
             | [ H : Ensembles.In _ (Empty_set _) _ |- _ ] => apply Constructive_sets.Noone_in_empty in H
             | _ => progress destruct_head or
             | _ => progress destruct_head_hnf Empty_set
             | _ => intro
             | _ => progress subst
             | _ => progress simpl in *
             | _ => solve [ eauto ]
             | _ => solve [ right; eauto ]
             | _ => left; reflexivity
             | _ => progress unfold EnsembleOfList in *
             | [ H : context[if ?E then _ else _] |- _ ]
               => revert H; case_eq E; intros
             | [ |- context[if ?E then _ else _] ]
               => case_eq E; intros
             | [ H : _ |- _ ] => progress rewrite NoFunctionJustFiniteSetOfFunction in H
           end.
    handle_calls_then' ltac:(fun H => specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfList _)));
      pre_t.
  Qed.

  Local Ltac t :=
    repeat match goal with
             | _ => reflexivity
             | _ => assumption
             | _ => progress inversion_by computes_to_inv
             | _ => progress subst
             | _ => progress simpl in *
             | _ => progress split_iff
             | _ => progress destruct_head_hnf bool
             | _ => split
             | _ => intro
             | [ H : ?T -> ?U, H' : ?T |- _ ] => specialize (H H')
             | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
             | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
             | [ H : (_, _) = ?x |- _ ] => destruct x
           end.

  Lemma classify_AbsR S fs
  : AbsR (projT2 FiniteSetImpl) S fs
    -> (forall x, Ensembles.In _ S x
                   <-> snd (CallMethod (projT1 FiniteSetImpl) sIn fs x) = true).
  Proof.
    t.
    { handle_calls_then' ltac:(fun H =>
                                 match goal with
                                   | [ H' : AbsR _ _ _ |- _ ] => specialize (H _ H')
                                 end).
      t. }
    { handle_calls_then' ltac:(fun H =>
                                 match goal with
                                   | [ H' : AbsR _ _ _ |- _ ] => specialize (H _ H')
                                 end).
      t. }
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
            { n : nat | AdditionalEnsembleDefinitions.cardinal _ S n })
           (ret (snd (CallMethod (projT1 FiniteSetImpl) sSize
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

  Lemma reverse_ensemble_list_equivalence_iff (S : Ensemble W)
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

  Lemma reverse_ensemble_list_equivalence_iff' {B} (S : Ensemble W) (f : _ -> Comp B)
  : refineEquiv (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 Bind {S0 : Ensemble W | forall x : W, Ensembles.In W S0 x <-> In x ls} f)
                (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 Bind { S' : _ | Same_set _ S' S } f).
  Proof.
    etransitivity; [ symmetry; apply refineEquiv_bind_bind | ].
    rewrite reverse_ensemble_list_equivalence_iff.
    apply refineEquiv_bind_bind.
  Qed.

  Lemma reverse_ensemble_list_equivalence_iff'' {B} (S : Ensemble W) (f : _ -> Comp B)
  : refine (ls <- {ls : list W | EnsembleListEquivalence S ls};
            Bind {S0 : Ensemble W | forall x : W, Ensembles.In W S0 x <-> In x ls} f)
           ({ls : list W | EnsembleListEquivalence S ls};;
            Bind { S' : _ | Same_set _ S' S } f).
  Proof.
    rewrite reverse_ensemble_list_equivalence_iff'.
    reflexivity.
  Qed.

  (*Lemma reverse_ensemble_list_equivalence (S : Ensemble W)
  : refineEquiv (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 ret (elements ls))
                (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 { S' : _ | Same_set _ S' S }).
  Proof.
    split; repeat intro;
    inversion_by computes_to_inv;
    subst.
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
  Qed.*)



  Lemma finite_set_handle_cardinal (S : Ensemble W)
  : refine { n : nat | AdditionalEnsembleDefinitions.cardinal _ S n }
           (ls <- { ls : _ | EnsembleListEquivalence S ls };
            ret (snd (CallMethod (projT1 FiniteSetImpl) sSize
                                 (FiniteSetOfList ls)
                                 tt))).
  Proof.
    simpl.
    setoid_rewrite <- finite_set_handle_cardinal_helper.
    rewrite reverse_ensemble_list_equivalence_iff'.
    rewrite <- refine_skip2.
    repeat intro;
      inversion_by computes_to_inv;
      constructor.
    eapply cardinal_Same_set; eassumption.
  Qed.

  (*Lemma FiniteSetAndListOfList_spec1 ls S
  : AbsR (projT2 FiniteSetImpl)
         S
         (fst (FiniteSetAndListOfList ls))
    <-> EnsembleListEquivalence S (snd (FiniteSetAndListOfList ls)).
  Proof.
    revert S.
    induction ls.
    { simpl.
      let lem := match goal with
                   | [ |- context[CallConstructor (projT1 ?impl) ?idx ?arg] ]
                     => constr:(ADTRefinementPreservesConstructors (projT2 impl) {| bindex := idx |} arg)
                   | [ IHls : AbsR _ _ _ |- context[CallMethod (projT1 ?impl) ?idx ?rep ?arg] ]
                     => constr:(ADTRefinementPreservesMethods (projT2 impl) {| bindex := idx |} _ rep arg IHls)
                 end in
      let lem' := constr:(lem  _ (ReturnComputes _)) in
      pose proof lem';
        inversion_by computes_to_inv;
        subst.
      intros; split.
      { repeat (intro || split || constructor || simpl in * || auto).
        match goal with
          | [ x : W, H1 : AbsR _ _ _, H2 : AbsR _ _ _ |- _ ]
            => let lem := constr:(ADTRefinementPreservesMethods
                                    (projT2 FiniteSetImpl)
                                    {| bindex := sIn |}) in
               pose proof (lem _ _ x H1 _ (ReturnComputes _));
                 pose proof (lem _ _ x H2 _ (ReturnComputes _))
        end.
        simpl in *.
        inversion_by computes_to_inv.
        repeat match goal with
                 | _ => progress simpl in *
                 | _ => progress subst
                 | _ => progress split_iff
                 | [ H : ?T -> ?U, H' : ?T |- _ ] => specialize (H H')
                 | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
                 | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
                 | [ H : (_, _) = ?x |- _ ] => destruct x
                 | _ => progress destruct_head_hnf Empty_set
               end. }
      { repeat first [ intro
                     | split
                     | constructor
                     | progress simpl in *
                     | progress split_iff
                     | progress destruct_head_hnf and ].
        (** TODO: eliminate extensionality_ensembles here? *)
        rewrite (Extensionality_Ensembles _ S (Empty_set _)); trivial.
        split; hnf; intros; unfold Ensembles.In in *;
        destruct_head_hnf Empty_set;
        solve [ exfalso; eauto ]. } }
    { simpl.
      match goal with
        | [ |- context[if ?E then _ else _] ] => case_eq E; intro
      end; auto.
      let lem := match goal with
                   | [ H : appcontext[CallMethod (projT1 ?impl) ?idx ?rep ?arg] |- _ ]
                     => constr:(fun rep' => ADTRefinementPreservesMethods (projT2 impl) {| bindex := idx |} rep' rep arg)
                 end in
      pose proof (fun rep' H => lem rep' H _ (ReturnComputes _));
        simpl in *.
      intro S.
      specialize (H0 (Subtract _ S a)).
      split.
      { intro H'.

      unfold refine in H0.
      simpl in H0.
      let lem' := constr:(lem  _ (ReturnComputes _)) in
      pose proof lem';
        inversion_by computes_to_inv;


      edestruct cMethods.
        exfalso; eauto.
        unfold Same_set in *.
        unfold Included in *.
        unfold iff in *.
 || auto).


        hnf in H2, H3.
        simpl in *.


        assert (Ensembles.In _ (Empty_set _) x).
        *)
  Lemma AbsR_EnsembleOfList_FiniteSetOfListOfFiniteSetAndListOfList ls
  : AbsR (projT2 FiniteSetImpl)
         (EnsembleOfList ls)
         (FiniteSetOfList (snd (FiniteSetAndListOfList ls))).
  Proof.
    induction ls; simpl.
    { handle_calls_then' ltac:(fun H => idtac).
      inversion_by computes_to_inv; subst; trivial. }
    { handle_calls_then' ltac:(fun H =>
                                 rewrite NoListJustFiniteSetOfList in *;
                                 specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfList _))).
      inversion_by computes_to_inv.
      destruct_head_hnf prod;
      destruct_head_hnf bool;
      t.
      { unfold EnsembleOfList in *; simpl in *.
        rewrite NoFunctionJustFiniteSetOfFunction in *.
        handle_calls_then' ltac:(fun H =>
                                   specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfList _))).
        t.
        eauto. }
      { unfold EnsembleOfList in *; simpl in *.
        rewrite NoFunctionJustFiniteSetOfFunction in *.
        let th :=
            handle_calls_then' ltac:(fun H =>
                                       match goal with
                                         | [ H' : AbsR _ _ _ |- _ ]
                                           => specialize (H _ H')
                                         | _ => specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfList _))
                                       end) in
        th;
          inversion_by computes_to_inv;
          t;
          eauto;
          th;
          inversion_by computes_to_inv;
          t;
          eauto;
          th;
          inversion_by computes_to_inv;
          t. } }
  Qed.

(*  Definition FiniteSetOfFiniteSetAndListOfList ls
  : AbsR (projT2 FiniteSetImpl) (EnsembleOfList ls) (FiniteSetOfList (snd (FiniteSetAndListOfList ls))).
  Proof.



                (ret ).
  Proof.*)

  Lemma refine_EnsembleListEquivalenceAdd_iff {T} ls a
  : refine (S <- {S : Ensemble T
                 | forall x, Ensembles.In T S x <-> a = x \/ List.In x ls};
            {ls' : list T | EnsembleListEquivalence S ls'})
           (S <- {S : Ensemble T
                 | forall x, Ensembles.In T S x <-> List.In x ls};
            ls' <- {ls' : list T | EnsembleListEquivalence S ls'};
            b <- { b : bool | b = true <-> List.In a ls };
            ret (if b then ls' else a::ls')).
  Proof.
    repeat intro.
    repeat match goal with
             | [ H : computes_to (Bind _ _) _ |- _ ]
               => apply computes_to_inv in H;
                 destruct_head_hnf ex;
                 destruct_head_hnf and
             | [ H : computes_to (ret _) _ |- _ ]
               => apply computes_to_inv in H
             | _ => progress subst
             | _ => progress inversion_by computes_to_inv
             | _ => progress split_iff
           end.
    let S := match goal with H : Ensemble _ |- _ => constr:H end in
    apply BindComputes with (comp_a_value := (Ensembles.Add _ S a));
      constructor;
      repeat match goal with
               | _ => intro
               | _ => split
               | _ => progress destruct_head_hnf Union
               | _ => progress destruct_head_hnf Singleton
               | _ => progress destruct_head_hnf sumbool
               | _ => progress destruct_head_hnf or
               | _ => progress destruct_head_hnf and
               | _ => progress destruct_head_hnf bool
               | _ => progress split_iff
               | _ => progress subst
               | _ => solve [ left; eauto ]
               | _ => solve [ right; eauto ]
               | [ H : forall x, Ensembles.In _ _ _ -> _, H' : Ensembles.In _ _ _ |- _ ]
                 => specialize (H _ H')
               | _ => solve [ eauto ]
               | _ => solve [ constructor; intuition ]
             end.
  Qed.

  Local Hint Constructors NoDup.

  Lemma refine_EnsembleListEquivalenceAdd {T} ls a
  : refine {ls' : list T | EnsembleListEquivalence (elements (a::ls)) ls'}
           (ls' <- {ls' : list T | EnsembleListEquivalence (elements ls) ls'};
            b <- { b : bool | b = true <-> List.In a ls };
            ret (if b then ls' else a::ls')).
  Proof.
    repeat intro.
    repeat match goal with
             | _ => assumption
             | _ => right; assumption
             | _ => intro
             | [ H : computes_to (Bind _ _) _ |- _ ]
               => apply computes_to_inv in H;
                 destruct_head_hnf ex;
                 destruct_head_hnf and
             | [ H : computes_to (ret _) _ |- _ ]
               => apply computes_to_inv in H
             | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
             | _ => progress subst
             | _ => progress destruct_head_hnf bool
             | _ => progress destruct_head_hnf or
             | _ => progress inversion_by computes_to_inv
             | _ => progress split_iff
             | _ => apply PickComputes
             | [ H : ?T -> false = true |- _ ]
               => assert (~T)
                 by (let H' := fresh in intro H'; specialize (H H'); inversion H);
                 clear H
             | [ |- EnsembleListEquivalence _ _ ] =>
               eapply EnsembleListEquivalence_Same_set; try eassumption; []
             | [ |- Same_set _ _ _ ] => split; repeat intro; hnf in *
             | [ |- EnsembleListEquivalence _ _ ] => destruct_head_hnf and; split
             | _ => progress unfold elements, Ensembles.In in *
             | [ |- NoDup (_::_) ] => constructor
             | _ => solve [ eauto ]
             | [ |- _ <-> _ ] => split
           end.
  Qed.

  Lemma finite_set_handle_EnsembleListEquivalence_iff (ls : list W)
  : refine (S <- { S : Ensemble W | forall x, Ensembles.In _ S x <-> List.In x ls };
            { ls' : _ | EnsembleListEquivalence S ls' })
           (ret (snd (FiniteSetAndListOfList ls))).
  Proof.
    simpl.
    induction ls; simpl.
    { autosetoid_rewrite with refine_monad.
      repeat first [ intro
                   | progress simpl
                   | rewrite <- refine_skip
                   | progress autosetoid_rewrite with refine_monad
                   | progress inversion_by computes_to_inv
                   | progress subst ].
      econstructor; repeat constructor; eauto; simpl; eauto. }
    { rewrite refine_EnsembleListEquivalenceAdd_iff.
      rewrite <- refineEquiv_bind_bind.
      rewrite IHls; clear IHls.
      autorewrite with refine_monad.
      rewrite NoListJustFiniteSetOfList.
      match goal with
        | [ |- context[if ?E then _ else _] ] => case_eq E; intro
      end;
        handle_calls_then'
          ltac:(fun H => specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfList _)));
        inversion_by computes_to_inv;
        t.
      { match goal with
          | [ H : Ensembles.In _ (EnsembleOfList _) _ |- _ ] => apply EnsembleOfList_In in H
        end.
        apply BindComputes with (comp_a_value := true);
        repeat constructor; eauto. }
      { apply BindComputes with (comp_a_value := false);
        repeat constructor; intros; eauto.
        match goal with
          | [ H : Ensembles.In _ (EnsembleOfList _) _ -> ?T |- ?T ]
            => apply H, EnsembleOfList_In; trivial
        end. } }
  Qed.

  Lemma finite_set_handle_EnsembleListEquivalence_iff' {A} (ls : list W) (f : _ -> Comp A)
  : refine (S <- { S : Ensemble W | forall x, Ensembles.In _ S x <-> List.In x ls };
            Bind { ls' : _ | EnsembleListEquivalence S ls' } f)
           (f (snd (FiniteSetAndListOfList ls))).
  Proof.
    simpl.
    rewrite <- refineEquiv_bind_bind.
    rewrite finite_set_handle_EnsembleListEquivalence_iff; simpl.
    match goal with
      | [ |- context[ret ?x] ] => generalize x; intro
    end.
    autorewrite with refine_monad.
    reflexivity.
  Qed.

  Lemma finite_set_handle_EnsembleListEquivalence (ls : list W)
  : refine { ls' : _ | EnsembleListEquivalence (elements ls) ls' }
           (ret (snd (FiniteSetAndListOfList ls))).
  Proof.
    simpl.
    induction ls; simpl.
    { autosetoid_rewrite with refine_monad.
      repeat first [ intro
                   | progress simpl
                   | rewrite <- refine_skip
                   | progress autosetoid_rewrite with refine_monad
                   | progress inversion_by computes_to_inv
                   | progress subst ].
      econstructor; repeat constructor; eauto; simpl; eauto. }
    { rewrite refine_EnsembleListEquivalenceAdd.
      rewrite IHls; clear IHls.
      autorewrite with refine_monad.
      rewrite NoListJustFiniteSetOfList.
      match goal with
        | [ |- context[if ?E then _ else _] ] => case_eq E; intro
      end;
        handle_calls_then'
          ltac:(fun H => specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfList _)));
        inversion_by computes_to_inv;
        t.
      { match goal with
          | [ H : Ensembles.In _ (EnsembleOfList _) _ |- _ ] => apply EnsembleOfList_In in H
        end.
        apply BindComputes with (comp_a_value := true);
        repeat constructor; eauto. }
      { apply BindComputes with (comp_a_value := false);
        repeat constructor; intros; eauto.
        match goal with
          | [ H : Ensembles.In _ (EnsembleOfList _) _ -> ?T |- ?T ]
            => apply H, EnsembleOfList_In; trivial
        end. } }
  Qed.

  Lemma CallSize_FiniteSetOfListOfFiniteSetAndListOfList ls arg
  : snd
      ((CallMethod (projT1 FiniteSetImpl) sSize)
         (FiniteSetOfList (snd (FiniteSetAndListOfList ls)))
         arg)
    = snd ((CallMethod (projT1 FiniteSetImpl) sSize)
             (FiniteSetOfList ls)
             arg).
  Proof.
    do 2 (handle_calls_then' ltac:(fun H =>
                                     first [ specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfListOfFiniteSetAndListOfList _))
                                           | specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfList _)) ]);
          inversion_by computes_to_inv;
          t).
    eapply cardinal_unique; eassumption.
  Qed.

  Lemma fold_right_snd_FiniteSetAndListOfList {A} (f : W -> A -> A) (a : A) ls
  : List.fold_right f a (snd (FiniteSetAndListOfList ls))
    = snd (FiniteSetAndFunctionOfList f a ls).
  Proof.
    simpl.
    induction ls; simpl; trivial.
    unfold FiniteSetAndListOfList in *.
    rewrite <- IHls.
    rewrite !NoFunctionJustFiniteSetOfFunction.
    match goal with
      | [ |- context[if ?x then _ else _] ] => case_eq x; intro
    end;
      reflexivity.
  Qed.
End FiniteSetHelpers.

Create HintDb finite_sets discriminated.

Hint Unfold FiniteSetADT.to_list FiniteSetADT.cardinal FiniteSetADT.fold_right : finite_sets.

Ltac start_FullySharpenedComputation :=
  eexists;
  match goal with
    | [ |- refine ?a ?b ] => let a' := eval hnf in a in change (refine a' b)
  end.

Ltac finish_FullySharpenedComputation :=
  reflexivity.

Notation Sharpening x := (refine x (ret _)).

Tactic Notation "begin" "sharpening" "computation" := start_FullySharpenedComputation.

Tactic Notation "finish" "sharpening" "computation" := finish_FullySharpenedComputation.

Ltac finite_set_sharpen_step FiniteSetImpl :=
  first [ setoid_rewrite (@finite_set_handle_cardinal FiniteSetImpl)
        | rewrite (@finite_set_handle_EnsembleListEquivalence FiniteSetImpl)
        | rewrite (@CallSize_FiniteSetOfListOfFiniteSetAndListOfList FiniteSetImpl)
        | rewrite (@fold_right_snd_FiniteSetAndListOfList FiniteSetImpl)
        | rewrite Ensemble_fold_right_simpl
        | rewrite Ensemble_fold_right_simpl'
        | progress autounfold with finite_sets
        | progress autorewrite with refine_monad ].

Tactic Notation "sharpen" "computation" "with" "FiniteSet" "implementation" ":=" constr(FiniteSetImpl) :=
  repeat finite_set_sharpen_step FiniteSetImpl.
