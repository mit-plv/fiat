(** * Refinement of computations involving ensembles, to ones using finite sets *)

Require Import Coq.Strings.String
   Coq.Sets.Ensembles
   Coq.Sets.Finite_sets
   Coq.Lists.List
   Coq.Sorting.Permutation
   Coq.Classes.RelationPairs
   Fiat.ADT
   Fiat.ADT.ComputationalADT
   Fiat.ADTRefinement.Core
   Fiat.ADTNotation
   Fiat.ADTRefinement.GeneralRefinements
   Fiat.Computation
   Fiat.Common
   Fiat.Common.Ensembles
   Fiat.Common.Ensembles.Tactics
   Fiat.ComputationalEnsembles
   Fiat.FiniteSetADTs.FiniteSetADTMethodLaws.
Require Export Fiat.FiniteSetADTs.FiniteSetADT.

(** TODO: Move this elsewhere *)
Notation FullySharpenedComputation spec
  := { c : _ | refine spec (ret c) }%type.

(** We prove equivalences to handle various operations on ensembles,
    and on lists equivalent to ensembles. *)

Local Open Scope Ensemble_scope.

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

  Definition ValidFiniteSetAndFunctionOfList_body {A} (f : W -> A -> A)
  : W
    -> (sigT (fun fs => sig (fun S0 => AbsR (projT2 FiniteSetImpl) S0 fs))) * A
    -> (sigT (fun fs => sig (fun S0 => AbsR (projT2 FiniteSetImpl) S0 fs))) * A.
  Proof.
    refine (fun w xs_acc =>
              let xs := fst xs_acc in
              let acc := snd xs_acc in
              ((if (snd (CallMethod (projT1 FiniteSetImpl) sIn (projT1 xs) w) : bool)
                then xs
                else (existT _ (fst (CallMethod (projT1 FiniteSetImpl) sAdd (projT1 xs) w)) _)),
               (if (snd (CallMethod (projT1 FiniteSetImpl) sIn (projT1 xs) w) : bool)
                then acc
                else f w acc))).
    abstract (
        destruct xs_acc as [[? ?] ?]; subst_body; simpl in *; destruct_head sig;
        eexists;
        apply AbsR_ToEnsemble_Add;
        eassumption
      ).
  Defined.

  Definition ValidFiniteSetAndFunctionOfList {A} (f : W -> A -> A) (a : A)
             (ls : list W)
  : (sigT (fun fs => sig (fun S0 => AbsR (projT2 FiniteSetImpl) S0 fs))) * A.
  Proof.
    refine (List.fold_right
              (ValidFiniteSetAndFunctionOfList_body f)
              (existT (fun fs => sig (fun S0 => AbsR (projT2 FiniteSetImpl) S0 fs))
                      (CallConstructor (projT1 FiniteSetImpl) sEmpty tt)
                      _,
               a)
              ls);
    eexists; apply AbsR_ToEnsemble_Empty.
  Defined.

  Definition FiniteSetAndFunctionOfList_ValidFiniteSetAndFunctionOfList {A} f a ls
  : @FiniteSetAndFunctionOfList A f a ls
    = (projT1 (fst (@ValidFiniteSetAndFunctionOfList A f a ls)), snd (@ValidFiniteSetAndFunctionOfList A f a ls)).
  Proof.
    unfold FiniteSetAndFunctionOfList, ValidFiniteSetAndFunctionOfList, ValidFiniteSetAndFunctionOfList_body; simpl.
    let H := fresh in
    match goal with
      | [ |- List.fold_right (fun (x : ?X) (acc : ?A * ?B) =>
                                (@?f0 x acc, @?g x acc))
                             ?init
                             ?ls
             = (projT1 (fst (List.fold_right _ (existT ?P _ ?pf, _) _)), _) ]
        => let f' := constr:(fun b x a => f0 x (a, b)) in
           let f'' := (eval simpl in f') in
           let f''' := match f'' with fun _ => ?f''' => constr:(f''') end in
           pose proof (@fold_right_projT1 A B X P init ls f''' (fun x a b => g x (a, b)) pf) as H
    end;
      simpl in *;
      erewrite H.
    repeat match goal with
             | _ => reflexivity
             | _ => rewrite !push_if_existT
             | _ => progress simpl in *
             | [ |- (_, _) = (_, _) ] => apply injective_projections; simpl
             | [ |- fst _ = fst _ ] => apply f_equal
             | [ |- snd _ = snd _ ] => apply f_equal
             | [ |- projT1 _ = projT1 _ ] => apply f_equal
             | [ |- List.fold_right _ _ _ = List.fold_right _ _ _ ] => apply fold_right_f_eq_mor
             | _ => intro
           end.
  Qed.

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

  Definition ValidFiniteSetOfList_body
  : W
    -> (sigT (fun fs => sig (fun S0 => AbsR (projT2 FiniteSetImpl) S0 fs)))
    -> (sigT (fun fs => sig (fun S0 => AbsR (projT2 FiniteSetImpl) S0 fs))).
  Proof.
    refine (fun w xs =>
              if (snd (CallMethod (projT1 FiniteSetImpl) sIn (projT1 xs) w) : bool)
              then xs
              else (existT _ (fst (CallMethod (projT1 FiniteSetImpl) sAdd (projT1 xs) w)) _)).
    abstract (
        destruct xs as [? ?]; subst_body; simpl in *; destruct_head sig;
        eexists;
        apply AbsR_ToEnsemble_Add;
        eassumption
      ).
  Defined.

  Definition ValidFiniteSetOfList
             (ls : list W)
  : (sigT (fun fs => sig (fun S0 => AbsR (projT2 FiniteSetImpl) S0 fs))).
  Proof.
    refine (List.fold_right
              ValidFiniteSetOfList_body
              (existT (fun fs => sig (fun S0 => AbsR (projT2 FiniteSetImpl) S0 fs))
                      (CallConstructor (projT1 FiniteSetImpl) sEmpty tt)
                      _)
              ls);
    eexists; apply AbsR_ToEnsemble_Empty.
  Defined.


  Definition FiniteSetOfList_ValidFiniteSetOfList ls
  : @FiniteSetOfList ls = projT1 (@ValidFiniteSetOfList ls).
  Proof.
    unfold FiniteSetOfList, ValidFiniteSetOfList, ValidFiniteSetOfList_body; simpl.
    let H := fresh in
    lazymatch goal with
      | [ |- List.fold_right ?f ?init ?ls
             = projT1 (List.fold_right _ (existT ?P _ ?pf) _) ]
        => pose proof (@fold_right_projT1' _ _ P init ls f pf) as H
    end;
      simpl in *;
      erewrite H.
    repeat match goal with
             | _ => reflexivity
             | _ => rewrite !push_if_existT
             | _ => progress simpl in *
             | [ |- (_, _) = (_, _) ] => apply injective_projections; simpl
             | [ |- fst _ = fst _ ] => apply f_equal
             | [ |- snd _ = snd _ ] => apply f_equal
             | [ |- projT1 _ = projT1 _ ] => apply f_equal
             | [ |- List.fold_right _ _ _ = List.fold_right _ _ _ ] => apply fold_right_f_eq_mor
             | _ => intro
           end.
  Qed.

  Definition FunctionOfList {A} (f : W -> A -> A) (a : A)
             (ls : list W)
    := snd (FiniteSetAndFunctionOfList f a ls).

  Definition UniqueListOfList (ls : list W) : list W
    := FunctionOfList (@cons _) nil ls.

  Definition UniqueFilterOfList (ls : list W) (P : W -> bool) : list W
    := FunctionOfList (fun x xs => if P x then (x::xs) else xs) nil ls.

  Lemma NoFiniteSetJustFunctionOfList {A} f a ls
  : snd (@FiniteSetAndFunctionOfList A f a ls) = FunctionOfList f a ls.
  Proof.
    reflexivity.
  Qed.

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

  Definition NoFiniteSetJustListOfList ls
  : snd (FiniteSetAndListOfList ls) = UniqueListOfList ls
    := NoFiniteSetJustFunctionOfList _ _ _.

  Definition FunctionIsListOfList ls
  : FunctionOfList _ _ _ = UniqueListOfList ls
    := reflexivity _.

  Definition NoFiniteSetJustFilterFunctionOfList P ls
  : snd (@FiniteSetAndFunctionOfList _ _ _ ls) = UniqueFilterOfList ls P
    := reflexivity _.

  Lemma FiniteSetAndFunctionOfList_pull_ret {A} (f : W -> A -> A) (a : A)
        (ls : list W)
  : refineEquiv (snd (FiniteSetAndFunctionOfList (fun w acc => a' <- acc; ret (f w a')) (ret a) ls))
                (ret (snd (FiniteSetAndFunctionOfList f a ls))).
  Proof.
    revert a; induction ls; simpl.
    { reflexivity. }
    { intro; simpl in *.
      rewrite !NoFunctionJustFiniteSetOfFunction.
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end.
      { rewrite <- IHls; reflexivity. }
      { rewrite IHls; autorewrite with refine_monad; reflexivity. } }
  Qed.

  Definition FunctionOfList_pull_ret {A} (f : W -> A -> A) (a : A)
        (ls : list W)
  : refineEquiv (FunctionOfList (fun w acc => a' <- acc; ret (f w a')) (ret a) ls)
                (ret (FunctionOfList f a ls))
    := FiniteSetAndFunctionOfList_pull_ret f a ls.

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
  : forall x, Ensembles.In _ (EnsembleOfList ls) x <-> List.In x ls.
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

  Ltac handle_calls :=
    repeat match goal with
             | [ |- context[ret ((CallMethod (projT1 ?impl) ?idx) ?rep ?arg)] ]
               => let lem := constr:(fun rep' => ADTRefinementPreservesMethods (projT2 impl) {| bindex := idx |} rep' rep arg) in
                  simpl rewrite <- lem
             | [ |- context[ret ((CallConstructor (projT1 ?impl) ?idx) ?arg)] ]
               => let lem := constr:(ADTRefinementPreservesConstructors (projT2 impl) {| bindex := idx |} arg) in
                  simpl rewrite <- lem
           end.

  Lemma FiniteSetAndFunctionOfList_proper {A} (R : relation A)
        (f f' : W -> A -> A) (a a' : A)
        (ls : list W)
        (Rf : pointwise_relation _ (respectful R R) f f')
        (RA : R a a')
  : R (snd (FiniteSetAndFunctionOfList f a ls))
      (snd (FiniteSetAndFunctionOfList f' a' ls)).
  Proof.
    unfold pointwise_relation, respectful in *.
    revert a a' RA.
    induction ls; simpl; trivial.
    intros.
    rewrite !NoFunctionJustFiniteSetOfFunction.
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E; auto
    end.
  Qed.

  Local Ltac FunctionOfList_proper_t :=
    unfold FunctionOfList; intros;
    apply FiniteSetAndFunctionOfList_proper;
    unfold pointwise_relation, respectful in *;
    eauto; try reflexivity.

  Global Add Parametric Morphism A : (@FunctionOfList (Comp A))
  with signature pointwise_relation _ (respectful refine refine) ==> eq ==> eq ==> refine
    as refine_FunctionOfList_mor1.
  Proof. FunctionOfList_proper_t. Qed.

  Global Add Parametric Morphism A : (@FunctionOfList (Comp A))
  with signature pointwise_relation _ (respectful refineEquiv refineEquiv) ==> eq ==> eq ==> refineEquiv
    as refineEquiv_FunctionOfList_mor1.
  Proof. FunctionOfList_proper_t. Qed.

  Global Add Parametric Morphism A f `{Proper _ (pointwise_relation _ (respectful refine refine)) f}
  : (@FunctionOfList (Comp A) f)
  with signature refine ==> eq ==> refine
    as refine_FunctionOfList_mor2.
  Proof. FunctionOfList_proper_t. Qed.

  Global Add Parametric Morphism A f `{Proper _ (pointwise_relation _ (respectful refineEquiv refineEquiv)) f}
  : (@FunctionOfList (Comp A) f)
  with signature refineEquiv ==> eq ==> refineEquiv
    as refineEquiv_FunctionOfList_mor2.
  Proof. FunctionOfList_proper_t. Qed.

  Global Add Parametric Morphism A f `{Proper _ (pointwise_relation _ (respectful refine refine)) f}
  : (@FunctionOfList (Comp A) f)
  with signature refineEquiv ==> eq ==> refineEquiv
    as refineEquiv_FunctionOfList_mor2'.
  Proof.
    intros; apply refineEquiv_FunctionOfList_mor2; trivial.
    unfold Proper, pointwise_relation, respectful in *.
    repeat intro; destruct_head_hnf and; split; eauto.
 Qed.

  Lemma finite_set_handle_cardinal_helper (ls : list W)
  : refine (S <- { S : Ensemble W | forall x, Ensembles.In _ S x <-> List.In x ls  };
            FiniteSetADT.cardinal S)
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
                 {S0 : Ensemble W | forall x : W, Ensembles.In W S0 x <-> List.In x ls})
                (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 { S' : _ | Same_set _ S' S }).
  Proof.
    split; repeat intro;
    inversion_by computes_to_inv;
    subst;
    repeat constructor;
    let x := match goal with H : EnsembleListEquivalence _ ?x |- _ => constr:(x) end in
    apply BindComputes with (comp_a_value := x);
      destruct_head_hnf and;
      split_iff;
      repeat constructor;
      hnf;
      auto.
  Qed.

  Lemma reverse_ensemble_list_equivalence_iff' {B} (S : Ensemble W) (f : _ -> Comp B)
  : refineEquiv (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 Bind {S0 : Ensemble W | forall x : W, Ensembles.In W S0 x <-> List.In x ls} f)
                (ls <- {ls : list W | EnsembleListEquivalence S ls};
                 Bind { S' : _ | Same_set _ S' S } f).
  Proof.
    etransitivity; [ symmetry; apply refineEquiv_bind_bind | ].
    rewrite reverse_ensemble_list_equivalence_iff.
    apply refineEquiv_bind_bind.
  Qed.

  Lemma reverse_ensemble_list_equivalence_iff'' {B} (S : Ensemble W) (f : _ -> Comp B)
  : refine (ls <- {ls : list W | EnsembleListEquivalence S ls};
            Bind {S0 : Ensemble W | forall x : W, Ensembles.In W S0 x <-> List.In x ls} f)
           ({ls : list W | EnsembleListEquivalence S ls};;
            Bind { S' : _ | Same_set _ S' S } f).
  Proof.
    rewrite reverse_ensemble_list_equivalence_iff'.
    reflexivity.
  Qed.

  Global Add Parametric Morphism : FiniteSetADT.cardinal
      with signature Same_set _ ==> refineEquiv
        as Same_set_cardinal.
  Proof.
    unfold FiniteSetADT.cardinal.
    intros x y H.
    setoid_rewrite H; reflexivity.
  Qed.

  Lemma finite_set_handle_cardinal (S : Ensemble W)
  : refine (FiniteSetADT.cardinal S)
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
      inversion_by computes_to_inv.
    match goal with
      | [ H : _ ≅ _, H' : computes_to ?a ?v |- computes_to ?b ?v ]
        => revert v H'; change (refine b a); rewrite H
    end.
    reflexivity.
  Qed.

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
    let S := match goal with H : Ensemble _ |- _ => constr:(H) end in
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

  Lemma FiniteSetOfListOfFiniteSetAndListOfList ls
  : FiniteSetOfList (snd (FiniteSetAndListOfList ls))
    = FiniteSetOfList ls.
  Proof.
    induction ls; simpl; trivial.
    rewrite (pull_if FiniteSetOfList); simpl.
    rewrite IHls.
    rewrite !NoListJustFiniteSetOfList.
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end;
      reflexivity.
  Qed.

  Lemma FiniteSetOfUniqueListOfList ls
  : FiniteSetOfList (UniqueListOfList ls) = FiniteSetOfList ls.
  Proof.
    apply FiniteSetOfListOfFiniteSetAndListOfList.
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

  Lemma fold_right_UniqueListOfList {A} (f : W -> A -> A) (a : A) ls
  : List.fold_right f a (UniqueListOfList ls)
    = snd (FiniteSetAndFunctionOfList f a ls).
  Proof.
    apply fold_right_snd_FiniteSetAndListOfList.
  Qed.

  Lemma refineEquivUnion {T A} P (P_respectful : forall S1 S2 x, Same_set A S1 S2 -> (P S1 x <-> P S2 x))
        (S1 S2 : Ensemble A)
  : refine { x : T | P (Ensembles.Union A S1 S2) x }
           (ls1 <- to_list S1;
            ls2 <- to_list S2;
            { x : T | P (elements (ls1 ++ ls2)) x }).
  Proof.
    unfold to_list, elements;
    repeat intro;
    inversion_by computes_to_inv.
    constructor.
    eapply P_respectful; try eassumption.
    repeat first [ split
                 | progress hnf in *
                 | intro
                 | progress destruct_head_hnf Union
                 | progress destruct_head_hnf and
                 | progress destruct_head_hnf or
                 | progress split_iff
                 | match goal with H : List.In _ (_ ++ _) |- _ => apply in_app_or in H end
                 | apply in_or_app
                 | progress unfold Ensembles.In in *
                 | left; unfold Ensembles.In in *; solve [ eauto ]
                 | right; unfold Ensembles.In in *; solve [ eauto ] ].
  Qed.

  Lemma Same_set_ELE {T} (S1 S2 : Ensemble T) (x : list T)
        (H : Same_set T S1 S2)
  : EnsembleListEquivalence S1 x <-> EnsembleListEquivalence S2 x.
  Proof.
    intros; split; intros; eapply EnsembleListEquivalence_Same_set; try eassumption.
    destruct_head_hnf and; split; assumption.
  Qed.

  Lemma filter_fold_right {A} (f : A -> bool) (ls : list A)
  : List.filter f ls = List.fold_right (fun x xs => if f x then x::xs else xs) nil ls.
  Proof.
    induction ls; trivial.
  Qed.

  Lemma list_filter_pred_In {T} P (ls : list T) v
  : computes_to (list_filter_pred P ls) v
    -> forall x, List.In x v -> List.In x ls.
  Proof.
    revert v; induction ls; simpl; intros.
    { inversion_by computes_to_inv; subst; simpl in *; trivial. }
    { repeat match goal with
               | [ H : computes_to (Bind _ _) _ |- _ ] => apply computes_to_inv in H
               | [ H : computes_to (ret _) _ |- _ ] => apply computes_to_inv in H
               | _ => progress destruct_head ex
               | _ => progress destruct_head and
               | _ => progress inversion_by computes_to_inv
               | _ => progress subst
               | _ => progress destruct_head bool
               | _ => progress destruct_head or
               | _ => progress split_iff
               | [ H : true = true -> _ |- _ ] => specialize (H eq_refl)
               | _ => left; reflexivity
               | _ => right; solve [ eauto ]
             end. }
  Qed.

  Lemma list_filter_pred_In_iff {T} P (ls : list T) v
  : computes_to (list_filter_pred P ls) v
    -> forall x, List.In x v <-> (List.In x ls /\ P x).
  Proof.
    revert v; induction ls;
    repeat match goal with
             | _ => intro
             | [ |- _ <-> _ ] => split
             | [ |- _ /\ _ ] => split
             | _ => progress simpl in *
             | _ => progress destruct_head False
             | [ H : computes_to (Bind _ _) _ |- _ ] => apply computes_to_inv in H
             | [ H : computes_to (ret _) _ |- _ ] => apply computes_to_inv in H
             | _ => progress destruct_head ex
             | _ => progress destruct_head and
             | _ => progress inversion_by computes_to_inv
             | _ => progress subst
             | _ => progress destruct_head bool
             | _ => progress destruct_head or
             | _ => progress split_iff
             | [ H : true = true -> _ |- _ ] => specialize (H eq_refl)
             | _ => left; reflexivity
             | _ => right; solve [ eauto ]
             | _ => solve [ eauto ]
             | _ => intuition congruence
           end.
  Qed.

  Lemma refine_ELE_filter_by_and {T} (P : T -> Prop) (S0 : Ensemble T)
  : refine {ls : list T
           | EnsembleListEquivalence
               (fun x : T =>
                  Ensembles.In T S0 x /\ P x)
               ls }
           (filter_pred P S0).
  Proof.
    unfold filter_pred, fold_right, to_list;
    repeat intro;
    try inversion_by computes_to_inv.
    repeat match goal with
             | _ => intro
             | [ H : computes_to (Bind _ _) _ |- _ ] => apply computes_to_inv in H
             | _ => progress destruct_head ex
             | _ => progress destruct_head_hnf and
             | _ => progress split_iff
             | _ => progress inversion_by computes_to_inv
             | [ |- computes_to (Pick _) _ ] => constructor
             | [ |- EnsembleListEquivalence _ _ ] => split
           end.
    { match goal with
        | [ H : NoDup ?ls, H' : computes_to (List.fold_right _ _ _) ?v |- _ ]
          => revert H H'; clear; intros H H';
             generalize dependent v; induction ls
      end;
      repeat match goal with
               | _ => intro
               | _ => progress subst
               | _ => progress simpl in *
               | [ H : computes_to (Bind _ _) _ |- _ ] => apply computes_to_inv in H
               | [ H : computes_to (ret _) _ |- _ ] => apply computes_to_inv in H
               | _ => progress destruct_head ex
               | _ => progress destruct_head_hnf and
               | _ => progress destruct_head_hnf bool
               | _ => progress split_iff
               | _ => progress inversion_by computes_to_inv
               | [ |- computes_to (Pick _) _ ] => constructor
               | [ |- EnsembleListEquivalence _ _ ] => split
               | [ |- NoDup nil ] => constructor
               | [ |- NoDup (_::_) ] => constructor
               | [ H : NoDup (_::_) |- _ ] => inversion H; clear H
               | [ H : ?T -> ?U, H' : ?T |- _ ] => specialize (H H')
               | [ IH : forall v, computes_to (List.fold_right _ _ _) v -> _,
                     H : computes_to (List.fold_right _ _ _) _ |- _ ]
                 => pose proof (@list_filter_pred_In _ _ _ _ H);
                   apply IH in H;
                   clear IH
               | [ H : true = true -> _ |- _ ] => specialize (H eq_refl)
               | _ => solve [ eauto ]
             end. }
    { unfold Ensembles.In in *.
      let H := match goal with H : computes_to _ _ |- _ => constr:(H) end in
      rewrite (@list_filter_pred_In_iff _ _ _ _ H).
      intuition. }
  Qed.

  Lemma bool_true_iff_beq_pick (b1 b2 b3 : bool)
  : refineEquiv { b0 : bool | b0 = b1 <-> b2 = b3 }
                (ret (if b1
                      then if b3
                           then b2
                           else negb b2
                      else if b3
                           then negb b2
                           else b2)).
  Proof.
    setoid_rewrite bool_true_iff_beq.
    rewrite refineEquiv_pick_eq.
    reflexivity.
  Qed.

  Lemma bool_true_iff_bneq_pick (b1 b2 b3 : bool)
  : refineEquiv { b0 : bool | b0 = b1 <-> b2 <> b3 }
                (ret (if b1
                      then if b3
                           then negb b2
                           else b2
                      else if b3
                           then b2
                           else negb b2)).
  Proof.
    setoid_rewrite bool_true_iff_bneq.
    rewrite refineEquiv_pick_eq.
    reflexivity.
  Qed.

  Lemma bool_true_iff_bnneq_pick (b1 b2 b3 : bool)
  : refineEquiv { b0 : bool | b0 = b1 <-> ~b2 <> b3 }
                (ret (if b1
                      then if b3
                           then b2
                           else negb b2
                      else if b3
                           then negb b2
                           else b2)).
  Proof.
    setoid_rewrite bool_true_iff_bnneq.
    rewrite refineEquiv_pick_eq.
    reflexivity.
  Qed.

  Global Add Parametric Morphism {A} : (@EnsembleListEquivalence A)
      with signature Same_set _ ==> eq ==> impl
        as impl_EnsembleListEquivalence_mor.
  Proof.
    repeat intro.
    eapply EnsembleListEquivalence_Same_set; eassumption.
  Qed.

  Global Add Parametric Morphism {A} : (@EnsembleListEquivalence A)
      with signature Same_set _ ==> eq ==> iff
        as iff_EnsembleListEquivalence_mor.
  Proof.
    repeat intro; split; intro;
    eapply EnsembleListEquivalence_Same_set; first [ eassumption | symmetry; eassumption ].
  Qed.

  Lemma Same_set_Setminus_fold {A} S0 ls
  : Same_set _
             (Setminus A S0 (elements ls))
             (List.fold_right (fun x S => Subtract _ S x) S0 ls).
  Proof.
    revert S0; induction ls; simpl;
    repeat match goal with
             | _ => intro
             | _ => split
             | _ => progress subst
             | _ => progress split_and
             | _ => progress destruct_head_hnf and
             | _ => progress destruct_head_hnf or
             | _ => progress destruct_head_hnf Singleton
             | _ => progress unfold Ensembles.In, elements, Same_set, Included, Setminus, not in *
             | _ => progress simpl in *
             | [ H : ~(_ \/ _) |- _ ] => apply Decidable.not_or in H
             | _ => solve [ eauto ]
             | [ H : _ |- _ ] => apply H; solve [ eauto ]
             | [ H : Singleton _ ?x ?x -> False |- _ ] => exfalso; apply H
           end.
  Qed.

  Local Ltac to_list_mor_t :=
    repeat match goal with
             | _ => progress unfold Included, Ensembles.In, to_list in *
             | _ => intro
             | _ => progress inversion_by computes_to_inv
             | [ |- computes_to (Pick _) _ ] => constructor
             | [ |- refineEquiv _ _ ] => split
             | _ => eapply EnsembleListEquivalence_Same_set; first [ eassumption | symmetry; eassumption ]
           end.
  Global Add Parametric Morphism {A} : (@to_list A)
    with signature Same_set _ ==> refine
      as refine_to_list_Included_mor.
  Proof. to_list_mor_t. Qed.

  Global Add Parametric Morphism {A} : (@to_list A)
    with signature Same_set _ ==> refineEquiv
      as refineEquiv_to_list_Included_mor.
  Proof. to_list_mor_t. Qed.

  Lemma In_check_impl (S0 : Ensemble W) {T} (f : (W -> Prop) -> Comp T)
        `{fR : Proper _ (respectful (pointwise_relation _ iff) refine) f}
  : refine (f (Ensembles.In _ S0))
           (ls <- to_list S0;
            let fs_S0 := FiniteSetOfList ls in
            (f (fun x =>
                  (snd (CallMethod (projT1 FiniteSetImpl) sIn fs_S0 x) : bool)
                  = true))).
  Proof.
    intros v H'.
    apply computes_to_inv in H'.
    destruct H' as [ls [Hls H']].
    revert v H'.
    hnf in fR.
    apply fR; clear fR.
    unfold to_list in *.
    inversion_by computes_to_inv.
    intro.
    handle_calls_then' ltac:(fun H =>
                               first [ specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfListOfFiniteSetAndListOfList _))
                                     | specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfList _)) ]);
      inversion_by computes_to_inv.
    repeat match goal with
             | _ => progress subst
             | _ => progress simpl in *
             | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
             | [ H : (_, _) = ?x |- context[?x] ] => destruct x
           end.
    rewrite EnsembleOfList_In in *.
    match goal with
      | [ H : ?T <-> _ |- _ <-> ?T ] => rewrite H; clear H
    end.
    destruct_head_hnf and; auto.
  Qed.

  Global Instance
  : Proper (pointwise_relation W iff ==> refine)
           (fun P : W -> Prop =>
              FunctionOfList
                (fun (a : W) (b' : Comp (list W)) =>
                   xs <- b';
                 b <- {b : bool | b = true <-> P a};
                 ret (if b then a :: xs else xs)) b0 ls).
  Proof.
    intros; hnf; simpl; intros.
    apply (@refine_FunctionOfList_mor1); auto.
    repeat (simpl in * || intro).
    unfold pointwise_relation in *.
    setoid_rewrite_hyp.
    assumption.
  Qed.

  Global Instance
  : Proper (pointwise_relation W iff ==> refine)
           (fun P : W -> Prop =>
              FunctionOfList
                (fun (a : W) (b' : Comp (list W)) =>
                   xs <- b';
                 b <- {b : bool | b = true <-> ~ P a};
                 ret (if b then a :: xs else xs)) b0 ls).
  Proof.
    intros; hnf; simpl; intros.
    apply (@refine_FunctionOfList_mor1); auto.
    repeat (simpl in * || intro).
    unfold pointwise_relation in *.
    setoid_rewrite_hyp.
    assumption.
  Qed.

  Local Ltac FunctionOfList_pick_t S0 :=
    let fS0 := match goal with |- refine ?fS0 _ => constr:(fS0) end in
    let f := (match eval pattern (Ensembles.In _ S0) in fS0 with
                | ?f _ => constr:(f)
              end) in
    rewrite (@In_check_impl S0 _ f); [ | exact _ ];
    repeat match goal with
             | _ => reflexivity
             | _ => progress simpl
             | _ => progress intros
             | [ |- refine (Bind ?c _) (Bind ?c _) ] => apply refine_bind; [ reflexivity | ]
             | [ |- pointwise_relation _ _ _ _ ] => intro
             | [ |- refine (FunctionOfList _ ?b ?ls) (FunctionOfList _ ?b ?ls) ] => apply (@refine_FunctionOfList_mor1); auto
             | [ |- respectful _ _ _ _ ] => intro
             | [ H : refine _ _ |- _ ] => setoid_rewrite H; clear H
             | _ => setoid_rewrite bool_true_iff_bneq
             | _ => setoid_rewrite bool_true_iff_beq
             | _ => rewrite refineEquiv_pick_eq
             | _ => progress autorewrite with refine_monad
           end.

  Lemma FunctionOfList_pick_not_in b0 ls S0
  : refine (FunctionOfList
              (fun (a : W) (b' : Comp (list W)) =>
                 xs <- b';
               b <- {b : bool | b = true <-> ~ Ensembles.In W S0 a};
               ret (if b then a :: xs else xs)) b0 ls)
           (ls' <- to_list S0;
            let fs_S0 := FiniteSetOfList ls' in
            FunctionOfList
              (fun (a : W) (b' : Comp (list W)) =>
                 (xs <- b';
                  ret (if negb (snd (CallMethod (projT1 FiniteSetImpl) sIn fs_S0 a) : bool)
                       then a :: xs
                       else xs))) b0 ls).
  Proof. FunctionOfList_pick_t S0. Qed.

  Lemma FunctionOfList_pick_in b0 ls S0
  : refine (FunctionOfList
              (fun (a : W) (b' : Comp (list W)) =>
                 xs <- b';
               b <- {b : bool | b = true <-> Ensembles.In W S0 a};
               ret (if b then a :: xs else xs)) b0 ls)
           (ls' <- to_list S0;
            let fs_S0 := FiniteSetOfList ls' in
            FunctionOfList
              (fun (a : W) (b' : Comp (list W)) =>
                 (xs <- b';
                  ret (if (snd (CallMethod (projT1 FiniteSetImpl) sIn fs_S0 a) : bool)
                       then a :: xs
                       else xs))) b0 ls).
  Proof. FunctionOfList_pick_t S0. Qed.

  Local Ltac handle_calls'' :=
    handle_calls_then' ltac:(fun H =>
                               first [ specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfListOfFiniteSetAndListOfList _))
                                     | specialize (H _ (AbsR_EnsembleOfList_FiniteSetOfList _)) ]);
    inversion_by computes_to_inv;
    repeat match goal with
             | _ => intro
             | _ => progress subst
             | _ => progress simpl in *
             | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
             | [ H : (_, _) = ?x |- context[?x] ] => destruct x
           end.

  Lemma EnsembleListEquivalence_Intersection_Singleton
        (x : W) (S0 : Ensemble W)
  : refine { ls' : _ | EnsembleListEquivalence (Intersection W (Singleton _ x) S0) ls' }
           (ls_S0 <- to_list S0;
            let fs_S0 := FiniteSetOfList ls_S0 in
            ret (if (snd (CallMethod (projT1 FiniteSetImpl) sIn fs_S0 x) : bool)
                 then x::nil
                 else nil)).
  Proof.
    simpl; unfold to_list; repeat intro; constructor.
    repeat match goal with
             | _ => intro
             | [ H : computes_to (Bind _ _) _ |- _ ] => apply computes_to_inv in H
             | [ H : computes_to (ret _) _ |- _ ] => apply computes_to_inv in H
             | _ => progress destruct_head ex
             | _ => progress destruct_head_hnf and
             | _ => progress destruct_head_hnf bool
             | _ => progress subst
             | _ => progress inversion_by computes_to_inv
             | _ => handle_calls''
             | [ H : _ |- _ ] => rewrite EnsembleOfList_In in H
             | _ => progress destruct_head_hnf and
             | _ => progress destruct_head_hnf or
             | _ => progress destruct_head_hnf bool
             | _ => progress destruct_head_hnf False
             | _ => progress destruct_head_hnf Union
             | _ => progress destruct_head_hnf Intersection
             | _ => progress destruct_head_hnf Singleton
             | _ => progress split_iff
             | _ => progress split_and
             | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
             | [ |- EnsembleListEquivalence _ _ ] => split
             | [ |- NoDup (_::_) ] => constructor
             | [ |- NoDup nil ] => constructor
             | [ |- _ \/ False ] => left
             | [ |- _ <-> _ ] => split
             | _ => reflexivity
             | _ => progress unfold Ensembles.In in *
             | [ |- Intersection _ _ _ _ ] => constructor
             | _ => solve [ eauto ]
             | [ H : ?T -> false = true |- _ ] => assert (T -> False) by (let x := fresh in intro x; specialize (H x); inversion H); clear H
           end.
  Qed.

  Lemma EnsembleListEquivalence_Intersection_Singleton'
        (x : W) (S0 : Ensemble W)
  : refine { ls' : _ | EnsembleListEquivalence (Intersection W S0 (Singleton _ x)) ls' }
           (ls_S0 <- to_list S0;
            let fs_S0 := FiniteSetOfList ls_S0 in
            ret (if (snd (CallMethod (projT1 FiniteSetImpl) sIn fs_S0 x) : bool)
                 then x::nil
                 else nil)).
  Proof.
    setoid_rewrite Intersection_sym.
    apply EnsembleListEquivalence_Intersection_Singleton.
  Qed.


  Lemma In_UniqueFilterOfList f ls x
  : List.In x (UniqueFilterOfList ls f) <-> f x = true /\ List.In x ls.
  Proof.
    unfold UniqueFilterOfList, FunctionOfList; simpl.
    induction ls.
    { simpl; split; tauto. }
    { simpl in *; intros.
      rewrite !NoFunctionJustFiniteSetOfFunction.
      rewrite !NoFiniteSetJustFunctionOfList.
      rewrite !NoFiniteSetJustFunctionOfList in IHls.
      handle_calls''.
      rewrite EnsembleOfList_In in *.
      repeat match goal with
               | [ H : ?T -> ?U, H' : ?T |- _ ] => specialize (H H')
               | [ |- _ <-> _ ] => split
               | [ |- _ /\ _ ] => split
               | _ => intro
               | _ => progress simpl in *
               | _ => progress split_iff
               | _ => progress split_and
               | _ => progress destruct_head bool
               | _ => progress destruct_head_hnf or
               | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
               | _ => progress subst
               | _ => right; assumption
               | [ H : ?x = true, H' : context[?x] |- _ ] => rewrite H in H'
               | [ H : ?x = true |- context[?x] ] => rewrite H
               | [ H : false = true -> _ |- _ ] => clear H
               | [ H : ?T -> false = true |- _ ] => assert (T -> False) by (let t := fresh in intro t; specialize (H t); inversion H); clear H
               | [ |- false = true ] => exfalso
               | [ H : false = true |- _ ] => inversion H
               | _ => tauto
               | [ H : context[if ?E then _ else _] |- _ ] => revert H; case_eq E
               | [ |- context[if ?E then _ else _] ] => case_eq E
             end. }
  Qed.

  Lemma UniqueListOfUniqueFilterOfList f ls
  : UniqueListOfList (UniqueFilterOfList ls f) = UniqueFilterOfList ls f.
  Proof.
    induction ls;
    unfold UniqueListOfList, UniqueFilterOfList, FunctionOfList in *; simpl in *; trivial.
    rewrite !NoFiniteSetJustListOfList in IHls |- *.
    rewrite !NoFiniteSetJustFunctionOfList.
    rewrite !(pull_if UniqueListOfList).
    unfold UniqueListOfList, UniqueFilterOfList, FunctionOfList in *; simpl in *; trivial.
    rewrite !NoFiniteSetJustFilterFunctionOfList in IHls |- *.
    rewrite !NoFunctionJustFiniteSetOfFunction.
    rewrite !NoFiniteSetJustFunctionOfList in IHls |- *.
    rewrite IHls.
    repeat handle_calls''.
    rewrite EnsembleOfList_In in *.
    rewrite In_UniqueFilterOfList in *.
    repeat match goal with
             | [ |- appcontext[if ?E then _ else _] ] => case_eq E
             | _ => intro
             | _ => progress subst
             | _ => reflexivity
             | [ H : ?x = true, H' : context[?x] |- _ ] => rewrite H in H'
             | _ => progress split_iff
             | _ => progress split_and
             | [ H : ?x = ?x /\ _ -> _ |- _ ] => specialize (fun k => H (conj eq_refl k))
             | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
             | [ H : ?T -> ?U, H' : ?T |- _ ] => specialize (H H')
             | _ => congruence
           end.
  Qed.

  Lemma UniuqeListOfList_cons_UniqueFilterOfList a f ls
  : UniqueListOfList (a::UniqueFilterOfList ls f)
    = if negb (andb (snd ((CallMethod (projT1 FiniteSetImpl) sIn) (FiniteSetOfList ls) a) )
                    (f a))
      then a::UniqueFilterOfList ls f
      else UniqueFilterOfList ls f.
  Proof.
    unfold UniqueListOfList, FunctionOfList; simpl.
    rewrite NoFunctionJustFiniteSetOfFunction.
    repeat handle_calls''.
    rewrite EnsembleOfList_In in *.
    rewrite In_UniqueFilterOfList in *.
    rewrite !NoFiniteSetJustListOfList.
    rewrite UniqueListOfUniqueFilterOfList.
    repeat match goal with
             | _ => progress simpl in *
             | _ => progress destruct_head bool
             | _ => progress destruct_head and
             | _ => progress destruct_head False
             | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
             | _ => progress split_iff
             | [ H : ?x = true |- context[?x] ] => rewrite H
             | [ H : ?x = false |- context[?x] ] => rewrite H
             | [ H : ?T -> false = true |- _ ] => assert (T -> False) by (let t := fresh in intro t; specialize (H t); inversion H); clear H
             | _ => reflexivity
             | [ H : false = true -> _ |- _ ] => clear H
             | [ H : _ -> ?x = ?x |- _ ] => clear H
             | [ H : _ /\ ?T -> ?U, H' : ?T |- _ ] => specialize (fun k => H (conj k H'))
             | [ H : ?T -> ?U, H' : ?T |- _ ] => specialize (H H')
             | [ H : _ = true -> False |- _ ] => apply Bool.not_true_is_false in H
           end.
  Qed.

  Lemma EnsembleListEquivalence_Intersection_elements1_fold
        (ls : list W) (S0 : Ensemble W)
  : refine { ls' : _ | EnsembleListEquivalence (Intersection W (elements ls) S0) ls' }
           (ls_S0 <- to_list S0;
            let fs_S0 := FiniteSetOfList ls_S0 in
            ret (UniqueFilterOfList ls (fun x => snd (CallMethod (projT1 FiniteSetImpl) sIn fs_S0 x) : bool))).
  Proof.
    induction ls; simpl.
    { repeat match goal with
               | _ => intro
               | _ => inversion_by computes_to_inv
               | [ H : computes_to (Bind _ _) _ |- _ ] => apply computes_to_inv in H
               | [ H : computes_to (ret _) _ |- _ ] => apply computes_to_inv in H
               | _ => progress destruct_head_hnf ex
               | _ => progress destruct_head_hnf and
               | _ => progress destruct_head_hnf Intersection
               | _ => progress destruct_head_hnf False
               | _ => progress subst
               | [ |- computes_to (Pick _) _ ] => constructor
               | _ => progress unfold to_list in *
               | _ => split
               | _ => progress unfold FunctionOfList, UniqueFilterOfList in *
               | _ => progress simpl in *
               | [ |- NoDup nil ] => constructor
               | _ => solve [ eauto ]
             end. }
    { intros; simpl.
      setoid_rewrite Same_set__elements_cons__Union; simpl.
      setoid_rewrite Same_set_Intersection_Union'.
      rewrite refineEquivUnion;
        [ | let H := fresh in intros ? ? ? H; rewrite H; reflexivity ].
      unfold to_list.
      setoid_rewrite EnsembleListEquivalence_Intersection_Singleton; simpl.
      setoid_rewrite IHls; clear IHls.
      simpl.
      autosetoid_rewrite with refine_monad.
      rewrite refine_bind_dedup.
      apply refine_under_bind; intros.
      inversion_by computes_to_inv.
      unfold UniqueFilterOfList, FunctionOfList; simpl.
      repeat setoid_rewrite NoFunctionJustFiniteSetOfFunction.
      rewrite finite_set_handle_EnsembleListEquivalence;
        rewrite !NoFiniteSetJustListOfList.

      rewrite !NoFiniteSetJustFilterFunctionOfList.
      rewrite if_app; simpl.
      rewrite (pull_if UniqueListOfList).

      rewrite UniuqeListOfList_cons_UniqueFilterOfList.
      rewrite !UniqueListOfUniqueFilterOfList.
      repeat handle_calls''.
      rewrite EnsembleOfList_In in *.
      destruct_head bool; simpl; trivial. }
  Qed.
End FiniteSetHelpers.

Create HintDb finite_sets discriminated.

Hint Unfold to_list fold_right Ensembles.Setminus filter_pred : finite_sets.

Ltac start_FullySharpenedComputation :=
  eexists;
  match goal with
    | [ |- refine ?a ?b ] => let a' := eval hnf in a in change (refine a' b)
  end.

Ltac finish_FullySharpenedComputation :=
  (lazymatch goal with
  | [ |- refine (ret _) (ret _) ] => reflexivity
  | [ |- refine ?x (ret _) ] => fail 1 "Not a fully sharpened computation:" x "A fully sharpened computation consists of a single [ret] applied to some term."
  | [ |- ?G ] => fail 1 "Cannot finish sharpening before it has begun." "Goal" G "is not of the form [refine _ (ret _)]"
   end).

Notation Sharpening x := (refine x (ret _)).

Tactic Notation "begin" "sharpening" "computation" := start_FullySharpenedComputation.

Tactic Notation "finish" "sharpening" "computation" := finish_FullySharpenedComputation.

Ltac finite_set_sharpen_step FiniteSetImpl :=
  first [ progress autorewrite with refine_monad
        | match goal with |- appcontext[Bind (Bind _ _)] => idtac end;
          setoid_rewrite refineEquiv_bind_bind
        | match goal with |- appcontext[Bind (Return _)] => idtac end;
          setoid_rewrite refineEquiv_bind_unit
        | match goal with |- appcontext[Bind _ (Return _)] => idtac end;
          setoid_rewrite refineEquiv_unit_bind
        | idtac;
          (* do an explicit [match] to avoid "Anomaly: Uncaught exception Invalid_argument("decomp_pointwise"). Please report." *)
          match goal with
            | |- appcontext[@FiniteSetADT.cardinal] => idtac
            | |- appcontext[@Ensembles.Cardinal.cardinal] => idtac
          end;
          setoid_rewrite (@finite_set_handle_cardinal FiniteSetImpl)
        | match goal with |- appcontext[@Ensembles.Union] => idtac end;
          setoid_rewrite refineEquivUnion; [ | apply Same_set_ELE ]
        | match goal with |- appcontext[@Ensembles.Complement] => idtac end;
          setoid_rewrite Same_set__Intersection_Complement__Setminus
        | match goal with |- appcontext[@Ensembles.Intersection] => idtac end;
          first [ setoid_rewrite Same_set__Intersection_beq__Setminus
                | setoid_rewrite Same_set__Intersection_bneq__Setminus
                | setoid_rewrite Same_set__Intersection_bnneq__Setminus ]
        (*| match goal with |- appcontext[@Ensembles.Setminus] => idtac end;
          setoid_rewrite Same_set_Setminus_fold*)
        | rewrite filter_fold_right
        | progress rewrite ?NoFiniteSetJustFunctionOfList, ?FunctionIsListOfList, ?NoFiniteSetJustListOfList
        | match goal with |- appcontext[EnsembleListEquivalence (fun x => Ensembles.In _ _ x /\ _)] => idtac end;
          setoid_rewrite refine_ELE_filter_by_and
        | match goal with |- appcontext[@FunctionOfList] => idtac end;
          (** N.B. the [not_in] one must come first, so we combine them; if it doesn't come first, then we end up trying to make a finite set out of the complement of a list, which is impossible *)
          first [ setoid_rewrite (@FunctionOfList_pick_not_in FiniteSetImpl)
                | setoid_rewrite (@FunctionOfList_pick_in FiniteSetImpl) ]
        | match goal with |- appcontext[@FunctionOfList] => idtac end;
          setoid_rewrite (@FunctionOfList_pull_ret FiniteSetImpl)
        | match goal with |- appcontext[@FiniteSetAndFunctionOfList] => idtac end;
          setoid_rewrite (@FiniteSetAndFunctionOfList_pull_ret FiniteSetImpl)
        | match goal with |- appcontext[@Ensembles.Intersection] => idtac end;
          setoid_rewrite (@EnsembleListEquivalence_Intersection_elements1_fold FiniteSetImpl)
        | idtac;
          match goal with |- appcontext[@eq bool] => idtac end;
          first [ setoid_rewrite bool_true_iff_beq_pick
                | setoid_rewrite bool_true_iff_bneq_pick
                | setoid_rewrite bool_true_iff_bnneq_pick ]
        | setoid_rewrite Ensemble_fold_right_simpl
        | setoid_rewrite Ensemble_fold_right_simpl'
        | rewrite (@finite_set_handle_EnsembleListEquivalence FiniteSetImpl)
        | rewrite (@FiniteSetOfListOfFiniteSetAndListOfList FiniteSetImpl)
        | rewrite (@FiniteSetOfUniqueListOfList FiniteSetImpl)
        | rewrite (@fold_right_snd_FiniteSetAndListOfList FiniteSetImpl)
        | rewrite (@fold_right_UniqueListOfList FiniteSetImpl)
        | progress (simpl negb; cbv iota)
        | progress autounfold with finite_sets ].

Tactic Notation "sharpen" "computation" "with" "FiniteSet" "implementation" ":=" constr(FiniteSetImpl) :=
  repeat finite_set_sharpen_step FiniteSetImpl.
