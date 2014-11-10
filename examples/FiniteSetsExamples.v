(** * Some examples about dealing with finite sets *)
Require Import ADTSynthesis.FiniteSetADTs.

(** Now we spec out two examples, the count of the unique elements in
    a list, and the sum of the unique elements in a list. *)

Definition countUniqueSpec (ls : list W) : Comp W
  := cardinal (elements ls).

Definition countUniqueSpec' (ls : list W) : Comp W
  := (xs <- to_list (elements ls);
      ret (from_nat (List.length xs))).

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
  := to_list (Ensembles.Setminus _ (elements ls) (fun y => wlt y x = false)).

Definition filterLtUniqueSpec2 (ls : list W) (x : W) : Comp (list W)
  := to_list (Ensembles.Intersection _ (elements ls) (Ensembles.Complement _ (fun y => wlt y x = false))).

Definition filterLtUniqueSpec3 (ls : list W) (x : W) : Comp (list W)
  := to_list (Ensembles.Setminus _ (elements ls) (fun y => ~wlt y x = true)).

Definition filterLtUniqueSpec4 (ls : list W) (x : W) : Comp (list W)
  := to_list (Ensembles.Intersection _ (elements ls) (Ensembles.Complement _ (fun y => ~wlt y x = true))).

Definition filterLtUniqueSpec5 (ls : list W) (x : W) : Comp (list W)
  := to_list (Ensembles.Setminus _ (elements ls) (fun y => wlt x y = true)).

Definition filterLtUniqueSpec6 (ls : list W) (x : W) : Comp (list W)
  := to_list (Ensembles.Intersection _ (elements ls) (fun y => wlt y x = true)).

Definition intersectionUniqueSpec (ls1 ls2 : list W) : Comp (list W)
  := to_list (Ensembles.Intersection _ (elements ls1) (elements ls2)).

Definition differenceUniqueSpec (ls1 ls2 : list W) : Comp (list W)
  := to_list (Ensembles.Setminus _ (elements ls1) (elements ls2)).

Definition symmetricDifferenceUniqueSpec (ls1 ls2 : list W) : Comp (list W)
  := to_list (Ensembles.Union
                _
                (Ensembles.Setminus _ (elements ls1) (elements ls2))
                (Ensembles.Setminus _ (elements ls2) (elements ls1))).

Definition countUniqueLessThanSpec1 (ls : list W) (x : W) : Comp W
  := (ls' <- to_list (Ensembles.Setminus _ (elements ls) (fun y => wlt y x = true));
      cardinal (elements ls')).

Definition countUniqueLessThanSpec2 (ls : list W) (x : W) : Comp W
  := (n <- cardinal (elements ls);
      n' <- cardinal (elements (List.filter (fun y => negb (wlt y x)) ls));
      ret (wminus n n')).

Require Import FiatToFacade.Compiler.
Require Import FiatToFacade.FacadeNotations.
Require Import Computation.ApplyMonad.
Require Import GLabelMapFacts.
Require Import List.
Require Import FiniteSetADTs.FiniteSetADTMethodLaws.

Ltac find_label_in_env :=
  unfold basic_env, AddPair, MakePair; simpl;
  try match goal with
        | |- GLabelMap.find ?k (GLabelMap.add ?k' (Axiomatic ?spec) _) = Some (Axiomatic ?spec) =>
          apply P.F.add_eq_o; try reflexivity
        | |- GLabelMap.find ?k (GLabelMap.add ?k' (Axiomatic ?spec) _) = Some (Axiomatic ?spec') =>
          rewrite P.F.add_neq_o; [ find_label_in_env | ]; congruence
      end.

Ltac vacuum :=
  trickle_deletion;
  match goal with
    | [ |- refine _ _ ] => try (simplify with monad laws)
    | [ |- ?a <> ?b ] => first [ is_evar a | is_evar b | discriminate ]
    | [ |- ~ StringMap.In ?k ∅ ] => solve [apply not_in_empty]
    | [ |- ~ StringMap.In ?k ?s ] => first [ is_evar s | solve [map_iff_solve ltac:(intuition discriminate)] ]
    | [ |- context[SCALoopBodyProgCondition] ] => progress (unfold SCALoopBodyProgCondition; intros; simpl)
    | [ |- context[ADTLoopBodyProgCondition] ] => progress (unfold ADTLoopBodyProgCondition; intros; simpl)
    | [ |- context[PairLoopBodyProgCondition] ] => progress (unfold PairLoopBodyProgCondition; intros; simpl)
    | [ |- ?m[?k >> ?v] ] => solve [map_iff_solve_evar intuition]
    | [ |- SomeSCAs _ ∅ ] => solve [apply SomeSCAs_empty]
    | [ |- SomeSCAs _ _ ] => eassumption
    | [ |- AllADTs _ _ ] => eassumption
    | [ |- AllADTs _ _ ] => solve [unfold AllADTs, Superset; intros; map_iff_solve intuition]
    | [ |- Word2Spec ?env _ = Some (Axiomatic _) ] => reflexivity
    | [ |- Label2Word ?env _ = Some _ ] => reflexivity
    | [ |- StringMap.Equal ?a ?b ] => first [ is_evar a | is_evar b | trickle_deletion; reflexivity ]
    | _ => solve [ find_label_in_env ]
  end.


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

  pose (["$ls" >adt> List (rev ls)]::∅) as adts.
  rewrite (start_sca adts "$ret" adts); try vacuum.

  unfold FiniteSetOfList; simpl.
  rewrite <- (@rev_involutive _ ls).
  rewrite !fold_left_rev_right.
  unfold adts.

  Unset Implicit Arguments.
  Lemma prepare_sSize' :
    forall {env knowledge} vens {vret}
           (FiniteSetImpl : FullySharpened FiniteSetSpec)
           (r : Core.Rep (ComputationalADT.LiftcADT (projT1 FiniteSetImpl)))
           (u : fst (ADTSig.MethodDomCod FiniteSetSig ``(sSize))),
    forall init_adts inter_adts inter_adts' final_adts init_scas inter_scas final_scas,
    refine
      (@Prog _ env knowledge
             init_scas ([vret >> SCA _ (snd ((CallMethod (projT1 FiniteSetImpl) sSize) r u))]::final_scas)
             init_adts final_adts)
      (pprep <- (@Prog _ env knowledge
                       init_scas inter_scas
                       init_adts ([vens >adt> FEnsemble (AbsImpl FiniteSetImpl r)]::inter_adts));
       pscas <- (@Prog _ env knowledge
                       inter_scas ([vret >> SCA _ (snd ((CallMethod (projT1 FiniteSetImpl) sSize) r u))]::inter_scas)
                       ([vens >adt> FEnsemble (AbsImpl FiniteSetImpl r)]::inter_adts) inter_adts');
       pclean <- (@Prog _ env knowledge
                        ([vret >> SCA _ (snd ((CallMethod (projT1 FiniteSetImpl) sSize) r u))]::inter_scas)
                        ([vret >> SCA _ (snd ((CallMethod (projT1 FiniteSetImpl) sSize) r u))]::final_scas)
                        inter_adts' final_adts);
       ret (pprep; pscas; pclean)%facade)%comp.
  Proof.
    
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  + repeat (safe_seq; intros); specialize_states; assumption.
  + intros; repeat inversion_facade; specialize_states; intuition.
  Qed.
                         
  rewrite (prepare_sSize' "$ens"); vacuum.

  rewrite (compile_fold_adt _ _ (fun x => (FEnsemble (AbsImpl FiniteSetImpl x))) _ _ "$head" "$is_empty"); vacuum.

  rewrite pull_forall_loop_adt; vacuum.

  rewrite compile_AbsImpl_sEmpty; vacuum.

  rewrite compile_sSize; try vacuum.

  (* Do the two deletions *)

  Focus 6.

  rewrite pull_if_FEnsemble.
  setoid_rewrite (compile_if_adt "$cond").

  setoid_rewrite compile_sIn; try vacuum.

  rewrite drop_sca; vacuum.

  Lemma eq_after_In :
    forall FiniteSetImpl: FullySharpened FiniteSetSpec,
    forall st key,
      to_ensemble _ (fst ((CallMethod (projT1 FiniteSetImpl) sIn) st key)) = to_ensemble _ st.
  Proof.
    (* Using extensionality? *)
  Admitted.

  setoid_rewrite eq_after_In.
  rewrite drop_sca; vacuum.
  rewrite drop_sca; vacuum.
  rewrite no_op; vacuum.

  rewrite drop_sca; vacuum.
  setoid_rewrite compile_add_intermediate_scas; vacuum.
  rewrite (compile_sAdd _ _ "$head" "TODO: REMOVE THIS PARAMETER" "$discard"); try vacuum.
  rewrite drop_sca; vacuum.
  do 2 (rewrite drop_sca; vacuum).
  rewrite no_op; vacuum.
  
Admitted.

  (*
  finish sharpening computation.

Defined.
*)
  
Definition countUniqueImpl' (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (countUniqueSpec' ls).
Proof.
  (** We turn the list into a finite set, then back into a list, and then call [Datatypes.length]. *)
  (** TODO: Do we care about optimizing this further at this stage? *)
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  (* TODO: convert from_nat length to a fold *)
  
  finish sharpening computation.
Defined.

Definition uniqueizeImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedComputation (uniqueizeSpec ls).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.
  etransitivity.

  pose (["$ls" >adt> List (rev ls)]::∅) as adts.
  rewrite (start_adt adts "$ret" List List_inj' adts); try vacuum.

  unfold UniqueListOfList, FunctionOfList, FiniteSetAndFunctionOfList; simpl.
  (* This uses a fold with two ADTs. *)

Admitted.
(*
  finish sharpening computation.
Defined.
*)
  
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

  pose (["$ls" >adt> List (rev ls)]::∅) as adts.
  rewrite (start_sca adts "$ret" adts); vacuum. (* TODO: Why isn't setoid_rewrite working here? *)

  unfold FunctionOfList, FiniteSetAndFunctionOfList.
  rewrite <- (@rev_involutive _ ls).
  rewrite !fold_left_rev_right.
  
  setoid_rewrite (compile_pair_sca "$adt" (fun x => FEnsemble (to_ensemble _ (fst x)))); vacuum.

  unfold adts; simpl.
  rewrite (compile_fold_pair basic_env _ (snd) (fun x => FEnsemble (to_ensemble FiniteSetImpl (fst x))) "$ls" "$ret" "$adt" "$head" "$tis_empty"); vacuum.

  rewrite pull_forall_loop_pair; vacuum.
  rewrite compile_constant; vacuum.
  setoid_rewrite compile_AbsImpl_sEmpty; vacuum.

  (* TODO: Do delete here. *)

  Focus 2.
  rewrite (pull_if_FEnsemble). (* setoid_rewrite without an argument raises an exception here *)
 
  setoid_rewrite (compile_if_parallel "$comp"); vacuum.
  
  setoid_rewrite (compile_sIn _ _ _ "TODO REMOVE"); try vacuum.

  (* True case *)
  rewrite drop_sca; vacuum.
  rewrite compile_scas_then_adts; vacuum.

  (* SCAs *)
  rewrite compile_add_intermediate_scas_with_ret; vacuum.
  rewrite copy_word; vacuum.

  do 3 (rewrite drop_second_sca_from_precond; trickle_deletion).
  rewrite no_op; vacuum.

  (* ADTs *)
  setoid_rewrite eq_after_In.  
  rewrite no_op; vacuum.

  (* False case *)
  rewrite drop_sca; vacuum.
  rewrite compile_scas_then_adts; vacuum.

  (* SCAs *)
  rewrite compile_add_intermediate_scas_with_ret; vacuum.
  setoid_rewrite (compile_binop_simple IL.Plus _ "$head'" "$ret'"); try vacuum.
  rewrite copy_word; vacuum.
  rewrite copy_word; vacuum.

  do 3 (rewrite drop_second_sca_from_precond; trickle_deletion).
  rewrite no_op.

  (* ADTs *)
  (* Note: the cruft around the call to sAdd is pretty generic *)
  setoid_rewrite compile_add_intermediate_scas; vacuum.
  rewrite (compile_sAdd _ _ "$head" "TODO: REMOVE THIS PARAMETER" "$discard"); try vacuum.
  rewrite drop_sca; vacuum.
  rewrite no_op; vacuum.

  reflexivity.

  (* 1,4: ??
     2,3: Lemma needs to be fixed *)
  5: vacuum.
  5: vacuum.

  (* TODO: Check if it wouldn't be better to overwrite everything in the end, instead of overwriting ret immediately. *)
Admitted.

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

Definition filterLtUniqueImpl3 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W) (x : W)
: FullySharpenedComputation (filterLtUniqueSpec3 ls x).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition filterLtUniqueImpl4 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W) (x : W)
: FullySharpenedComputation (filterLtUniqueSpec4 ls x).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition filterLtUniqueImpl5 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W) (x : W)
: FullySharpenedComputation (filterLtUniqueSpec5 ls x).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition filterLtUniqueImpl6 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W) (x : W)
: FullySharpenedComputation (filterLtUniqueSpec6 ls x).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
Defined.

Definition intersectionUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls1 ls2 : list W)
: FullySharpenedComputation (intersectionUniqueSpec ls1 ls2).
Proof.
  begin sharpening computation.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.
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
