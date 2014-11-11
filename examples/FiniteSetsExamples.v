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
    | [ |- Core.AbsR ?impl ?e (projT1 ?fs) ] => exact (proj2_sig (projT2 fs))
    | _ => solve [ find_label_in_env ]
  end.

(*

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
      to_ensemble _ (fst ((CallMethod (projT1 FiniteSetImpl) sIn) st key))
      = to_ensemble _ st.
  Proof.
    intros.
    assert (is_valid : exists S0, Core.AbsR (projT2 FiniteSetImpl) S0 st) by admit.
    apply Coq.Sets.Ensembles.Extensionality_Ensembles.
    destruct is_valid as [S0 H].
    transitivity S0; [ | symmetry ];
    apply Same_set_ToEnsemble_AbsR; trivial.
    apply AbsR_ToEnsemble_In; trivial.
  Qed.

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
*)
(** And now we do the same for summing. *)

Notation FullySharpenedFacadeProgramOnListReturningWord spec ls
  := (sig (fun p => refine (x <- spec;
                            @Prog _ basic_env True ∅
                                  (["$ret" >sca> x]::∅)
                                  (["$ls" >adt> List ls]::∅)
                                  ∅)
                           (ret p))).

Tactic Notation "begin" "sharpening" "facade" "program" :=
  (lazymatch goal with
  | [ |- sig (fun p => refine (x <- ?spec; @Prog _ _ _ _ _ _ _) (ret p)) ]
    => (let T := match type of spec with Comp ?T => constr:T end in
        let c := fresh in
        evar (c : T);
        let H := fresh in
        assert (H : refine spec (ret c)); subst c;
        [
        | eexists; rewrite H; simplify with monad laws ])
  | [ |- ?G ] => fail "Goal is not about sharpening a facade program." "Goal:" G "is not of the form" "{ p : _ | refine (x <- spec; Prog _ _ _ _ _) (ret p) }"
   end).
  
Lemma compile_FiniteSetAndFunctionOfList_SCA (FiniteSetImpl : FullySharpened FiniteSetSpec)
      f (x : W) ls
      tis_empty thead vadt flistrev flistempty flistpop fsetempty fsetdelete
      {vret}
      {env}
      {vls} (vdiscard: StringMap.key)
      init_knowledge
      init_scas init_adts
:
  GLabelMap.find (elt:=FuncSpec ADTValue) flistrev env = Some (Axiomatic List_rev) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) flistempty env = Some (Axiomatic List_empty) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) flistpop env = Some (Axiomatic List_pop) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) fsetempty env = Some (Axiomatic FEnsemble_sEmpty) ->
  GLabelMap.find (elt:=FuncSpec ADTValue) fsetdelete env = Some (Axiomatic FEnsemble_sDelete) ->
  vret <> vadt ->
  vret <> vls ->
  vret <> tis_empty ->
  vadt <> vls ->
  vadt <> tis_empty ->
  thead <> vret ->
  thead <> vadt ->
  thead <> vls ->
  vls <> vret ->
  tis_empty <> vls ->
  vls <> vdiscard ->
  ~ StringMap.In vadt init_adts ->
  ~ StringMap.In vret init_adts ->
  ~ StringMap.In thead init_adts ->
  ~ StringMap.In tis_empty init_adts ->
  ~ StringMap.In vdiscard init_adts ->
  ~ StringMap.In vdiscard init_scas ->
  ~ StringMap.In vadt init_scas ->
  ~ StringMap.In vls init_scas ->
  ~ StringMap.In tis_empty init_scas ->
  refine (@Prog _ env init_knowledge
                init_scas ([vret >sca> (snd (FiniteSetAndFunctionOfList FiniteSetImpl f x ls))] :: init_scas)
                ([vls >adt> List ls]::init_adts)
                ([vls >adt> List nil]::init_adts))
         (cloop <- { cloop : Stmt
                    | PairLoopBodyOk
                        basic_env
                        (fun xs_acc w =>
                           ValidFiniteSetAndFunctionOfList_body
                             FiniteSetImpl
                              f
                             w
                             xs_acc)
                        cloop init_knowledge init_scas init_adts vls vret vadt thead tis_empty snd
                        (fun xs_acc =>
                           FEnsemble (to_ensemble FiniteSetImpl (projT1 (fst xs_acc)))) };
          ret
            (Fold thead tis_empty vls flistpop flistempty cloop)%facade).
Proof.
  intros.
  rewrite FiniteSetAndFunctionOfList_ValidFiniteSetAndFunctionOfList.
  unfold ValidFiniteSetAndFunctionOfList.
  rewrite <- (@rev_involutive _ ls).
  rewrite !fold_left_rev_right.
  rewrite -> (@rev_involutive _ ls).
  simpl.
  
  rewrite (compile_pair_sca vadt (fun x => FEnsemble (to_ensemble _ (projT1 (fst x))))); vacuum.

  rewrite (fun b => @compile_list_rev_general env flistrev vdiscard vls b _ _ _); try first [ eassumption | rewrite add_add_add'; reflexivity | vacuum ].

  rewrite add_add_add'.
  setoid_rewrite (compile_fold_pair env _ snd (fun x => FEnsemble (to_ensemble _ (projT1 (fst x)))) vls vret vadt thead tis_empty flistpop flistempty); try first [ eassumption | solve [map_iff_solve intuition] | vacuum ].

  simpl; rewrite General.refine_under_bind.

  Focus 2.
  intros.
  rewrite compile_constant; vacuum.
  rewrite compile_AbsImpl_sEmpty; first [ eassumption | solve [map_iff_solve eauto] | vacuum ]. 
  rewrite compile_AbsImpl_sDelete; try first [ eassumption | solve [map_iff_solve eauto] | vacuum ].
Admitted.

Lemma eq_ToEnsemble_In (FiniteSetImpl: FullySharpened FiniteSetSpec)
      (st : { st : _ & { S0 : _ | Core.AbsR (projT2 FiniteSetImpl) S0 st }%type})
      key
: to_ensemble _ (fst ((CallMethod (projT1 FiniteSetImpl) sIn) (projT1 st) key))
  = to_ensemble _ (projT1 st).
Proof.
  intros.
  apply Coq.Sets.Ensembles.Extensionality_Ensembles.
  destruct st as [st [S0 H]].
  transitivity S0; [ | symmetry ];
  apply Same_set_ToEnsemble_AbsR; trivial.
  apply AbsR_ToEnsemble_In; trivial.
Qed.

Lemma compile_list_delete_no_return
      (vret : StringMap.key)
      (env : GLabelMap.t (FuncSpec ADTValue))
      (f : GLabelMap.key) (vseq : StringMap.key)
      (seq : list Memory.W) (knowledge : Prop)
      (scas adts : StringMap.t (Value ADTValue))
: GLabelMap.find (elt:=FuncSpec ADTValue) f env =
  Some (Axiomatic List_delete) ->
  ~ StringMap.In (elt:=Value ADTValue) vret adts ->
  ~ StringMap.In (elt:=Value ADTValue) vseq scas ->
  ~ StringMap.In (elt:=Value ADTValue) vret scas ->
  vret <> vseq ->
  refine
    (Prog (env := env) knowledge scas scas ([vseq >> ADT (List seq)]::adts) adts)
    (Return (Call vret f (cons vseq nil))).
Proof.
  intros.
  (* Same as compile_list_delete_no_ret ?*)
Admitted.


Ltac new_variable_name base :=
  let base' := (eval compute in base) in
  (lazymatch goal with
  | [ |- context[base'] ] => new_variable_name (base' ++ "'")
  | _ => constr:base'
   end).

Ltac get_first_comp_from G :=
  (lazymatch G with
  | refine (prog <- ?c; _) _ => constr:c
  | refine ?c _ => constr:c
   end).

Ltac get_pre_post_scas_adts_from G :=
  let G' := get_first_comp_from G in
  (lazymatch G' with
  | { prog : _ | ProgOk prog _ ?prescas ?postscas ?preadts ?postadts }%comp => constr:((prescas, postscas, preadts, postadts))
  | Prog _ ?prescas ?postscas ?preadts ?postadts => constr:((prescas, postscas, preadts, postadts))
   end).
Ltac get_pre_post_scas_adts_from_goal :=
  let G := match goal with |- ?G => constr:G end in
  get_pre_post_scas_adts_from G.

Ltac string_map_t_in key value map :=
  match map with
    | ∅ => constr:false
    | [ key >> value ]::_ => constr:true
    | [ key >> _ ]::_ => constr:false
    | [ _ >> _ ]::?map' => string_map_t_in key value map'
  end.

Ltac string_map_t_get_key_of_value_in value map :=
  match map with
    | [ ?key >> value ]::_ => constr:key
    | [ _ >> _ ]::?map' => string_map_t_get_key_of_value_in value map'
  end.

Ltac string_map_t_get_key_of_sca_value_in value map :=
  match map with
    | [ ?key >sca> value ]::_ => constr:key
    | [ _ >> _ ]::?map' => string_map_t_get_key_of_sca_value_in value map'
  end.

(** Note: this gives the wrong answer if [smaller] syntactically
      maps the same key to two difference values *)
Ltac string_map_t_subset smaller larger :=
  match smaller with
    | ∅ => constr:true
    | [ ?key >> ?value ]::?smaller'
      => match string_map_t_in key value larger with
           | true => string_map_t_subset smaller' larger
           | false => constr:false
         end
  end.

Ltac solve_SomeSCAs :=
  solve [ (lazymatch goal with
          | [ |- SomeSCAs _ _ ]
            => hnf; intros * ;
           StringMapFacts.map_iff;
           repeat match goal with
                    | _ => assumption
                    | _ => intro
                    | _ => progress destruct_head or
                    | _ => progress destruct_head and
                    | _ => progress subst
                    | _ => progress map_iff_solve' idtac
                  end
           end) ].



(*Ltac get_post_prog_and_var_from G :=
  (lazymatch G with
  | refine (prog <- { prog : _ | ProgOk prog _ _ ([?var >> SCA _ ?p]::_) _ _ }; _) _ => constr:((var, p))
  | refine ({ prog : _ | ProgOk prog _ _ ([?var >> SCA _ ?p]::_) _ _ }) _ => constr:((var, p))
   end).
Ltac get_post_prog_and_var_in_goal :=
  let G := match goal with |- ?G => constr:G end in
  get_post_prog_and_var_from G.

Ltac get_post_adt_and_var_from G :=
  (lazymatch G with
  | refine (prog <- { prog : _ | ProgOk prog _ _ _ _ ([?var >> ADT ?p]::_) }; _) _ => constr:((var, p))
  | refine ({ prog : _ | ProgOk prog _ _ _ _ ([?var >> ADT ?p]::_) }) _ => constr:((var, p))
   end).

Ltac get_post_adt_and_var_in_goal :=
  let G := match goal with |- ?G => constr:G end in
  get_post_adt_and_var_from G.



Ltac get_pre_prog_and_var_from G :=
  (lazymatch G with
  | refine (prog <- { prog : _ | ProgOk prog _ ([?var >> SCA _ ?p]::_) _ _ _ }; _) _ => constr:((var, p))
  | refine ({ prog : _ | ProgOk prog _ ([?var >> SCA _ ?p]::_) _ }) _ _ _ => constr:((var, p))
   end).
Ltac get_pre_prog_and_var_in_goal :=
  let G := match goal with |- ?G => constr:G end in
  get_pre_prog_and_var_from G.

Ltac get_pre_adt_and_var_from G :=
  (lazymatch G with
  | refine (prog <- { prog : _ | ProgOk prog _ _ _ ([?var >> ADT ?p]::_) _ }; _) _ => constr:((var, p))
  | refine ({ prog : _ | ProgOk prog _ _ _ ([?var >> ADT ?p]::_) _ }) _ => constr:((var, p))
   end).

Ltac get_pre_adt_and_var_in_goal :=
  let G := match goal with |- ?G => constr:G end in
  get_pre_adt_and_var_from G.*)

Ltac guarded_compile_step_same_states :=
  idtac;
  let p := get_pre_post_scas_adts_from_goal in
  (lazymatch p with
  | (?prescas, ?postscas, ?preadts, ?postadts)
    => (test unify prescas postscas;
        test unify preadts postadts;
        setoid_rewrite no_op; vacuum)
   end).

Ltac guarded_compile_if_parallel :=
  idtac;
  let p := get_pre_post_scas_adts_from_goal in
  (lazymatch p with
  | (?prescas, [?svar >sca> if ?test then _ else _]::?postscas,
     ?preadts, [?sadt >adt> FEnsemble (if ?test then _ else _)]::?postadts)
    => (idtac;
        let vcond := new_variable_name "$cond" in
        setoid_rewrite (compile_if_parallel vcond))
   end).

(** N.B. It might be possible to not need [setoid_rewrite] by filling
    in more arguments explicitly to [rewrite].  As it is, we must pass
    [prescas] explicitly to not get error messages about
    meta-variables deep in the βι-normal form of the term. *)
Ltac compile_step_same_adts_handle_first_post_sca :=
  idtac;
  let after_tac := (idtac; vacuum) in
  let p := get_pre_post_scas_adts_from_goal in
  (lazymatch p with
  | (?prescas, [?var >> SCA _ ?prog]::?postscas', ?preadts, ?postadts)
    => (idtac;
        (lazymatch prog with
        | Word.wmult _ _
          => (let t1 := new_variable_name "$t1" in
              let t2 := new_variable_name "$t2" in
              first [ rewrite (@compile_binop_nicer _ _ IL.Times var t1 t2 _ _ _ prescas)
                    | setoid_rewrite (@compile_binop_nicer _ _ IL.Times var t1 t2 _ _ _ prescas) ]; after_tac)
        | Word.wplus _ _
          => (let t1 := new_variable_name "$t1" in
              let t2 := new_variable_name "$t2" in
              first [ rewrite (@compile_binop_nicer _ _ IL.Plus var t1 t2 _ _ _ prescas)
                    | setoid_rewrite (@compile_binop_nicer _ _ IL.Plus var t1 t2 _ _ _ prescas) ]; after_tac)
        | Word.wminus _ _
          => (let t1 := new_variable_name "$t1" in
              let t2 := new_variable_name "$t2" in
              first [ rewrite (@compile_binop_nicer _ _ IL.Minus var t1 t2 _ _ _ prescas)
                    | setoid_rewrite (@compile_binop_nicer _ _ IL.Minus var t1 t2 _ _ _ prescas) ]; after_tac)
        | nat_as_word _
          => (first [ rewrite (compile_constant var)
                    | setoid_rewrite (compile_constant var) ]; after_tac)
        | FunctionOfList _ _ _ _ => unfold FunctionOfList
        | snd (@FiniteSetAndFunctionOfList ?impl W ?f ?x ?ls)
          => (let tis_empty := new_variable_name "$is_empty" in
              let thead     := new_variable_name "$head" in
              let vadt      := new_variable_name "$adt" in
              let lem       := constr:(@compile_FiniteSetAndFunctionOfList_SCA impl f x ls tis_empty thead vadt var) in
              first [ rewrite lem
                    | setoid_rewrite lem ])
        | if _ then _ else _
          => (let vcond := new_variable_name "$cond" in
              setoid_rewrite (compile_if_parallel vcond); try after_tac)
        | BoolToW (snd ((CallMethod (projT1 ?impl) sIn) ?r ?w'))
          => (setoid_rewrite (compile_sIn _ _ _ "TODO REMOVE"); try after_tac)
        | _ (** catch-all case; we look for the value in [prescas] *)
          => let key := string_map_t_get_key_of_sca_value_in prog prescas in
             rewrite (@copy_word _ _ key var); [ | solve [ vacuum ]..]
         end))
   end).

Ltac guarded_compile_step_same_adts :=
  idtac;
  let after_tac := (idtac; vacuum) in
  let p := get_pre_post_scas_adts_from_goal in
  (lazymatch p with
  | (?prescas, ?postscas, ?preadts, ?postadts)
    => (not unify prescas postscas;
        test unify preadts postadts;
        (lazymatch string_map_t_subset postscas prescas with
        | true
          => ((** [postscas] is a subset of [prescas] *)
            first [ rewrite (@drop_scas_from_precond _ _ _ prescas postscas postscas)
                  | setoid_rewrite (@drop_scas_from_precond _ _ _ prescas postscas postscas) ];
            [
            | solve_SomeSCAs ])
        | false
          => compile_step_same_adts_handle_first_post_sca
         end))
   end).

Ltac guarded_compile_step_same_scas :=
  idtac;
  let after_tac := (idtac; vacuum) in
  let p := get_pre_post_scas_adts_from_goal in
  (lazymatch p with
  | (?prescas, ?postscas, ?preadts, ?postadts)
    => (test unify prescas postscas;
        not unify preadts postadts;
        (lazymatch constr:((preadts, postadts)) with
        | ([ ?var >adt> List ?val ]::postadts, _)
          => (let vret := new_variable_name "$dummy_ret" in
              rewrite (@compile_list_delete_no_return vret); try reflexivity)
        | ([ ?var >adt> FEnsemble (to_ensemble ?impl ?fs)]::?rest,
           [ ?var >adt> FEnsemble (to_ensemble ?impl (fst ((CallMethod (projT1 ?impl) sAdd) ?fs ?head)))]::?rest')
          => (let dummy := new_variable_name "$dummy_ret" in
              setoid_rewrite (@compile_sAdd_better dummy))
         end))
   end).

Ltac guarded_compile_step_different_adts_different_scas :=
  idtac;
  let p := get_pre_post_scas_adts_from_goal in
  (lazymatch p with
  | (?prescas, ?postscas, ?preadts, ?postadts)
    => (not unify prescas postscas;
        not unify preadts postadts;
        setoid_rewrite compile_add_intermediate_scas_with_ret;
        setoid_rewrite compile_add_intermediate_adts; vacuum (** split into scalars and adts *))
   end).

Ltac compile_step :=
  first [ progress change (Word.word 32) with W
        | progress change AbsImpl with to_ensemble in *
        | progress unfold wplus, wminus in *
        | progress simpl projT1
        | progress simpl proj1_sig
        | ((** Calling "In" always yields something equivalent to the original
       ADT; it's always safe to simplify with this fact. *)
          rewrite !eq_ToEnsemble_In)
        | ((** pull [if]s underneath [FEnsemble]; this is (hopefully?)
              always a good thing to do, and we want to do it
              preemptively, before splitting *)
          progress repeat match goal with
                            | [ |- appcontext[FEnsemble ?E] ]
                              => progress repeat match E with
                                                   | appcontext[?f (if _ then _ else _)]
                                                     => rewrite (pull_if f)
                                                 end
                          end)
        | guarded_compile_if_parallel
        | guarded_compile_step_same_states
        | guarded_compile_step_same_scas
        | guarded_compile_step_same_adts
        | guarded_compile_step_different_adts_different_scas
        | (lazymatch goal with
          | [ |- refine (cloop <- { cloop : Stmt | PairLoopBodyOk _ _ _ _ _ _ _ _ _ _ _ _ _ }; _) (ret _) ]
            => (rewrite pull_forall_loop_pair; vacuum)
          | [ |- refine (ret _) (ret _) ]
            => reflexivity
           end)
        | progress vacuum ].

Tactic Notation "compile" := repeat repeat compile_step.

Tactic Notation "finish" "compiling" := reflexivity.

Definition sumUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W)
: FullySharpenedFacadeProgramOnListReturningWord (sumUniqueSpec ls) ls.
Proof.
  begin sharpening facade program.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  finish sharpening computation.

  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  
  Time compile. (* 47 s *)

  admit.
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
