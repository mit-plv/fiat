(** * Some examples about dealing with finite sets *)
Require Import ADTSynthesis.FiniteSetADTs.

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

Require Import StringMapNotations.

Require Import StringMap StringMapFacts String.

Require Import FiatToFacade.Utilities.

Require Import Bedrock.Platform.Facade.CompileDFacade.
Require Import CompileUnit.

Require Import Computation.ApplyMonad.
Require Import GLabelMapFacts.
Require Import List.
Require Import FiniteSetADTs.FiniteSetADTMethodLaws.
Require Import FiatToFacade.Compiler.
Require Import FiatToFacade.FacadeNotations.
Require Import FiatToFacade.Compiler.Automation.Vacuum.
Require Import Compiler.Automation.FacadeHelpers.
Require Import Compiler.Automation.SpecializedFolds.
Require Import Memory.

Definition Program_pre :=
  (fun v1 v2 => exists ls w, v1 = ADT (List ls) /\ v2 = SCA ADTValue w).

Definition ProgramOnListReturningWord_post spec :=
  (fun v1 v2 retval => exists ls w wret, v1 = ADT (List ls) /\ v2 = SCA ADTValue w /\
                                         retval = SCA ADTValue wret /\ computes_to (spec ls) wret).

Definition ProgramOnListReturningList_post spec :=
  (fun v1 v2 retval => exists ls w aret, v1 = ADT (List ls) /\ v2 = SCA ADTValue w /\
                                         retval = ADT (List aret) /\ computes_to (spec ls) aret).

Definition ProgramOnListAndWordReturningList_post spec :=
  (fun v1 v2 retval => exists ls w aret, v1 = ADT (List ls) /\ v2 = SCA ADTValue w /\
                                         retval = ADT (List aret) /\ computes_to (spec ls w) aret).

Definition ProgramOnListReturningWord_refinement spec ls retval prog :=
  refine (r <- spec ls;
          p <- (@Prog ADTValue basic_imports_wrapped True
                      ∅ ([retvar >sca> r]::∅)
                      ([argvar1 >adt> List ls]::∅) ∅);
          ret (r, p))
         (ret (retval, prog)).

Definition ProgramOnListReturningList_refinement spec ls retval prog :=
  refine (r <- spec ls;
          p <- (@Prog ADTValue basic_imports_wrapped True
                      ∅ ∅
                      ([argvar1 >adt> List ls]::∅) ([retvar >adt> List r]::∅));
          ret (r, p))
         (ret (retval, prog)).

Definition ProgramOnListAndWordReturningList_refinement spec ls w retval prog :=
  refine (r <- spec ls w;
          p <- (@Prog ADTValue basic_imports_wrapped True
                      ([argvar2 >sca> w]::∅) ∅
                      ([argvar1 >adt> List ls]::∅) ([retvar >adt> List r]::∅));
          ret (r, p))
         (ret (retval, prog)).

Lemma FullySharpenedFacadeProgramOnListAndWordReturningListByRefinements spec Q P :
  (sigT (fun prog =>
           ((forall ls w, exists retval,
              ProgramOnListAndWordReturningList_refinement spec ls w retval prog) /\ Q prog)
           * P prog))%type ->
  (sigT (fun prog => (PairOfConditionsForCompileUnit _ prog
                                                    Program_pre
                                                    (ProgramOnListAndWordReturningList_post spec)
                                                    basic_imports /\ Q prog)
                     * P prog))%type.
Proof.
  unfold PairOfConditionsForCompileUnit, ProgramOnListReturningWord_refinement,
         Program_pre, ProgramOnListReturningWord_post, Prog.
  intros [ prog ([forall_ls] & ?) ].
  exists prog; split; [split; [ | assumption ] | assumption ]; apply two_conds_as_one; intros st v1 v2 map_eq [ls [w (sv1 & sv2)]]; subst;
  cbv delta [StringMapFacts.make_map] in *; simpl in *;
  specialize (forall_ls ls w); destruct forall_ls as [retval refi].

  apply pick_compile_helper in refi.
  destruct refi as (retval_correct & prog_ok); hnf in prog_ok.

  match type of (prog_ok st) with
    | ?a /\ ?b /\ ?c -> _ =>
      assert a by apply I; assert b; assert c;
      try rewrite map_eq; (* TODO: This superseeds the match in other similar lemmas *)
      first [ eapply AllADTs_chomp, add_adts_pop_sca; map_iff_solve intuition
            | eapply add_sca_pop_adts, SomeSCAs_chomp; map_iff_solve intuition; try discriminate
            | apply SomeSCAs_empty
            | specialize_states; split; try solve [ intuition ] ]
  end.

  intros; destruct_pairs; specialize_states.

  exists (ADT (List retval)).
  split; intros; destruct_pairs.

  scas_adts_mapsto;
  unfold StringMapFacts.Submap;
  setoid_rewrite <- StringMapFacts.find_mapsto_iff; intros *;
  map_iff_solve ltac:(intuition; subst; intuition).

  split;
    [ destruct_pairs;
      intros;
      eapply not_in_adts_not_mapsto_adt; eauto;
      try (rewrite StringMapFacts.add_neq_in_iff; eauto);
      try apply not_in_empty
    | repeat eexists; repeat split; first [ reflexivity | eassumption ] ].
Defined.

Lemma FullySharpenedFacadeProgramOnListReturningListByRefinements spec Q P :
  (sigT (fun prog =>
           ((forall ls, exists retval,
              ProgramOnListReturningList_refinement spec ls retval prog) /\ Q prog)
           * P prog))%type ->
  (sigT (fun prog => (PairOfConditionsForCompileUnit _ prog
                                                    Program_pre
                                                    (ProgramOnListReturningList_post spec)
                                                    basic_imports /\ Q prog)
                     * P prog))%type.
Proof.
  unfold PairOfConditionsForCompileUnit, ProgramOnListReturningWord_refinement,
         Program_pre, ProgramOnListReturningWord_post, Prog.
  intros [ prog ([forall_ls] & ?) ].
  exists prog; split; [ split; [ | assumption ] | assumption ]; apply two_conds_as_one; intros st v1 v2 map_eq [ls [w (sv1 & sv2)]]; subst;
  cbv delta [StringMapFacts.make_map] in *; simpl in *;
  specialize (forall_ls ls); destruct forall_ls as [retval refi].

  apply pick_compile_helper in refi.
  destruct refi as (retval_correct & prog_ok); hnf in prog_ok.

  match type of (prog_ok st) with
    | ?a /\ ?b /\ ?c -> _ =>
      assert a by apply I; assert b; assert c;
      try rewrite map_eq;
      first [ eapply AllADTs_chomp, add_adts_pop_sca; map_iff_solve intuition
            | apply SomeSCAs_empty
            | specialize_states; split; try solve [ intuition ] ]
  end.

  intros; destruct_pairs; specialize_states.

  exists (ADT (List retval)).
  split; intros; destruct_pairs.

  scas_adts_mapsto;
  unfold StringMapFacts.Submap;
  setoid_rewrite <- StringMapFacts.find_mapsto_iff; intros *;
  map_iff_solve ltac:(intuition; subst; intuition).

  split;
    [ destruct_pairs;
      intros;
      eapply not_in_adts_not_mapsto_adt; eauto;
      try (rewrite StringMapFacts.add_neq_in_iff; eauto);
      try apply not_in_empty
    | repeat eexists; repeat split; first [ reflexivity | eassumption ] ].
Defined.

Lemma FullySharpenedFacadeProgramOnListReturningWordByRefinements spec Q P :
  (sigT (fun prog =>
           ((forall ls, exists retval,
               ProgramOnListReturningWord_refinement spec ls retval prog) /\ Q prog)
           * P prog))%type ->
  (sigT (fun prog => (PairOfConditionsForCompileUnit _ prog
                                                     Program_pre
                                                     (ProgramOnListReturningWord_post spec)
                                                     basic_imports /\ Q prog)
                     * P prog))%type.
Proof.
  unfold PairOfConditionsForCompileUnit, ProgramOnListReturningWord_refinement,
         Program_pre, ProgramOnListReturningWord_post, Prog.
  intros [ prog ([forall_ls] & ?) ].
  exists prog; split; [ split; [ | assumption ] | assumption ]; apply two_conds_as_one; intros st v1 v2 map_eq [ls [w (sv1 & sv2)]]; subst;
  cbv delta [StringMapFacts.make_map] in *; simpl in *;
  specialize (forall_ls ls); destruct forall_ls as [retval refi].

  apply pick_compile_helper in refi.
  destruct refi as (retval_correct & prog_ok); hnf in prog_ok.

  match type of (prog_ok st) with
    | ?a /\ ?b /\ ?c -> _ =>
      assert a by apply I; assert b; assert c;
      try rewrite map_eq;
      first [ eapply AllADTs_chomp, add_adts_pop_sca; map_iff_solve intuition
            | apply SomeSCAs_empty
            | specialize_states; split; try solve [ intuition ] ]
  end.

  intros; destruct_pairs; specialize_states.

  exists (SCA ADTValue retval).
  split; intros; destruct_pairs.

  scas_adts_mapsto;
  unfold StringMapFacts.Submap;
  setoid_rewrite <- StringMapFacts.find_mapsto_iff; intros *;
  map_iff_solve ltac:(intuition; subst; intuition).

  split;
    [ destruct_pairs;
      intros; eapply not_in_adts_not_mapsto_adt; eauto;
      try apply not_in_empty
    | repeat eexists; repeat split; first [ reflexivity | eassumption ] ].
Defined.

Definition FullySharpenedFacadeProgramOnListReturningList spec :=
  CompileUnit Program_pre (ProgramOnListReturningList_post spec).

Definition FullySharpenedFacadeProgramOnListReturningWord spec :=
  CompileUnit Program_pre (ProgramOnListReturningWord_post spec).

Definition FullySharpenedFacadeProgramOnListAndWordReturningList spec :=
  CompileUnit Program_pre (ProgramOnListAndWordReturningList_post spec).

Record is_disjoint_r x y := {
  IDR_dummy : unit;
  IDR : is_disjoint x y = true
}.

Record is_syntax_ok_r x : Type := {
  ISO_dummy : unit;
  ISO : is_syntax_ok x = true
}.

Lemma CompileUnit_construct av pre_cond post_cond imports:
  (sigT (fun prog =>
           ((PairOfConditionsForCompileUnit av prog pre_cond post_cond imports /\
           (let imported_module_names :=
                                  map (fun x : String.string * String.string * AxiomaticSpec av => fst (fst x))
                                      (GLabelMap.elements imports)
                              in (forallb  (fun x : String.string =>
                                              negb (ListFacts3.string_bool "dfmodule" x))
                                           imported_module_names &&
                                           forallb NameDecoration.is_good_module_name
                                           imported_module_names)%bool = true)) *
            sigT (fun p : is_disjoint_r (assigned prog) (StringSetFacts.of_list argvars) =>
                    sigT (fun q : is_syntax_ok_r prog =>
                            (FModule.is_syntax_ok
                               (compile_op
                                  {|
                                    ArgVars := argvars;
                                    RetVar := "ret";
                                    Body := prog;
                                    args_no_dup := eq_refl;
                                    ret_not_in_args := eq_refl;
                                    DFacade.no_assign_to_args := IDR p;
                                    args_name_ok := eq_refl;
                                    ret_name_ok := eq_refl;
                                    DFacade.syntax_ok := ISO q |}) = true)))))%type ->
   CompileUnit pre_cond post_cond).
Proof.
  destruct 1 as [prog [ ]].
  destruct s as [p [q]].
  destruct p, q.
  destruct a.
  destruct H.
  simpl in *.
  econstructor; eauto.
Defined.

Tactic Notation "begin" "sharpening" "facade" "program" :=
  idtac;
  (lazymatch goal with
     | [ |- FullySharpenedFacadeProgramOnListReturningList ?spec ] =>
       (unfold FullySharpenedFacadeProgramOnListReturningList;
        apply (CompileUnit_construct (imports := basic_imports));
        apply FullySharpenedFacadeProgramOnListReturningListByRefinements;
        econstructor; split; [ split; [ | reflexivity ]; intro; eexists; unfold ProgramOnListReturningList_refinement | ])
     | [ |- FullySharpenedFacadeProgramOnListAndWordReturningList ?spec ] =>
       (unfold FullySharpenedFacadeProgramOnListAndWordReturningList;
        apply (CompileUnit_construct (imports := basic_imports));
        apply FullySharpenedFacadeProgramOnListAndWordReturningListByRefinements;
        econstructor; split; [ split; [ | reflexivity ]; intro; eexists; unfold ProgramOnListAndWordReturningList_refinement | ])
     | [ |- FullySharpenedFacadeProgramOnListReturningWord ?spec ] =>
       (unfold FullySharpenedFacadeProgramOnListReturningWord;
        apply (CompileUnit_construct (imports := basic_imports));
        apply FullySharpenedFacadeProgramOnListReturningWordByRefinements;
        econstructor; split; [ split; [ | reflexivity ]; intro; eexists; unfold ProgramOnListReturningWord_refinement | ])
     | [ |- ?G ] => fail "Goal is not about sharpening a facade program."
                         "Goal:" G "is not of the form" "FullySharpenedFacadeProgramOnListReturning* _"
  end).

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

Ltac string_map_t_key_in key map :=
  match map with
    | ∅ => constr:false
    | [ key >> _ ]::_ => constr:true
    | [ _ >> _ ]::?map' => string_map_t_key_in key map'
    | _ => constr:false (* TODO: this is the evar case *)
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
    | ?other => (* FIXME is_evar other; *) constr:true
  end.

Ltac solve_map_inclusion_step :=
  idtac; match goal with
           | |- ?a = ?a  => reflexivity
           | |- ?a <> ?a => congruence
           | |- ?a = ?b  => congruence
           | _ => eassumption
           | _ => intro
           | _ => progress destruct_head or
           | _ => progress destruct_head and
           | _ => progress subst
           | _ => progress map_iff_solve' idtac
         end. (* FIXME duplicated? *)

Ltac solve_map_inclusion :=
  hnf; intros * ;
  StringMapFacts.map_iff;
  repeat solve_map_inclusion_step.

Ltac solve_map_eq :=
  match goal with
    | |- StringMap.Equal _ _ =>
      apply StringMapFacts.Equal_mapsto_iff;
        intros ? ? ;
        split;
        solve_map_inclusion
  end.

Ltac solve_SomeSCAs :=
  solve [ (lazymatch goal with
          | [ |- SomeSCAs _ _ ]
            => solve_map_inclusion
          end) ].

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

Ltac guarded_compile_if_parallel_adts :=
  idtac;
  let p := get_pre_post_scas_adts_from_goal in
  (lazymatch p with
  | (_, _, _,
     [?vens >adt> FEnsemble (if ?test then _ else _)]
       ::[?vls >adt> List (if ?test then _ else _)]::_)
    => (idtac;
        let vcond := new_variable_name "$cond" in
        setoid_rewrite (compile_if_parallel_adts vcond))
  | (_, _, _,
     [?vls >adt> List (if ?test then _ else _)]
       ::[?vens >adt> FEnsemble (if ?test then _ else _)]::_)
    => (idtac;
        let vcond := new_variable_name "$cond" in
        setoid_rewrite (compile_if_parallel_adts vcond))
   end).

Unset Implicit Arguments.

Lemma compile_fold_right_sca :
  forall {env : GLabelMap.t (FuncSpec ADTValue)}
         (vseq vret thead tis_empty vdiscard: StringMap.key) (fpop fempty frev : GLabelMap.key)
         (loop : W -> W -> W) (knowledge : Prop)
         (scas adts : StringMap.t (Value ADTValue)),
    GLabelMap.find (elt:=FuncSpec ADTValue) fempty env = Some (Axiomatic List_empty) ->
    GLabelMap.find (elt:=FuncSpec ADTValue) fpop env = Some (Axiomatic List_pop) ->
    GLabelMap.find (elt:=FuncSpec ADTValue) frev env = Some (Axiomatic List_rev) ->
    vret <> vseq ->
    vret <> tis_empty ->
    vseq <> vdiscard ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In (elt:=Value ADTValue) tis_empty adts ->
    ~ StringMap.In (elt:=Value ADTValue) tis_empty scas ->
    ~ StringMap.In (elt:=Value ADTValue) thead adts ->
    ~ StringMap.In (elt:=Value ADTValue) vdiscard adts ->
    ~ StringMap.In (elt:=Value ADTValue) vdiscard scas ->
    ~ StringMap.In (elt:=Value ADTValue) vseq scas ->
    forall (seq : list W) (init : W),
      refine
        (@Prog _ env knowledge
               scas ([vret >sca> fold_right loop init seq]::scas)
               ([vseq >> ADT (List seq)]::adts)
               ([vseq >> ADT (List nil)]::adts))
        (cloop <- {cloop : Stmt | SCALoopBodyOk env (fun acc x => loop x acc) cloop knowledge scas adts vseq vret thead tis_empty};
         pinit <- (@Prog _ env knowledge
                         scas ([vret >sca> init]::scas)
                         ([vseq >> ADT (List (rev seq))]::adts)
                         ([vseq >> ADT (List (rev seq))]::adts));
         ret (Seq (Call vdiscard frev (cons vseq nil))
                  (Seq pinit (Fold thead tis_empty vseq fpop fempty cloop)))).
Proof.
  intros.
  erewrite (@compile_list_rev_general _ _ vdiscard vseq seq); first [ eassumption | map_iff_solve intuition ].
  rewrite add_add_add'.
  rewrite <- (rev_involutive seq).
  rewrite fold_left_rev_right.
  rewrite (rev_involutive seq).
  rewrite (@compile_fold_sca _ vseq vret thead tis_empty); eauto.
  simplify with monad laws.

  apply General.refine_under_bind; intros.
  apply General.refine_under_bind; intros.

  reflexivity.
Qed.

Lemma swap_adts :
  forall av env knowl
         scas scas'
         adts adts'
         k v k' v' v'',
    k <> k' ->
    refine (@Prog av env knowl scas scas'
                  ([k >> v]::[k' >> v']::adts) ([k >> v]::[k' >> v'']::adts'))
           (@Prog av env knowl scas scas'
                  ([k' >> v']::[k >> v]::adts) ([k' >> v'']::[k >> v]::adts')).
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.
  rewrite add_add_comm in H5 by assumption.
  specialize_states.

  split; trivial.
  intros; specialize_states; trivial.
  rewrite add_add_comm by assumption.
  intuition.
Qed.


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
              first [ rewrite (@compile_binop_generic _ _ IL.Times var t1 t2 _ _ _ prescas)
                    | setoid_rewrite (@compile_binop_generic _ _ IL.Times var t1 t2 _ _ _ prescas) ]; after_tac)
        | Word.wplus _ _
          => (let t1 := new_variable_name "$t1" in
              let t2 := new_variable_name "$t2" in
              first [ rewrite (@compile_binop_generic _ _ IL.Plus var t1 t2 _ _ _ prescas)
                    | setoid_rewrite (@compile_binop_generic _ _ IL.Plus var t1 t2 _ _ _ prescas) ]; after_tac)
        | Word.wminus _ _
          => (let t1 := new_variable_name "$t1" in
              let t2 := new_variable_name "$t2" in
              first [ rewrite (@compile_binop_generic _ _ IL.Minus var t1 t2 _ _ _ prescas)
                    | setoid_rewrite (@compile_binop_generic _ _ IL.Minus var t1 t2 _ _ _ prescas) ]; after_tac)
        | BoolToW (IL.wltb _ _) (* TODO: make a "generic" version of compile_test *)
          => (let t1 := new_variable_name "$t1" in
              let t2 := new_variable_name "$t2" in
              first [ rewrite (@compile_test_simple _ _ IL.Lt var t1 t2 _ _ _ prescas)
                    | setoid_rewrite (@compile_test_simple _ _ IL.Lt var t1 t2 _ _ _ prescas) ]; after_tac)
        | nat_as_word _
          => (first [ rewrite (compile_constant var)
                    | setoid_rewrite (compile_constant var) ]; after_tac)
        | Word.natToWord _ _
          => (first [ rewrite (compile_constant var)
                    | setoid_rewrite (compile_constant var) ]; after_tac)
        | FunctionOfList _ _ _ _ => unfold FunctionOfList
        | snd (@FiniteSetAndFunctionOfList ?impl Memory.W ?f ?x ?ls)
          => (let tis_empty := new_variable_name "$is_empty" in
              let thead     := new_variable_name "$head" in
              let vadt      := new_variable_name "$adt" in
              let vdiscard  := new_variable_name "$discard" in
              let lem       := constr:(@compile_FiniteSetAndFunctionOfList_SCA impl f x ls tis_empty thead vadt vdiscard var) in
              first [ rewrite lem
                    | setoid_rewrite lem ])
        | fold_right ?loop ?init ?seq
          => (let tis_empty := new_variable_name "$is_empty" in
              let thead     := new_variable_name "$head" in
              let vadt      := new_variable_name "$adt" in
              let vdiscard  := new_variable_name "$discard" in
              let vls       := string_map_t_get_key_of_value_in (ADT (List seq)) preadts in
              first [ rewrite (compile_fold_right_sca vls var thead tis_empty vdiscard)
                    | setoid_rewrite (compile_fold_right_sca vls thead tis_empty vdiscard) ])
        | if _ then _ else _
          => (let vcond := new_variable_name "$cond" in
              setoid_rewrite (compile_if_parallel vcond); try after_tac)
        | BoolToW (snd ((CallMethod (projT1 ?impl) sIn) ?r ?w'))
          => (setoid_rewrite (compile_sIn _ _ _); try after_tac) (* TODO precise these placeholders *)
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

  Unset Implicit Arguments.

Ltac guarded_compile_step_same_scas :=
  idtac;
  let after_tac := (idtac; vacuum) in
  let p := get_pre_post_scas_adts_from_goal in
  (lazymatch p with
  | (?prescas, ?postscas, ?preadts, ?postadts)
    => (test unify prescas postscas;
        not unify preadts postadts;
        (match constr:((preadts, postadts)) with
        | ([?var >adt> List ?val]::postadts, _)
          => (let vret := new_variable_name "$dummy_ret" in
              rewrite (@compile_list_delete_no_ret vret var); try reflexivity)

        | ([?k >adt> ?v]::[?var >adt> List ?val]::?tail, [?k >adt> ?v]::?tail)
          => (let vret := new_variable_name "$dummy_ret" in
              rewrite (@compile_list_delete_no_ret vret var); try reflexivity)

        | ([?vseq >adt> List ?seq]::_, [?vseq >adt> List (?head::?seq)]::_)
          => (let vret := new_variable_name "$dummy_ret" in
              first [ let vhead := string_map_t_get_key_of_sca_value_in head prescas in
                      rewrite (@compile_list_push_generic _ _ vseq vhead vret head seq prescas preadts postadts)
                    | setoid_rewrite (compile_list_push_generic vseq vret head seq) ]; try reflexivity)

        | ([?k >adt> ?v]::[?vseq >adt> List ?seq]::?tail, [?k >adt> ?v]::[?vseq >adt> List (?head::?seq)]::?tail)
          => (let vret := new_variable_name "$dummy_ret" in
              first [ let vhead := string_map_t_get_key_of_sca_value_in head prescas in
                      rewrite (@compile_list_push_generic _ _ vseq vhead vret head seq prescas preadts postadts)
                    | setoid_rewrite (compile_list_push_generic vseq vret head seq) ]; try reflexivity)

        | ([ ?var >adt> FEnsemble (to_ensemble ?impl ?fs)]::?rest,
           [ ?var >adt> FEnsemble (to_ensemble ?impl (fst ((CallMethod (projT1 ?impl) sAdd) ?fs ?head)))]::?rest')
          => (let dummy := new_variable_name "$dummy_ret" in
              setoid_rewrite (@compile_sAdd_no_ret impl dummy _ var))

        | ([?vls >adt> List ?ls]::_,
           [?var >adt> List (snd (FiniteSetAndFunctionOfList ?impl ?f nil ?ls))]::_)
          => (let tis_empty := new_variable_name "$is_empty" in
              let thead     := new_variable_name "$head" in
              let vadt      := new_variable_name "$adt" in
              let vdiscard  := new_variable_name "$discard" in
              let lem       := constr:(@compile_FiniteSetAndFunctionOfList_ADT impl f ls tis_empty thead vadt vdiscard var) in
              first [ rewrite lem
                    | setoid_rewrite lem ])

        | ([?vls >adt> List ?ls]::_,
           [?var >adt> List (fold_right ?f ?init ?ls)]::_)
          => (let tis_empty := new_variable_name "$is_empty" in
              let thead     := new_variable_name "$head" in
              let vadt      := new_variable_name "$adt" in
              let vdiscard  := new_variable_name "$discard" in
              first [ rewrite (compile_fold_right_adt vls var thead tis_empty vdiscard)
                    | setoid_rewrite (compile_fold_right_adt vls var thead tis_empty vdiscard) ])

        | (_, [?vls >adt> List nil]::_)
          => let in_scas := string_map_t_key_in vls prescas in
             let in_adts := string_map_t_key_in vls preadts in
             match constr:((in_scas, in_adts)) with
               | (false, false) => rewrite compile_list_new
               | _ => fail
             end
             (* TODO: This perhaps shouldn't be a lazy match --
                right now it doesn't matter because we're never refining pops *)

        | (_, [?vls >adt> ?wrapper (if ?c then ?t else ?f)]::?finaladts)
          => (let tcond := new_variable_name "$cond" in
              rewrite (@compile_if_adt _ _ tcond vls c))

        | ([?k >> _]::_, [?k >> _]::[?vls >adt> ?wrapper (if ?c then ?t else ?f)]::?finaladts)
          => (rewrite swap_adts) (* Swap to expose the right shape to trigger the clause above.
                                    Could also use the more generic approach found in list_push_generic *)

        | (_, [ ?var >adt> ?val ]::?postadts_tail)
          => (not is_evar postadts_tail;
              rewrite compile_add_intermediate_adts_with_ret)
               (* Introduce an extra step, to deal with the ADTs separately.
                  The evar check prevents a simple infinite loop, but does
                  not guard against all cases. *)
         end))
   end).

Ltac guarded_compile_step_different_adts_different_scas :=
  idtac;
  let p := get_pre_post_scas_adts_from_goal in
  (lazymatch p with
  | (?prescas, ?postscas, ?preadts, ?postadts)
    => (not unify prescas postscas;
        not unify preadts postadts;
        first [setoid_rewrite compile_add_intermediate_scas_with_ret
              |setoid_rewrite compile_add_intermediate_scas];
        setoid_rewrite compile_add_intermediate_adts (** split into scalars and adts *))
   end).

Lemma pull_forall_loop_adt_pair :
  forall  acc_type wsca wadt env b loop knowledge
         scas adts vseq vsca vadt thead tis_empty,
    (forall head acc seq,
       refine  { cloop | @ADTPairLoopBodyProgCondition env acc_type loop cloop knowledge
                                                    scas adts vseq vsca vadt thead tis_empty
                                                    acc wsca wadt head seq } b) ->
    refine { cloop | @ADTPairLoopBodyOk env acc_type loop cloop knowledge
                                     scas adts vseq vsca vadt thead tis_empty wsca wadt }%facade b.
Proof. (* REMOVE *)
  eauto using pull_forall.
Qed.

Ltac compile_step :=
  idtac;
  match goal with
    | |- context[is_disjoint] => fail 1 (* don't waste time is compilation is complete *)
    | |- _ => idtac
  end;
  first [ progress change (Word.word 32) with Memory.W
        | progress change AbsImpl with to_ensemble in *
        | progress unfold wplus, wminus, wlt, wzero, BedrockWordW.W in *
        | progress simpl projT1
        | progress simpl proj1_sig
        | progress unfold UniqueListOfList, FunctionOfList
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
        | guarded_compile_if_parallel_adts
        | guarded_compile_step_same_states
        | guarded_compile_step_same_scas
        | guarded_compile_step_same_adts
        | guarded_compile_step_different_adts_different_scas
        | (lazymatch goal with
          | [ |- refine (cloop <- { cloop : Stmt | PairLoopBodyOk _ _ _ _ _ _ _ _ _ _ _ _ _ }; _) (ret _) ]
            => (rewrite pull_forall_loop_pair; vacuum)
          | [ |- refine (cloop <- { cloop : Stmt | ADTPairLoopBodyOk _ _ _ _ _ _ _ _ _ _ _ _ _ }; _) _ ]
            => (rewrite pull_forall_loop_adt_pair; vacuum)
          | [ |- refine (cloop <- { cloop : Stmt | ADTLoopBodyOk _ _ _ _ _ _ _ _ _ _ _ }; _) _ ]
            => (rewrite pull_forall_loop_adt; vacuum)
          | [ |- refine (cloop <- { cloop : Stmt | SCALoopBodyOk _ _ _ _ _ _ _ _ _ _ }; _) _ ]
            => (rewrite pull_forall_loop_sca; vacuum)
          | [ |- refine (ret _) (ret _) ]
            => reflexivity
           end)
        | progress vacuum ].

Tactic Notation "compile" := repeat repeat compile_step.

Ltac solve_one_using_reflexivity :=
  cbv zeta;
  match goal with
    | |- sigT ?P =>
      match type of P with
        | ?thm -> _ =>
          let proof := fresh in
          assert thm as proof; [ | apply (@existT _ P proof) ]
      end
    | _ => constructor
  end.

Ltac solve_using_reflexivity :=
  repeat solve_one_using_reflexivity.

Tactic Notation "finish" "compiling" := solve_using_reflexivity.

(** Now we spec out two examples, the count of the unique elements in
    a list, and the sum of the unique elements in a list. *)
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

  unfold FiniteSetOfList; simpl.
  rewrite <- (@rev_involutive _ ls).
  rewrite !fold_left_rev_right.
  unfold adts.
Admitted. (*
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

  setoid_rewrite eq_after_In.
  rewrite drop_sca; vacuum.
  rewrite drop_sca; vacuum.
  rewrite no_op; vacuum.

  rewrite drop_sca; vacuum.
  setoid_rewrite compile_add_intermediate_scas; vacuum.
  rewrite (compile_sAdd _ _ "$head" "$discard"); try vacuum.
  rewrite drop_sca; vacuum.
  do 2 (rewrite drop_sca; vacuum).
  rewrite no_op; vacuum.

Admitted.
*)
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
 *)

Definition uniqueizeImpl (FiniteSetImpl : FullySharpened FiniteSetSpec)
: FullySharpenedFacadeProgramOnListReturningList uniqueizeSpec.
Proof.
  begin sharpening facade program.

  unfold uniqueizeSpec. (* FIXME *)
  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  compile.

  finish compiling.
Defined.

(** And now we do the same for summing. *)
Definition sumUniqueImpl (FiniteSetImpl : FullySharpened FiniteSetSpec)
: FullySharpenedFacadeProgramOnListReturningWord sumUniqueSpec.
Proof.
  begin sharpening facade program.

  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  compile.

  finish compiling.
Defined.

Definition sumAllImpl (FiniteSetImpl : FullySharpened FiniteSetSpec)
: FullySharpenedFacadeProgramOnListReturningWord sumAllSpec.
Proof.
  (** We see that the sharpening does the right thing when there's
      nothing to do. *)
  begin sharpening facade program.

  unfold sumAllSpec. (* FIXME *)
  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  Time compile.

  finish compiling.
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


Definition filterLtImpl (FiniteSetImpl : FullySharpened FiniteSetSpec)
: FullySharpenedFacadeProgramOnListAndWordReturningList filterLtSpec.
Proof.
  begin sharpening facade program.

  unfold filterLtSpec. (* FIXME *)
  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  Time compile.

  finish compiling.
Defined.

Definition filterLtUniqueImpl1 (FiniteSetImpl : FullySharpened FiniteSetSpec) (ls : list W) (x : W)
: FullySharpenedFacadeProgramOnListAndWordReturningList filterLtUniqueSpec1.
Proof.
  begin sharpening facade program.

  unfold filterLtUniqueSpec1.
  sharpen computation with FiniteSet implementation := FiniteSetImpl.

  compile.

  finish compiling.
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
