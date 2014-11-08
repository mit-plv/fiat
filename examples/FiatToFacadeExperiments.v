Require Import Facade.FacadeADTs.
Require Import Cito.StringMap.
Require Import AutoDB.

Require Import FiatToFacade.Compiler.Prerequisites.
Require Import FiatToFacade.Compiler.Basics.
Require Import FiatToFacade.Compiler.Constants.
Require Import FiatToFacade.Compiler.Conditionals.
Require Import FiatToFacade.Compiler.Binops.
Require Import FiatToFacade.Compiler.Cleanup.
Require Import FiatToFacade.Compiler.NoOp.
Require Import FiatToFacade.Compiler.ADTs.Folds.

Unset Implicit Arguments.

Definition empty_state {av} : State av := ∅ .

Require Import GLabelMap.

Definition AddPair {av} pair m :=
  @GLabelMap.add (FuncSpec av) (fst pair) (snd pair) m.
Definition MakePair {av} (k: GLabel.glabel) (v: AxiomaticSpec av) := (k, Axiomatic v).

Notation "[[[ p1 ; .. ; pn ]]]" := (AddPair p1 .. (AddPair pn (GLabelMap.empty _)) ..).
Notation "k ↦ v" := (MakePair k v) (at level 55, no associativity).

Definition empty_env {av} := GLabelMap.empty (FuncSpec av).
                                                      
Definition basic_env := [[[ ("List", "empty") ↦ List_empty;
                            ("List", "Pop") ↦ List_pop;
                            ("List", "New") ↦ List_new;
                            ("List", "Push") ↦ List_push;
                            ("List", "Copy") ↦ List_copy;
                            ("List", "Delete") ↦ List_delete ]]].

Definition start_compiling_sca :=
  fun av => @start_compiling' av empty_env empty_state.

Ltac StringMap_remove_add_neq k1 k2 v m :=
  let H := fresh in
  let neq := fresh in
  assert (k2 <> k1) as neq by congruence;
    pose proof (@StringMap_remove_add_neq _ k2 k1 v m neq) as H;
    setoid_rewrite H;
    clear H;
    clear neq.

Ltac StringMap_remove_add_eq k1 k2 v m :=
  let H := fresh in
  let neq := fresh in
  assert (k2 = k1) as neq by congruence;
    pose proof (@StringMap_remove_add_eq _ k2 k1 v m neq) as H;
    setoid_rewrite H;
    clear H;
    clear neq.

Ltac trickle_deletion := (* FIXME: overwrite existing trickle_deletion *)
  repeat
   match goal with
   | |- context [StringMap.remove ?k ([?k' >> ?v]::?m)] => first
     [ StringMap_remove_add_neq k k' v m | StringMap_remove_add_eq k k' v m ]
   | H:context [StringMap.remove ?k ([?k' >> ?v]::?m)]
     |- _ => first
     [ rewrite StringMap_remove_add_eq in H by congruence
     | rewrite StringMap_remove_add_neq in H by congruence ]
   | |- context [StringMap.remove _ ∅] => setoid_rewrite StringMap_remove_empty
   | H:context [StringMap.remove _ ∅] |- _ => rewrite StringMap_remove_empty
   end.

Ltac vacuum :=
  trickle_deletion;
  match goal with
    | [ |- ?a <> ?b ] => first [ is_evar a | is_evar b | discriminate ]
    | [ |- ~ StringMap.In ?k ∅ ] => solve [apply not_in_empty]
    | [ |- ~ StringMap.In ?k ?s ] => first [ is_evar s |
                                             solve [map_iff_solve ltac:(intuition discriminate)] ]
    | [ |- refine _ _ ] => try (simplify with monad laws)
    | [ |- context[SCALoopBodyProgCondition] ] => progress (unfold SCALoopBodyProgCondition; intros)
    | [ |- context[ADTLoopBodyProgCondition] ] => progress (unfold ADTLoopBodyProgCondition; intros)
    | [ |- ?m[?k >> ?v] ] => solve [map_iff_solve_evar intuition]
    | [ |- SomeSCAs _ ∅ ] => solve [apply SomeSCAs_empty]
    | [ |- SomeSCAs _ _ ] => eassumption
    | [ |- AllADTs _ _ ] => eassumption
    | [ |- AllADTs _ _ ] => solve [unfold AllADTs, Superset; intros; map_iff_solve intuition]
    | [ |- Word2Spec ?env _ = Some (Axiomatic _) ] => reflexivity
    | [ |- Label2Word ?env _ = Some _ ] => reflexivity
    | [ |- StringMap.Equal ?a ?b ] => first [ is_evar a | is_evar b | trickle_deletion; reflexivity ]
  end.

Goal forall w1 w2: W, 
     exists x, 
       refine (ret (if Word.weqb w1 w2 then (IL.natToW 3) else (IL.natToW 4))) x.
Proof.
  eexists.

  rewrite (start_compiling_sca False "$ret"); vacuum.
  rewrite (compile_if_sca "$cond"); vacuum.

  setoid_rewrite (compile_test_general IL.Eq "$cond" "$w1" "$w2"); vacuum.
  rewrite compile_constant; vacuum.
  rewrite compile_constant; vacuum.
  
  rewrite drop_sca; vacuum.
  rewrite compile_constant; vacuum.
  rewrite drop_sca; vacuum.
  rewrite compile_constant; vacuum.
  
  reflexivity.
  vacuum.
Qed.

Ltac new_variable_name base :=
  let base' := (eval compute in base) in
  (lazymatch goal with
  | [ |- context[base'] ] => new_variable_name (base' ++ "'")
  | _ => constr:base'
   end).

Ltac get_prog_and_var_from G :=
  (lazymatch G with
  | refine (prog <- Prog _ _ ([?var >> SCA _ ?p]::_) _ _; _) _ => constr:((var, p))
   end).
Ltac get_prog_and_var_in_goal :=
  let G := match goal with |- ?G => constr:G end in
  get_prog_and_var_from G.

Tactic Notation "start" "compiling" "constant" :=
  eexists;
  setoid_rewrite (start_compiling_sca False "$ret"); vacuum.


Ltac compile_step :=
  first [ let after_tac := (idtac; vacuum) in
          let p := get_prog_and_var_in_goal in
          (lazymatch p with
          | (?var, Word.wmult _ _)
            => (let t1 := new_variable_name "$t1" in
                let t2 := new_variable_name "$t2" in
                first [ rewrite (compile_binop_general IL.Times var t1 t2)
                      | setoid_rewrite (compile_binop_general IL.Times var t1 t2) ]; after_tac)
          | (?var, Word.wplus _ _)
            => (let t1 := new_variable_name "$t1" in
                let t2 := new_variable_name "$t2" in
                first [ rewrite (compile_binop_general IL.Plus var t1 t2)
                      | setoid_rewrite (compile_binop_general IL.Plus var t1 t2) ]; after_tac)
          | (?var, Word.wminus _ _)
            => (let t1 := new_variable_name "$t1" in
                let t2 := new_variable_name "$t2" in
                first [ rewrite (compile_binop_general IL.Minus var t1 t2)
                      | setoid_rewrite (compile_binop_general IL.Minus var t1 t2) ]; after_tac)
          | (?var, nat_as_word _)
            => (first [ rewrite (compile_constant var)
                      | setoid_rewrite (compile_constant var) ]; after_tac)
           end)
        | progress vacuum ].

Tactic Notation "compile" := repeat compile_step.

Tactic Notation "finish" "compiling" := reflexivity.


Goal exists x, 
       refine (ret (Word.wmult 
                      (Word.wplus  3 4)
                      (Word.wminus 5 6))) x.
Proof.
  start compiling constant.

  compile.

  finish compiling.
Qed.

Definition start_sca state vret adts :=
  (@start_compiling_sca_with_precondition _ basic_env state ∅ adts vret).

Goal forall seq: list W, 
     forall state,
       AllADTs state (["$list" >adt> List seq]::∅) ->
       exists x, 
         refine (ret (fold_left (fun (sum item: W) => Word.wplus item sum) seq 0)) x.
Proof.
  intros; eexists.
  setoid_rewrite (start_sca state "$ret"); vacuum.

  setoid_rewrite compile_add_intermediate_adts; vacuum.
  setoid_rewrite (compile_fold_sca basic_env "$list" "$ret" "$head" "$is_empty"); try vacuum.


  Focus 2.
  Require Import GLabelMapFacts.

  Ltac find_label :=
    unfold basic_env, AddPair, MakePair; simpl;
    try match goal with
      | |- GLabelMap.find ?k (GLabelMap.add ?k' (Axiomatic ?spec) _) = Some (Axiomatic ?spec) =>
        apply P.F.add_eq_o; try reflexivity
      | |- GLabelMap.find ?k (GLabelMap.add ?k' (Axiomatic ?spec) _) = Some (Axiomatic ?spec') =>
        rewrite P.F.add_neq_o; [ find_label | ]; [ | congruence ]
    end.

  find_label.

  Focus 2.

  find_label.
rewrite P.F.add_neq_o.
  Unset Printing Notations.
  Show.
  
  setoid_rewrite (pull_forall_loop_sca); vacuum. 

  Focus 2.
  setoid_rewrite compile_add_intermediate_scas_with_ret.
  (* TODO: Figure out why compile_binop_general breaks here; this would save the copies *)
  setoid_rewrite (compile_binop_simple IL.Plus "$ret" "$head'" "$ret'"); vacuum.
  Require Import FiatToFacade.Compiler.Copy.
  rewrite copy_word; vacuum.
  rewrite copy_word; vacuum.

  rewrite drop_second_sca_from_precond; trickle_deletion.
  rewrite drop_second_sca_from_precond; trickle_deletion.
  rewrite drop_second_sca_from_precond; trickle_deletion.
  rewrite no_op; vacuum.
  reflexivity.

  rewrite compile_constant; vacuum.
  rewrite compile_add_intermediate_scas; vacuum.
  Require Import FiatToFacade.Compiler.ADTs.Lists.
  rewrite (@compile_list_delete basic_env ("", "List_delete") 5 "$pointer" "$discard");
    try vacuum; cbv beta; try vacuum. (* TODO: Find way to get rid of the cbv. *)
  rewrite drop_sca; vacuum; trickle_deletion.
  rewrite drop_sca; vacuum; trickle_deletion.
  rewrite no_op; vacuum.
  reflexivity.

  admit.
Qed.

Definition start_adt state vret {ret_type v} wrapper wrapper_inj adts :=
  (@start_compiling_adt_with_precondition _ basic_env state ∅ adts vret ret_type v wrapper wrapper_inj).

Goal forall seq: list W, 
     forall state,
       AllADTs state (["$list" >adt> List seq]::∅) ->
       exists x, 
         refine
           (ret (fold_left
                   (fun (acc: list W) (item: W) =>
                      if IL.wltb 0 item then
                        Word.wmult item 2 :: acc
                      else
                        acc)
                   seq nil)) x.
Proof.
  intros; eexists.
  
  (* Start compiling, copying the state_precond precondition to the resulting
     program's preconditions. Result is stored into [$ret] *)
  rewrite (start_adt state "$ret" List List_inj'); vacuum.

  Check start_compiling_adt_with_precondition.

  Print State.

  unfold Prog. unfold ProgOk.

  Unset Printing Notations.
  idtac.
  
  Print StringMap.MapsTo.
  
  (* Compile the fold, reading the initial value of the accumulator from
     [$init], the input data from [$seq], and storing temporary variables in
     [$head] and [$is_empty]. *)
  setoid_rewrite compile_add_intermediate_adts_with_ret; vacuum.
  setoid_rewrite (compile_fold_adt _ _ _ "$list" "$ret" "$head" "$is_empty" 1 0); vacuum.
  
  (* Extract the quantifiers, and move the loop body to a second goal *)
  rewrite pull_forall_loop_adt; vacuum.
  
  (* The output list is allocated by calling List_new, whose axiomatic
     specification is stored at address 2 *)
  setoid_rewrite compile_add_intermediate_scas; vacuum.
  setoid_rewrite (compile_new _ _ _ "$ret" "new()" ("Lists", "new") 2); try vacuum.
  rewrite drop_scas_from_precond; try vacuum.
  rewrite no_op; try vacuum.
  
  rewrite (@compile_list_delete basic_env ("Lists", "delete") 5 "$pointer" "$discard" "$list");
    try vacuum; cbv beta; try vacuum. (* TODO: Find way to get rid of the cbv. *)
  rewrite drop_scas_from_precond; try vacuum.
  rewrite no_op; vacuum.

  Focus 2. vacuum.
  Focus 2. admit.
  Focus 2. vacuum.
  Focus 2. admit.
  Focus 2.

  (* We're now ready to proceed with the loop's body! *)
  
  (* Compile the if test *)
  setoid_rewrite compile_add_intermediate_scas.
  rewrite (compile_if_adt' "$cond"); vacuum.

  (* Extract the comparison to use Facade's comparison operators, storing the
     operands in [$0] and [$head], and the result of the comparison in
     [$cond] *)
  rewrite (compile_test_simple IL.Lt "$cond" "$0" "$head'"); vacuum. (* TODO: Overriding in test? *)

  (* The two operands of [<] are easily refined *)
  rewrite (compile_constant); vacuum.
  rewrite (copy_word); vacuum.

  (* Now for the true part of the if: append the value to the list *)

  (* Delegate the cons-ing to an ADT operation specified axiomatically; [3]
     points to [List_push] in the current environment; we pick [$new_head] as
     the place to temporarily store the new head *)
  setoid_rewrite (compile_pre_push "$ret" "$head'"); vacuum.

  (* TODO unify cons/push terminology *)
  
  (* The head needs to be multiplied by two before being pushed into the output
     list. *)
  setoid_rewrite (compile_binop_simple IL.Times _ "$head'" "$2"); vacuum.
  rewrite (copy_word); vacuum.
  rewrite (compile_constant); vacuum.
  rewrite no_op; vacuum.
  
  rewrite (compile_push "$ret" "$head'" "$push()" "$discard" ("List", "Push") 3); try vacuum.

  (* Cleanup behind compile_push *)
  do 3 (rewrite drop_sca; vacuum).
  rewrite no_op; vacuum.
  
  (* The false part is a lot simpler *)
  rewrite no_op; vacuum.

  (* Leftover from generalizing before the if *)
  repeat (rewrite drop_sca; vacuum).
  rewrite no_op; vacuum.
  
  (* Ok, this loop body looks good :) *)
  reflexivity.

  admit.
  vacuum.
  unfold Fold.

  (*
  repeat setoid_rewrite Seq_Skip.
  repeat setoid_rewrite Skip_Seq.
   *)
  
  (* Yay, a program! *)
  reflexivity.
Qed.

Definition max seq :=
  fold_left
    (fun (max: W) (item: W) =>
       if (IL.wltb max item) then
         item
       else
         max) seq 0.

Definition min seq :=
  fold_left
    (fun (min: W) (item: W) =>
       if (IL.wltb item min) then
         item
       else
         min) seq 0.

Goal forall seq: list W, 
     forall state,
       state["$list" >> ADT (List seq)] ->
       exists x, 
         refine
           (ret (Word.wminus (max seq) (min seq))) x.
Proof.
  intros * state_precond; eexists. 

  rewrite (start_compiling_sca_with_precondition "$ret" state_precond).
  unfold min, max;
    setoid_rewrite (compile_binop IL.Minus "$ret" "$max" "$min"); cleanup_adt.

  rewrite (compile_fold_sca "$init" "$seq" "$head" "$is_empty" 1 0); cleanup_adt.
  rewrite (pull_forall (fun cond => cond_indep cond "$max")); cleanup_adt.
  rewrite (compile_constant); cleanup_adt.
  rewrite (compile_copy 4 "$list"); cleanup_adt.

  rewrite (compile_fold_sca "$init" "$seq" "$head" "$is_empty" 1 0); cleanup_adt.
  rewrite (pull_forall (fun cond => cond_indep cond "$min")); cleanup_adt.
  rewrite (compile_constant); cleanup_adt.
  rewrite (compile_copy 4 "$list"); cleanup_adt.

  Focus 2.
  
  rewrite (compile_if "$cond").  
  rewrite (compile_test IL.Lt "$cond" "$head" "$min"); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  rewrite (copy_word "$head"); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  reflexivity.

  Focus 2.

  rewrite (compile_if "$cond").  
  rewrite (compile_test IL.Lt "$cond" "$max" "$head"); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  rewrite (copy_word "$head"); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  reflexivity.

  repeat setoid_rewrite Skip_Seq.
  reflexivity.
Qed.

(* TODO: Multiple Facade ADTs vs single cito ADT *)

(* TODO: Sigma types *)

(* TODO: Coercions to get rid of explicit "'" operator. Look at constants being used *)

(* TODO: Use function names *)

  (*
  (* TODO: Cleanup should remove redundant clauses from expressions. Otherwise copying $ret to $ret doesn't work. *)
setoid_rewrite (copy_variable "$ret" "$ret"); cleanup_adt. (* TODO Replace by no-op *)
setoid_rewrite (copy_variable "$head" "$head"); cleanup_adt. (* TODO Replace by no-op *)
reflexivity.
   *)

(* TODO: Three different approaches: 
         * <> precond and postcond, but forall x, precond x -> postcond (add blah x); 
         * Same pre/post cond, with extra conditions (see compile_fold et al.)
         * <> precond and postcond, and postcond indep of modified var (see compile_cons) *)
(* TODO: Post-conditions should include the beginning state, too *)  

(* TODO: Replace all instances of 
       precond st1 /\ blah st1 -> RunsTo -> postcond st2 /\ bluh st2
   by
       precond st1 -> RunsTo -> postcond st2
   with additional constraints `precond st1 -> blah st1` and `postcond st2 -> bluh st2` *)

(* TODO: Tweak autorewrite_equal to make it faster *)
