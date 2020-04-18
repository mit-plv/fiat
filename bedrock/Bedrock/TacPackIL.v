Require Import Bedrock.Expr Bedrock.SepExpr.
Require Import Bedrock.Prover Bedrock.SymEval.
Require Import Bedrock.Env Bedrock.TypedPackage.
Import List.
Require Import Bedrock.IL Bedrock.SepIL Bedrock.SymIL Bedrock.ILEnv.
Require Bedrock.ReifyExpr Bedrock.ReifySepExpr Bedrock.ReifyHints.
Require Bedrock.Unfolder.

Set Implicit Arguments.
Set Strict Implicit.

(*TIME
Add Rec LoadPath "/usr/local/lib/coq/user-contrib/" as Timing.
Add ML Path "/usr/local/lib/coq/user-contrib/".
Declare ML Module "Timing_plugin".
*)

Module UNF := Unfolder.Make SH ExprUnify.UNIFIER.

Module ILAlgoTypes <: AlgoTypes SEP BedrockCoreEnv.
  Module PACK := TypedPackage.Make SEP BedrockCoreEnv.
  Module SEP_REIFY := ReifySepExpr.ReifySepExpr SEP.
  Module HINTS_REIFY := ReifyHints.Make UNF.LEM.

  Record AllAlgos (ts : list type) : Type :=
  { Prover : option (ProverT (repr BedrockCoreEnv.core ts))
  ; Hints : option (UNF.hintsPayload (repr BedrockCoreEnv.core ts) BedrockCoreEnv.pc BedrockCoreEnv.st)
  ; MemEval : option (MEVAL.MemEvaluator (repr BedrockCoreEnv.core ts) BedrockCoreEnv.pc BedrockCoreEnv.st)
  }.

  Section oplus.
    Variable T : Type.
    Variable F : T -> T -> T.

    Definition oplus (l r : option T) : option T :=
      match l , r with
        | None , _ => r
        | _ , None => l
        | Some l , Some r => Some (F l r)
      end.
  End oplus.

  Definition AllAlgos_composite types (l r : AllAlgos types) : AllAlgos types :=
    match l , r with
      | {| Prover  := pl ; Hints := hl ; MemEval := ml |} , {| Prover := pr ; Hints := hr ; MemEval := mr |} =>
        {| Prover  := oplus (@composite_ProverT _) pl pr
         ; Hints   := oplus (fun l r => {| UNF.Forward := UNF.Forward l ++ UNF.Forward r
         ; UNF.Backward := UNF.Backward l ++ UNF.Backward r |}) hl hr
         ; MemEval := oplus (@MEVAL.Composite.MemEvaluator_composite _ BedrockCoreEnv.pc BedrockCoreEnv.st) ml mr
        |}
    end.

  Record AllAlgos_correct
    (types : list type)
    (funcs : functions (repr BedrockCoreEnv.core types))
    (preds : SEP.predicates (repr BedrockCoreEnv.core types) BedrockCoreEnv.pc BedrockCoreEnv.st)
    (algos : AllAlgos types) : Type :=
  { Acorrect_Prover :
    match Prover algos with
      | None => True
      | Some P => ProverT_correct P funcs
    end
  ; Acorrect_Hints :
    match Hints algos with
      | None => True
      | Some H => UNF.hintsSoundness funcs preds H
    end
  ; Acorrect_MemEval :
    match MemEval algos with
      | None => True
      | Some M =>
        @MEVAL.MemEvaluator_correct _ BedrockCoreEnv.pc BedrockCoreEnv.st M funcs preds
          (tvarD (repr BedrockCoreEnv.core types) BedrockCoreEnv.st) (tvType 0) (tvType 0)
          (@IL_mem_satisfies types) (@IL_ReadWord types) (@IL_WriteWord types)
          (@IL_ReadByte types) (@IL_WriteByte types)
    end
  }.

  Theorem AllAlgos_correct_composite types (l r : AllAlgos types) funcs preds
    (CL : @AllAlgos_correct types funcs preds l)
    (CR : @AllAlgos_correct types funcs preds r) :
    @AllAlgos_correct types funcs preds (AllAlgos_composite l r).
  Proof.
    destruct l; destruct r; destruct CL; destruct CR; simpl in *; constructor; simpl.
    destruct Prover0; destruct Prover1; simpl; auto. apply composite_ProverT_correct; auto.
    destruct Hints0; destruct Hints1; simpl; auto; destruct Acorrect_Hints0; destruct Acorrect_Hints1; constructor; simpl;
      eapply Folds.Forall_app; auto.
    destruct MemEval0; destruct MemEval1; simpl; auto. apply MEVAL.Composite.MemEvaluator_correct_composite; auto.
  Qed.

  Record TypedPackage : Type :=
  { Env   : PACK.TypeEnv
  ; Algos : forall ts, AllAlgos (PACK.applyTypes Env ts)
  ; Algos_correct : forall ts fs ps,
    @AllAlgos_correct (PACK.applyTypes Env ts) (PACK.applyFuncs Env _ fs) (PACK.applyPreds Env _ ps) (Algos ts)
  }.

  Definition EnvOf : TypedPackage -> PACK.TypeEnv := Env.

  Module EmptyPackage.
    Definition empty_package : TypedPackage.
    refine (
      {| Env := {| PACK.Types := nil_Repr EmptySet_type
                 ; PACK.Funcs := fun ts => nil_Repr (Default_signature _)
                 ; PACK.Preds := fun ts => nil_Repr (SEP.Default_predicate _ _ _)
                |}
       ; Algos := fun ts => {| Prover := None ; Hints := None ; MemEval := None |}
       ; Algos_correct := _
      |}).
    abstract (constructor; simpl; trivial).
    Defined.

(*
    Ltac simplifier s1 s2 s3 H :=
      match H with
        | tt =>
          cbv delta [ s1 s2 s3
            empty_package UNF.default_hintsPayload
          ]
        | _ =>
          cbv delta [ s1 s2 s3
            empty_package UNF.default_hintsPayload
          ] in H
      end ;
      MEVAL.LearnHookDefault.unfolder H ;
      provers.ReflexivityProver.unfold_reflexivityProver H ;
      MEVAL.Default.unfolder H ;
      sym_evaluator s1 s2 s3 H.

     Goal forall (cs : codeSpec W (settings * state)) (stn : settings) st st' SF,
       PropX.interp cs (SepIL.SepFormula.sepFormula SF (stn, st)) ->
       Structured.evalCond (RvImm (natToW 0)) IL.Eq (RvImm (natToW 0)) stn st' = Some true ->
       evalInstrs stn st (Assign Rp (RvImm (natToW 0)) :: nil) = Some st' ->
       Regs st' Rp = natToW 0.
     Proof.
       intros.
       sym_eval ltac:(isConst) empty_package simplifier.
       intuition congruence.
     Abort.*)

  End EmptyPackage.

  Module BedrockPackage.
    Definition bedrock_package : TypedPackage.
    refine (
      {| Env := {| PACK.Types := nil_Repr EmptySet_type
        ; PACK.Funcs := bedrock_funcs_r
        ; PACK.Preds := fun ts => nil_Repr (SEP.Default_predicate _ _ _)
      |}
      ; Algos := fun ts => {| Prover := None ; Hints := None ; MemEval := None |}
        ; Algos_correct := _
      |}).
    abstract (constructor; simpl; trivial).
    Defined.

(*
    Ltac simplifier H :=
      match H with
        | tt =>
          cbv delta [
            bedrock_package UNF.default_hintsPayload
          ]
        | _ =>
          cbv delta [
            bedrock_package UNF.default_hintsPayload
          ] in H
      end ;
      MEVAL.LearnHookDefault.unfolder H ;
      provers.ReflexivityProver.unfold_reflexivityProver H ;
      MEVAL.Default.unfolder H ;
      sym_evaluator H.
*)
  End BedrockPackage.

  Module Tactics.

    (** Build Packages for Provers **)
    Ltac build_prover_pack prover ret :=
      let res := constr:(
        let env :=
          {| PACK.Types := Prover.ProverTypes prover
           ; PACK.Funcs := fun ts => Prover.ProverFuncs prover (repr bedrock_types_r ts)
           ; PACK.Preds := fun ts =>
             nil_Repr (SEP.Default_predicate (repr (Prover.ProverTypes prover) (repr bedrock_types_r ts)) (tvType 0) (tvType 1))
          |}
        in
        let algos ts :=
          @Build_AllAlgos (PACK.applyTypes env ts)
            (Some (Prover.Prover prover (PACK.applyTypes env ts)))
            None
            None
        in
        {| Env := env
         ; Algos := algos
         ; Algos_correct := fun ts fs ps =>
           let types := repr (PACK.Types env) (repr bedrock_types_r ts) in
           let funcs := repr (PACK.Funcs env types) fs in
           @Build_AllAlgos_correct types funcs ps (algos ts)
             (@Prover.Prover_correct prover types funcs)
             I I
        |})
      in
      let res := eval simpl in res in
      ret res.

    Module ProverPackTest.
      Require Bedrock.provers.ReflexivityProver.
      (** Test **)
      Goal TypedPackage.
        build_prover_pack provers.ReflexivityProver.ReflexivityProver ltac:(fun x => refine x).
      Defined.
    End ProverPackTest.

    Ltac build_mem_pack mem ret :=
      match type of mem with
        | @MEVAL.MemEvaluatorPackage ?tr ?pc ?st ?ptr ?val IL_mem_satisfies
          IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte =>
          (let res := constr:(
             let TR := Env.repr_combine tr (MEVAL.MemEvalTypes mem) in
             let env :=
               {| PACK.Types := TR
                ; PACK.Funcs := fun ts => MEVAL.MemEvalFuncs mem (Env.repr ILEnv.bedrock_types_r (Env.repr TR ts))
                ; PACK.Preds := fun ts => MEVAL.MemEvalPreds mem (Env.repr ILEnv.bedrock_types_r (Env.repr TR ts))
               |}
             in
             let algos ts :=
               @Build_AllAlgos (PACK.applyTypes env ts)
                 None
                 None
                 (Some (MEVAL.MemEval mem (PACK.applyTypes env ts)))
             in
             @Build_TypedPackage env algos
               (fun ts fs ps => @Build_AllAlgos_correct _ _ _ (algos ts) I I
                 (MEVAL.MemEval_correct mem (Env.repr ILEnv.bedrock_types_r ts) _ _))) in
           let res := eval simpl in res in
           ret res) || fail 10000 "couldn't construct mem_package"
        | ?T =>
          fail 10000 "got bad type" T "expected value of type Packages.MemEvaluatorPackage"
      end.

    Definition min_types_r : Repr type :=
      {| footprint := firstn 2 (footprint bedrock_types_r)
       ; default := default bedrock_types_r
      |}.

    Module MemPackTest.

      Goal TypedPackage.
        pose (mem :=
          {| MEVAL.MemEvalTypes := nil_Repr EmptySet_type
           ; MEVAL.MemEvalFuncs := fun ts => nil_Repr (Default_signature _)
           ; MEVAL.MemEvalPreds := fun ts => nil_Repr (SEP.Default_predicate _ _ _)
           ; MEVAL.MemEval := fun ts => @MEVAL.Default.MemEvaluator_default _ (tvType 0) (tvType 1)
           ; MEVAL.MemEval_correct := fun ts fs ps =>
             @MEVAL.Default.MemEvaluator_default_correct _ _ _ _ _ _ _ _ _ _ _ _ _
          |} : @MEVAL.MemEvaluatorPackage min_types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0)
                   IL_mem_satisfies IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte).
        build_mem_pack mem ltac:(fun x => refine x).
      Defined.
    End MemPackTest.

    (** Package hints together with their environment/parameters. *)
    Record hints := {
      Types : Repr type;
      Functions : forall ts, Repr (signature (repr Types ts));
      PcType : tvar;
      StateType : tvar;
      Predicates : forall ts, Repr (SEP.predicate (Env.repr Types ts) PcType StateType);
      Hints : forall ts, UNF.hintsPayload (repr Types ts) PcType StateType;
      HintsOk : forall ts fs ps, UNF.hintsSoundness (repr (Functions ts) fs) (repr (Predicates ts) ps) (Hints ts)
    }.

    Ltac prepareHints unfoldTac pcType stateType isConst env fwd bwd ret :=
    let types :=
      match type of env with
        | PACK.TypeEnv =>
          let ts := eval cbv beta iota zeta delta [ env PACK.applyTypes PACK.Types ] in (PACK.applyTypes env nil) in
          eval simpl in ts
        | PACK.TypeEnv =>
          let ts := eval cbv beta iota zeta delta [ PACK.applyTypes PACK.Types ] in (PACK.applyTypes env nil) in
          eval simpl in ts
      end
    in
    HINTS_REIFY.collectTypes_hints unfoldTac isConst fwd (Reflect.Tnil) ltac:(fun rt =>
      HINTS_REIFY.collectTypes_hints unfoldTac isConst bwd rt ltac:(fun rt =>
        let rt := constr:(Tcons pcType (Tcons stateType rt)) in
        let types := ReifyExpr.extend_all_types rt types in
        let pcT := ReifyExpr.reflectType types pcType in
        let stateT := ReifyExpr.reflectType types stateType in
        let funcs := eval simpl in (PACK.applyFuncs_red env types nil) in
        let preds := eval simpl in (PACK.applyPreds_red env types nil) in
        (HINTS_REIFY.reify_hints unfoldTac pcT stateT isConst fwd types funcs preds ltac:(fun funcs preds fwd' =>
          HINTS_REIFY.reify_hints unfoldTac pcT stateT isConst bwd types funcs preds ltac:(fun funcs preds bwd' =>
            let types_r := eval cbv beta iota zeta delta [ listToRepr ] in (listToRepr types EmptySet_type) in
            let types_rV := fresh "types" in
            (pose (types_rV := types_r) || fail 1000);
            let funcs_r := HINTS_REIFY.lift_signatures_over_repr funcs types_rV in
            let funcs_r := eval cbv beta iota zeta delta [ listToRepr ] in (fun ts => listToRepr (funcs_r ts) (Default_signature (repr types_rV ts))) in
            let funcs_rV := fresh "funcs" in
            pose (funcs_rV := funcs_r) ;
            let preds_r := HINTS_REIFY.lift_ssignatures_over_repr preds types_rV pcT stateT in
            let preds_rV := fresh "preds" in
            let preds_r := eval cbv beta iota zeta delta [ listToRepr ] in (fun ts => listToRepr (preds_r ts) (SEP.Default_predicate (repr types_rV ts) pcT stateT)) in
            pose (preds_rV := preds_r) ;
            let fwd' := HINTS_REIFY.lift_lemmas_over_repr fwd' types_rV pcT stateT in
            let bwd' := HINTS_REIFY.lift_lemmas_over_repr bwd' types_rV pcT stateT in
            let pf := fresh "fwd_pf" in
            assert (pf : forall ts fs ps, UNF.hintsSoundness (repr (funcs_rV ts) fs) (repr (preds_rV ts) ps) ({| UNF.Forward := fwd' ts ; UNF.Backward := bwd' ts |})) by
              (abstract (constructor; [ HINTS_REIFY.prove fwd | HINTS_REIFY.prove bwd ])) ;
            let res := constr:(
              {| Types      := types_rV
               ; PcType     := pcT
               ; StateType  := stateT
               ; Functions  := funcs_rV
               ; Predicates := preds_rV
               ; Hints      := fun ts => {| UNF.Forward := fwd' ts ; UNF.Backward := bwd' ts |}
               ; HintsOk    := pf
               |}) in ret res))))).


    (** builds a [TypedPackage] from the arguments
     ** - [hints] is a list of separation logic hints
     **)
    Ltac build_hints_pack hints ret :=
      let res := constr:(
        let env :=
          {| PACK.Types := Types hints
           ; PACK.Funcs := fun ts => Functions hints (repr bedrock_types_r ts)
           ; PACK.Preds := fun ts => Predicates hints (repr bedrock_types_r ts) |}
        in
        let algos ts :=
          @Build_AllAlgos (PACK.applyTypes env ts)
            None
            (Some (Hints hints ts))
            None
        in
        @Build_TypedPackage env algos
          (fun ts fs ps =>
            let types := repr bedrock_types_r (repr (Types hints) ts) in
            @Build_AllAlgos_correct _ _ _ (algos ts) I (HintsOk hints ts fs ps) I))
      in
      let res := eval simpl in res in
      ret res.

    Definition bedrock_env : PACK.TypeEnv :=
      {| PACK.Types := nil_Repr EmptySet_type
       ; PACK.Funcs := fun ts => nil_Repr (Default_signature _)
       ; PACK.Preds := fun ts => nil_Repr (SEP.Default_predicate _ _ _)
      |}.

    Module HintsPackTest.

(*
      Goal TypedPackage.
        PACKAGED.prepareHints ltac:(fun x => x) W (prod IL.settings IL.state) ltac:(isConst) bedrock_env tt tt ltac:(fun v =>
          build_hints_pack v ltac:(fun x => refine x)).
      Defined.
*)
    End HintsPackTest.


    (** given to [TypedPackage]s, combines them and passes the combined [TypedPackage]
     ** to [k].
     ** This tactic will fail if any of the environments are not compatible.
     **)
Ltac glue_pack left_pack right_pack ret :=
  let res := constr:(
    let l := left_pack in
    let r := right_pack in
    let ntypesV := Env.repr_combine (PACK.Types (Env l)) (PACK.Types (Env r)) in
    let nfuncsV ts :=
      Env.repr_combine (PACK.Funcs (Env l) (Env.repr ntypesV ts))
                       (PACK.Funcs (Env r) (Env.repr ntypesV ts))
    in
    let npredsV ts :=
      Env.repr_combine (PACK.Preds (Env l) (Env.repr ntypesV ts))
                       (PACK.Preds (Env r) (Env.repr ntypesV ts))
    in
    let env :=
      {| PACK.Types := ntypesV
       ; PACK.Funcs := nfuncsV
       ; PACK.Preds := npredsV
       |}
    in
    let algos ts :=
      @AllAlgos_composite
        (ILAlgoTypes.PACK.applyTypes env (Env.repr ntypesV ts))
        (Algos l (Env.repr ntypesV ts))
        (Algos r (Env.repr ntypesV ts))
    in
    {| Env   := env
     ; Algos := algos
     ; Algos_correct := fun ts fs ps =>
       let types := @ILAlgoTypes.PACK.applyTypes env ts in
       let funcs := @ILAlgoTypes.PACK.applyFuncs env types fs in
       let preds := @ILAlgoTypes.PACK.applyPreds env types ps in
       @ILAlgoTypes.AllAlgos_correct_composite
       types
       (ILAlgoTypes.Algos l types)
       (ILAlgoTypes.Algos r types)
       funcs
       preds
       (@ILAlgoTypes.Algos_correct l types funcs preds)
       (@ILAlgoTypes.Algos_correct r types funcs preds)
(*
       AllAlgos_correct_composite (@Algos_correct l (Env.repr ntypesV ts)
                                                    (Env.repr (nfuncsV ts) fs)
                                                    (Env.repr (npredsV ts) ps))
                                  (@Algos_correct r (Env.repr ntypesV ts)
                                                    (Env.repr (nfuncsV ts) fs)
                                                    (Env.repr (npredsV ts) ps))
*)
    |})
  in ret res.

(** given a tuple or list of [TypedPackage]s, this tactic combines them all and calls [k] with
 ** the result.
 **)
Ltac glue_packs packs k :=
  match type of packs with
    | TypedPackage => k packs
    | _ =>
      match packs with
        | tt => k BedrockPackage.bedrock_package
        | nil => k BedrockPackage.bedrock_package
        | ?L :: ?R =>
          glue_packs R ltac:(fun R => glue_pack L)
        | (?L, ?R) =>
          glue_packs L ltac:(fun L =>
          glue_packs R ltac:(fun R =>
            glue_pack L R k))
      end
  end.

(** TODO: is there a way to make this more efficient? **)
Ltac opaque_pack pack :=
  let pack := eval hnf in pack in
  let pack := eval simpl in pack in
  match pack with
    | @Build_TypedPackage ?env ?algos ?pf =>
      refine (@Build_TypedPackage env algos _); abstract (exact pf)
  end.

Goal TypedPackage.
  Require Bedrock.provers.ReflexivityProver.
  build_prover_pack provers.ReflexivityProver.ReflexivityProver ltac:(fun x =>
    build_mem_pack (MEVAL.Default.package bedrock_types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0) IL_mem_satisfies IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte) ltac:(fun y =>
    glue_pack x y ltac:(opaque_pack))).
Qed.

(*
Goal TypedPackage bedrock_types_r (tvType 0) (tvType 1) IL_mem_satisfies IL_ReadWord IL_WriteWord.
  build_prover_pack Provers.ReflexivityProver ltac:(fun x =>
    build_mem_pack (MEVAL.Default.package bedrock_types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0) IL_mem_satisfies IL_ReadWord IL_WriteWord) ltac:(fun y =>
      idtac "1" ;
    glue_packs (x, y, y) ltac:(fun v => exact v))).
Qed.
*)

Module Extension.

  Ltac combine_repr l r :=
    match l with
      | tt => r
      | _ => match r with
               | tt => l
               | _ => constr:(Env.repr_combine l r)
             end
    end.
  Ltac combine_repr_abs l r :=
    match eval hnf in l with
      | tt => r
      | ?abs => match r with
                  | tt => l
                  | _ => constr:(fun ts => Env.repr_combine (l ts) (r ts))
                end
    end.

  Ltac gather_env_prover prover ts fs ps k :=
    match eval hnf in prover with
      | tt => k ts fs ps
      | ?prover =>
        let ts := combine_repr ts (ProverTypes prover) in
        let fs := combine_repr_abs fs (ProverFuncs prover) in
        k ts fs ps
    end.
  Ltac gather_env_meval meval ts fs ps k :=
    match eval hnf in meval with
      | tt => k ts fs ps
      | ?meval => match type of meval with
                    | @MEVAL.MemEvaluatorPackage ?tr ?pc ?st ?ptr ?val IL_mem_satisfies IL_ReadWord IL_WriteWord =>
                      let ts := combine_repr ts (Env.repr_combine tr (MEVAL.MemEvalTypes mem)) in
                      let fs := combine_repr_abs fs (MEVAL.MemEvalFuncs meval) in
                      let ps := combine_repr_abs ps (MEVAL.MemEvalPreds meval ts) in
                      k ts fs ps
                  end
    end.
  Ltac gather_env_pack pack ts fs ps k :=
    match eval hnf in pack with
      | tt => k ts fs ps
      | ?pack =>
        let ts := combine_repr ts (PACK.Types (Env pack)) in
        let fs := combine_repr_abs fs (PACK.Funcs (Env pack)) in
        let ps := combine_repr_abs ps (PACK.Preds (Env pack)) in
        k ts fs ps
    end.

  Lemma hintSideD_app : forall types pc st funcs preds A B,
    @UNF.hintSideD types funcs pc st preds A ->
    @UNF.hintSideD types funcs pc st preds B ->
    @UNF.hintSideD types funcs pc st preds (A ++ B).
  Proof.
    induction 1; simpl; intros; auto. constructor; eauto. eapply IHForall. auto.
  Qed.

  Definition extend_opt_hints types pc st (o : option (UNF.hintsPayload types pc st)) (fwd bwd : list (UNF.LEM.lemma types pc st)) : option (UNF.hintsPayload types pc st) :=
    match fwd , bwd with
      | nil , nil => o
      | _ , _ =>
        match o with
          | None => Some (UNF.Build_hintsPayload fwd bwd)
          | Some e => Some (UNF.Build_hintsPayload (UNF.Forward e ++ fwd) (UNF.Backward e ++ bwd))
        end
    end.
  Lemma extend_opt_hintsOk : forall types pc st funcs preds (o : option (UNF.hintsPayload types pc st)) (fwd bwd : list (UNF.LEM.lemma types pc st)),
    match o with
      | None => True
      | Some H => @UNF.hintsSoundness types funcs pc st preds H
    end ->
    UNF.hintSideD funcs preds fwd ->
    UNF.hintSideD funcs preds bwd ->
    match extend_opt_hints o fwd bwd with
      | Some H => UNF.hintsSoundness funcs preds H
      | None => True
    end.
  Proof.
    unfold extend_opt_hints; destruct o; simpl; intros.
    destruct H; destruct fwd; destruct bwd; constructor; simpl; auto; repeat rewrite app_nil_r; eauto using hintSideD_app.
    destruct fwd; destruct bwd; constructor; simpl; auto; repeat rewrite app_nil_r; eauto using hintSideD_app.
  Qed.

  Ltac extend unfoldTac isConst pack prover mevals fwd bwd :=
    let reduce_repr t := eval cbv beta iota zeta delta
      [ ILAlgoTypes.Env ILAlgoTypes.PACK.Funcs ILEnv.bedrock_funcs_r map hd tl Env.listToRepr Env.listOptToRepr Env.repr_combine Env.nil_Repr Env.repr ILEnv.BedrockCoreEnv.core
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Preds ILAlgoTypes.PACK.Funcs ILEnv.bedrock_types_r ] in t
    in
    let red_pack t := eval cbv beta iota zeta delta
      [ ILAlgoTypes.MemEval ILAlgoTypes.Hints ILAlgoTypes.Prover ILAlgoTypes.Algos pack ] in t
    in
    (*TIME start_timer "extend:gather" ; *)
    gather_env_pack pack (ILEnv.BedrockCoreEnv.core) tt tt ltac:(fun ts fs ps =>
    gather_env_prover prover ts fs ps ltac:(fun ts fs ps =>
    gather_env_meval mevals ts fs ps ltac:(fun ts fs ps =>
    (*TIME stop_timer "extend:gather" ; *)
    (*TIME start_timer "extend:reduce_repr" ; *)
      let types := reduce_repr (Env.repr ts nil) in
    (*TIME stop_timer "extend:reduce_repr" ; *)
    (*TIME start_timer "extend:reify" ; *)
      HINTS_REIFY.collectTypes_hints unfoldTac isConst fwd (Reflect.Tnil) ltac:(fun Ts =>
      HINTS_REIFY.collectTypes_hints unfoldTac isConst bwd Ts ltac:(fun Ts => (
      let types := ReifyExpr.extend_all_types Ts types in
      set (typesV := types) ;
      let funcs := reduce_repr (Env.repr (fs types) nil) in
      let preds := reduce_repr (Env.repr (ps types) nil) in
      let pcT := ILEnv.BedrockCoreEnv.pc in
      let stateT := ILEnv.BedrockCoreEnv.st in
      HINTS_REIFY.reify_hints unfoldTac pcT stateT isConst fwd types funcs preds ltac:(fun funcs preds fwd' =>
      HINTS_REIFY.reify_hints unfoldTac pcT stateT isConst bwd types funcs preds ltac:(fun funcs preds bwd' => (
    (*TIME stop_timer "extend:reify" ; *)
    (*TIME start_timer "extend:lifting" ; *)
        let types_r := eval cbv beta iota zeta delta [ typesV Env.listToRepr map ] in (Env.listToRepr typesV Expr.EmptySet_type) in
        set (types_rV := types_r) ;
        let funcs_r := HINTS_REIFY.lift_signatures_over_repr funcs types_rV in
        let funcs_r := eval cbv beta iota zeta delta [ Env.listToRepr map ] in
          (fun ts => Env.listToRepr (funcs_r ts) (Expr.Default_signature (Env.repr types_rV ts))) in
        set (funcs_rV := funcs_r) ;
        let preds_r := HINTS_REIFY.lift_ssignatures_over_repr preds types_rV pcT stateT in
        let preds_r := eval cbv beta iota zeta delta [ Env.listToRepr map ] in
          (fun ts => Env.listToRepr (preds_r ts) (SEP.Default_predicate (Env.repr types_rV ts) pcT stateT)) in
        set (preds_rV := preds_r) ;
    (*TIME stop_timer "extend:lifting" ; *)
    (*TIME start_timer "extend:combining" ; *)
        set (env := {| ILAlgoTypes.PACK.Types := types_rV
                     ; ILAlgoTypes.PACK.Funcs := funcs_rV
                     ; ILAlgoTypes.PACK.Preds := preds_rV |}) ;
        let fwd' := HINTS_REIFY.lift_lemmas_over_repr fwd' types_rV pcT stateT in
        let bwd' := HINTS_REIFY.lift_lemmas_over_repr bwd' types_rV pcT stateT in
        let nprover :=
          match prover with
            | tt => match pack with
                      | tt => constr:(fun ts => @None (Prover.ProverT (Env.repr types_rV ts)))
                      | _ => red_pack (fun ts => ILAlgoTypes.Prover (ILAlgoTypes.Algos pack (Env.repr types_rV ts)))
                    end
            | _ => match pack with
                     | tt => constr:(fun ts => Some (Prover.Prover (Env.repr types_rV ts)))
                     | _ => fail 1000 "we don't support combining provers yet!" prover pack
                   end
          end
        in
        let nmevals :=
          match mevals with
            | tt => match pack with
                      | tt => constr:(fun ts => @None (MEVAL.MemEvaluator (Env.repr types_rV ts) pcT stateT))
                      | _ => red_pack (fun ts => ILAlgoTypes.MemEval (ILAlgoTypes.Algos pack (Env.repr types_rV ts)))
                    end
            | _ => match pack with
                     | tt => constr:(fun ts => Some (MEVAL.MemEval mevals (Env.repr types_rV ts)))
                     | _ => fail 1000 "not sure"
                   end
          end
        in
        let nhints :=
          let res := match pack with
            | tt => constr:(fun ts => @extend_opt_hints _ _ _ None (fwd' ts) (bwd' ts))
            | _ => red_pack (fun ts => @extend_opt_hints _ _ _ (ILAlgoTypes.Hints (ILAlgoTypes.Algos pack (Env.repr types_rV ts))) (fwd' ts) (bwd' ts))
(*
constr:(fun ts => @None (UNF.hintsPayload (Env.repr ILEnv.BedrockCoreEnv.core (Env.repr types_rV ts)) pcT stateT)) *)
          end in
          eval simpl extend_opt_hints in res
        in
        let algos := eval cbv beta in
          (fun ts => @ILAlgoTypes.Build_AllAlgos (ILAlgoTypes.PACK.applyTypes env ts) (nprover ts) (nhints ts) (nmevals ts)) in
        set (algos_V := algos) ;
        refine ({| ILAlgoTypes.Env := env
                 ; ILAlgoTypes.Algos := algos_V
                 ; ILAlgoTypes.Algos_correct := _
                |});
    (*TIME stop_timer "extend:combining" ; *)
        abstract (let ts := fresh "ts" in
         let fs := fresh "fs" in
         let ps := fresh "ps" in
         intros ts fs ps ;
         let ntypes := fresh "types" in
         set (ntypes := @ILAlgoTypes.PACK.applyTypes env ts) ;
         let nfuncs := fresh "funcs" in
         set (nfuncs := @ILAlgoTypes.PACK.applyFuncs env ntypes fs) ;
         let npreds := fresh "preds" in
         set (npreds := @ILAlgoTypes.PACK.applyPreds env ntypes ps) ;
         constructor ;
         [ match prover with
             | tt => match pack with
                       | tt => simpl; trivial
                       | _ => eapply (@ILAlgoTypes.Algos_correct pack ntypes nfuncs npreds)
                     end
             | _ => match pack with
                      | tt => eapply (@Prover.Prover_correct prover ntypes nfuncs)
                      | _ => idtac "NOPE" prover pack
                    end
           end
         | match goal with
             | [ |- match ?X with _ => _ end ] =>
               match pack with
                 | tt => change (X) with (@extend_opt_hints _ _ _ None (fwd' ntypes) (bwd' ntypes))
                 | _ =>
                   (change (X) with (@extend_opt_hints _ _ _ (ILAlgoTypes.Hints (ILAlgoTypes.Algos pack (Env.repr types_rV ts))) (fwd' ntypes) (bwd' ntypes)))
               end; apply extend_opt_hintsOk; [ simpl; auto | HINTS_REIFY.prove fwd | HINTS_REIFY.prove bwd ]
           end
         | match mevals with
             | tt => match pack with
                       | tt => simpl; trivial
                       | _ => eapply (@ILAlgoTypes.Algos_correct pack ntypes nfuncs npreds)
                     end
             | _ => idtac
           end
         ]) || fail 1000 "Failed to prove. Make sure your function and predicate environments are compatible. If they are, Please report this.")
      || fail 1000 "Combine failed. Make sure your type environments are compatible!")
      || fail 1000 "Type collection failed! Please report this!"
      ))))))).

  End Extension.



(*    extend tt tt BedrockPackage.bedrock_package tt tt tt tt. *)


  End Tactics.

  Definition AlgoImpl := AllAlgos.
  Definition AlgoProof := AllAlgos_correct.
End ILAlgoTypes.
