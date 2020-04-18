Require Import Coq.Lists.List.

Require Bedrock.ReifySepExpr.
Require Import Bedrock.ILTacCommon.
Require Import Bedrock.SepIL.
Require Import Bedrock.TacPackIL.
Require Import Bedrock.IL Bedrock.ILEnv Bedrock.SymIL.
Require Import Bedrock.Word Bedrock.Memory.
Require Import Bedrock.Env.

Export ILTacCommon.

Set Implicit Arguments.
Set Strict Implicit.

Module SEP_REIFY := ReifySepExpr.ReifySepExpr SEP.

(** Cancellation **)
(******************)
(** The parameters are the following.
 ** - [isConst] is an ltac [* -> bool]
 ** - [ext] is a [TypedPackage .. .. .. .. ..]
 ** - [simplifier] is an ltac that simplifies the goal after the cancelation, it is passed
 **   constr:(tt).
 **)
Ltac sep_canceller isConst ext simplifier :=
(*TIME  start_timer "sep_canceler:change_to_himp" ; *)
  (try change_to_himp) ;
(*TIME  stop_timer "sep_canceler:change_to_himp" ; *)
(*TIME  start_timer "sep_canceler:init" ; *)
  let ext' :=
    match ext with
      | tt => eval cbv delta [ ILAlgoTypes.BedrockPackage.bedrock_package ] in ILAlgoTypes.BedrockPackage.bedrock_package
      | _ => eval cbv delta [ ext ] in ext
      | _ => ext
    end
  in
  match goal with
    | [ |- himp ?cs ?L ?R ] =>
      let pcT := constr:(W) in
      let stateT := constr:(prod settings state) in
(*TIME      start_timer "sep_canceler:init"; *)
(*TIME      start_timer "sep_canceler:gather_props" ; *)
      let all_props :=
        ReifyExpr.collect_props ltac:(ILTacCommon.reflectable shouldReflect)
      in
      let pures := ReifyExpr.props_types all_props in
(*TIME      stop_timer "sep_canceler:gather_props" ; *)
(*TIME      start_timer "sep_canceler:unfold_notation" ; *)
      let L := eval unfold empB, injB, injBX, starB, exB, hvarB in L in
      let R := eval unfold empB, injB, injBX, starB, exB, hvarB in R in
(*TIME      stop_timer "sep_canceler:unfold_notation" ; *)
(*TIME      start_timer "sep_canceler:reify" ; *)
      (** collect types **)
      let Ts := constr:(Reflect.Tnil) in
       ReifyExpr.collectTypes_exprs ltac:(isConst) pures Ts ltac:(fun Ts =>
      SEP_REIFY.collectTypes_sexpr ltac:(isConst) L Ts ltac:(fun Ts =>
      SEP_REIFY.collectTypes_sexpr ltac:(isConst) R Ts ltac:(fun Ts =>
      (** check for potential universe inconsistencies **)
      match Ts with
        | context [ PropX.PropX ] =>
          fail 1000 "found PropX in types list"
            "(this causes universe inconsistencies)" Ts
        | context [ PropX.spec ] =>
          fail 1000 "found PropX in types list"
            "(this causes universe inconsistencies)" Ts
        | _ => idtac
      end ;
      (** elaborate the types **)
      let types_ :=
        reduce_repr ext tt (ILAlgoTypes.PACK.applyTypes (ILAlgoTypes.Env ext) nil)
      in
      let types_ := ReifyExpr.extend_all_types Ts types_ in
      let typesV := fresh "types" in
      pose (typesV := types_);
      (** build the variables **)
      let uvars := eval simpl in (@nil _ : Expr.env typesV) in
      let gvars := uvars in
      let vars := eval simpl in (@nil Expr.tvar) in
      (** build the funcs **)
      let funcs := reduce_repr ext tt (ILAlgoTypes.PACK.applyFuncs (ILAlgoTypes.Env ext) typesV nil) in
      let pcT := constr:(Expr.tvType 0) in
      let stT := constr:(Expr.tvType 1) in
      (** build the base sfunctions **)
      let preds := reduce_repr ext tt (ILAlgoTypes.PACK.applyPreds (ILAlgoTypes.Env ext) typesV nil) in
      ReifyExpr.reify_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
      let proofs := ReifyExpr.props_proof all_props in
      SEP_REIFY.reify_sexpr ltac:(isConst) L typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds L =>
      SEP_REIFY.reify_sexpr ltac:(isConst) R typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds R =>
(*TIME        stop_timer "sep_canceler:reify" ; *)
(*TIME        start_timer "sep_canceler:pose" ; *)
        let funcsV := fresh "funcs" in
        pose (funcsV := funcs) ;
        let predsV := fresh "preds" in
        pose (predsV := preds) ;
(*TIME          stop_timer "sep_canceler:pose" ; *)
(*TIME          start_timer "sep_canceler:apply_CancelSep" ; *)
        (((** TODO: for some reason the partial application to proofs doesn't always work... **)
         apply (@ApplyCancelSep typesV funcsV predsV
                   (ILAlgoTypes.Algos ext typesV)
                   (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV) uvars pures L R);
           [ solve [ apply proofs ] | compute; reflexivity | ]
(*TIME       ;  stop_timer "sep_canceler:apply_CancelSep" *)
 )
        || (idtac "failed to apply, generalizing instead!" ;
            let algos := constr:(ILAlgoTypes.Algos ext typesV) in
            idtac "-" ;
            let algosC := constr:(@ILAlgoTypes.Algos_correct ext typesV funcsV predsV) in
            idtac "*" ;
            first [ generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars pures L R) ; idtac "p"
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars pures L)  ; idtac "o"
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars pures) ; idtac "i"
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC uvars) ; idtac "u"
                  | generalize (@ApplyCancelSep typesV funcsV predsV algos algosC) ; pose (uvars) ; idtac "y"
                  | generalize (@ApplyCancelSep typesV funcsV predsV); pose (algosC) ; idtac "r"
                  | generalize (@ApplyCancelSep typesV funcsV) ; idtac "q"
                  ])) ;
(*TIME          start_timer "sep_canceler:simplify" ; *)
           first [ simplifier typesV funcsV predsV tt | fail 100000 "canceler: simplifier failed" ] ;
(*TIME          stop_timer "sep_canceler:simplify" ; *)
(*TIME          start_timer "sep_canceler:clear" ; *)
           try clear typesV funcsV predsV
(*TIME        ;  stop_timer "sep_canceler:clear"  *)
        ))))))
    | [ |- ?G ] =>
      idtac "no match" G
  end.

(** Symbolic Execution **)
(************************)
(** NOTE:
 ** - [isConst] is an ltac function of type [* -> bool]
 ** - [ext] is the extension. it is a value of type [TypedPackage]
 ** - [simplifier] is an ltac that takes a hypothesis names and simplifies it
 **     (this should be implmented using [cbv beta iota zeta delta [ ... ] in H])
 **     (it is recommended/necessary to call [sym_evaluator] or import its simplification)
 **)
Ltac sym_eval isConst ext simplifier :=
(*TIME  start_timer "sym_eval:init" ; *)
  let rec init_from st :=
    match goal with
      | [ H : evalInstrs _ ?st' _ = Some st |- _ ] => init_from st'
      | [ |- _ ] => st
    end
  in
  let stn_st_SF :=
    match goal with
      | [ H : PropX.interp _ (![ ?SF ] ?X) |- _ ] =>
        let SF := eval unfold empB, injB, injBX, starB, exB, hvarB in SF in
        constr:((X, (SF, H)))
      | [ H : Structured.evalCond _ _ _ ?stn ?st = _ |- _ ] =>
        let st := init_from st in
        constr:(((stn, st), tt))
      | [ H : IL.evalInstrs ?stn ?st _ = _ |- _ ] =>
        let st := init_from st in
        constr:(((stn, st), tt))
      | [ |- _ ] => tt
    end
  in
  let cs :=
    match goal with
      | [ H : PropX.codeSpec _ _ |- _ ] => H
    end
  in
  let ext' :=
    match ext with
      | _ => eval cbv delta [ ext ] in ext
      | _ => ext
    end
  in
  match stn_st_SF with
    | tt => idtac (* nothing to symbolically evluate *)
    | ((?stn, ?st), ?SF) =>
      match find_reg st Rp with
        | (?rp_v, ?rp_pf) =>
          match find_reg st Sp with
            | (?sp_v, ?sp_pf) =>
              match find_reg st Rv with
                | (?rv_v, ?rv_pf) =>
(*TIME                  stop_timer "sym_eval:init" ; *)
(*TIME                  start_timer "sym_eval:gather_instrs" ; *)
                  let all_instrs := get_instrs st in
                  let all_props :=
                    ReifyExpr.collect_props ltac:(ILTacCommon.reflectable shouldReflect)
                  in
                  let pures := ReifyExpr.props_types all_props in
                  let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
(*TIME                  stop_timer "sym_eval:gather_instrs" ; *)
                  (** collect the raw types **)
(*TIME                  start_timer "sym_eval:reify" ; *)
                  let Ts := constr:(Reflect.Tnil) in
                  let Ts k :=
                    match SF with
                      | tt => k Ts
                      | (?SF,_) => (** TODO: a little sketchy since it is in CPS **)
                        SEP_REIFY.collectTypes_sexpr ltac:(isConst) SF Ts k
                    end
                  in
                    Ts ltac:(fun Ts =>
                  collectAllTypes_instrs all_instrs Ts ltac:(fun Ts =>
                  ReifyExpr.collectTypes_exprs ltac:(isConst) regs Ts ltac:(fun Ts =>
                  ReifyExpr.collectTypes_exprs ltac:(isConst) pures Ts ltac:(fun Ts =>
                  (** check for potential universe problems **)
                  match Ts with
                    | context [ PropX.PropX ] =>
                      fail 1000 "found PropX in types list"
                        "(this causes universe inconsistencies)" Ts
                    | context [ PropX.spec ] =>
                      fail 1000 "found PropX.spec in types list"
                        "(this causes universe inconsistencies)" Ts
                    | _ => idtac
                  end;
                  (** elaborate the types **)
                  let types_ := reduce_repr ext tt (ILAlgoTypes.PACK.applyTypes (TacPackIL.ILAlgoTypes.Env ext) nil) in
                  let types_ := ReifyExpr.extend_all_types Ts types_ in
                  let typesV := fresh "types" in
                  pose (typesV := types_);
                  (** Check the types **)
                  let pcT := constr:(Expr.tvType 0) in
                  let stT := constr:(Expr.tvType 1) in
                  (** build the variables **)
                  let uvars := constr:(@nil (@sigT Expr.tvar (fun t : Expr.tvar => Expr.tvarD typesV t))) in
                  let vars := uvars in
                  (** build the base functions **)
                  let funcs := reduce_repr ext tt (ILAlgoTypes.PACK.applyFuncs (TacPackIL.ILAlgoTypes.Env ext) typesV (repr (bedrock_funcs_r typesV) nil)) in
                   (** build the base sfunctions **)
(*                  let preds := constr:(@nil (@SEP.ssignature typesV pcT stT)) in *)
                  let preds := reduce_repr ext tt (ILAlgoTypes.PACK.applyPreds (TacPackIL.ILAlgoTypes.Env ext) typesV nil) in
                  (** reflect the expressions **)
                  ReifyExpr.reify_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
                  let proofs := ReifyExpr.props_proof all_props in

                  ReifyExpr.reify_expr ltac:(isConst) rp_v typesV funcs uvars vars ltac:(fun uvars funcs rp_v  =>
                  ReifyExpr.reify_expr ltac:(isConst) sp_v typesV funcs uvars vars ltac:(fun uvars funcs sp_v =>

                  ReifyExpr.reify_expr ltac:(isConst) rv_v typesV funcs uvars vars ltac:(fun uvars funcs rv_v =>
                    let finish H  :=
(*TIME                      start_timer "sym_eval:cleanup" ; *)
                      ((try exact H) ||
                       (let rec destruct_exs H :=
                         match type of H with
                           | Logic.ex _ =>
                             destruct H as [ ? H ] ; destruct_exs H
                           | forall x : ?T, _ =>
                             let n := fresh in
                             evar (n : T);
                             let e := eval cbv delta [ n ] in n in
                             specialize (H e)
                           | (_ /\ (_ /\ _)) /\ (_ /\ _) =>
                             destruct H as [ [ ? [ ? ? ] ] [ ? ? ] ];
                               repeat match goal with
                                        | [ H' : _ /\ _ |- _ ] => destruct H'
                                      end
                           | False => destruct H
                           | ?G =>
                             fail 100000 "bad result goal" G
                         end
                        in let fresh Hcopy := fresh "Hcopy" in
                          let T := type of H in
                            assert (Hcopy : T) by apply H; clear H; destruct_exs Hcopy))
(*TIME                    ;  stop_timer "sym_eval:cleanup" *)
                    in
                    build_path typesV all_instrs st uvars vars funcs ltac:(fun uvars funcs is fin_state is_pf =>
                      match SF with
                        | tt =>
(*TIME                          stop_timer "sym_eval:reify" ; *)
                          let funcsV := fresh "funcs" in
                          pose (funcsV := funcs) ;
                          let predsV := fresh "preds" in
                          pose (predsV := preds) ;
(*                          let ExtC := constr:(@Algos_correct _ _ _ _ _ _ ext typesV funcsV predsV) in *)
                          generalize (@SymILTac.stateD_proof_no_heap typesV funcsV predsV
                            uvars st sp_v rv_v rp_v
                            sp_pf rv_pf rp_pf pures proofs cs stn) ;
                          let H_stateD := fresh in
                          intro H_stateD ;
                          ((apply (@SymILTac.Apply_sym_eval typesV funcsV predsV
                            (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                            stn uvars fin_state st is is_pf) in H_stateD)
                          || fail 100000 "couldn't apply sym_eval_any! (non-SF case)");
                          first [ simplifier typesV funcsV predsV H_stateD | fail 100000 "simplifier failed! (non-SF)" ] ;
                          try clear typesV funcsV predsV ;
                          first [ finish H_stateD (*; clear_instrs all_instrs*) | fail 100000 "finisher failed! (non-SF)" ]
                        | (?SF, ?H_interp) =>
                          SEP_REIFY.reify_sexpr ltac:(isConst) SF typesV funcs pcT stT preds uvars vars
                          ltac:(fun uvars funcs preds SF =>
(*TIME                            stop_timer "sym_eval:reify" ; *)
(*TIME                            start_timer "sym_eval:pose" ; *)
                            let funcsV := fresh "funcs" in
                            pose (funcsV := funcs) ;
                            let predsV := fresh "preds" in
                            pose (predsV := preds) ;
(*                            let ExtC := constr:(@Algos_correct ext typesV funcsV predsV) in *)
(*TIME                            stop_timer "sym_eval:pose" ; *)
(*TIME                            start_timer "sym_eval:apply_stateD_proof" ; *)
                            apply (@SymILTac.stateD_proof typesV funcsV predsV
                              uvars _ sp_v rv_v rp_v
                              sp_pf rv_pf rp_pf pures proofs SF _ _ (refl_equal _)) in H_interp ;
(*TIME                            stop_timer "sym_eval:apply_stateD_proof" ; *)
(*TIME                            start_timer "sym_eval:apply_sym_eval" ; *)
                            ((apply (@SymILTac.Apply_sym_eval typesV funcsV predsV
                              (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                              stn uvars fin_state st is is_pf) in H_interp) ||
                             (idtac "couldn't apply sym_eval_any! (SF case)";
                               first [
                                 generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                                   stn uvars fin_state st is is_pf) ; idtac "6"
                               | generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                                   stn uvars fin_state st) ; idtac "5"
                               | generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                                   stn uvars) ; idtac "4"
                               | generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)); idtac "3"
                               | generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV)) ; generalize (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV) ; idtac "2"
                               | generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV) ; idtac "1"
                               ])) ;
(*TIME                             stop_timer "sym_eval:apply_sym_eval" ; *)
(*TIME                             start_timer "sym_eval:simplify" ; *)
                            first [ simplifier typesV funcsV predsV H_interp | fail 100000 "simplifier failed! (SF)" ] ;
(*TIME                             stop_timer "sym_eval:simplify" ; *)
(*TIME                             start_timer "sym_eval:clear" ; *)
                            try clear typesV funcsV predsV ;
(*TIME                             stop_timer "sym_eval:clear" ; *)
                            first [ finish H_interp ; clear_instrs all_instrs | fail 100000 "finisher failed! (SF)" ])
                      end)))))  ))))
              end
          end
      end
  end.
