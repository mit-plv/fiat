Require Import Coq.Lists.List.

Require Bedrock.ReifySepExpr.
Require Import Bedrock.ILTacCommon.
Require Import Bedrock.SepIL.
Require Import Bedrock.TacPackIL.
Require Import Bedrock.IL Bedrock.ILEnv Bedrock.SymIL.
Require Import Bedrock.Word Bedrock.Memory.
Require Import Bedrock.Env.
Require Bedrock.PropX.
Require Import Bedrock.ILTacCommon.

Set Implicit Arguments.
Set Strict Implicit.

Declare ML Module "extlib".
Declare ML Module "reif".


(** Cancellation **)
(*******************)
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
  let types := reduce_repr ext tt (ILAlgoTypes.PACK.applyTypes (TacPackIL.ILAlgoTypes.Env ext) nil) in
  let funcs := reduce_repr ext tt (ILAlgoTypes.PACK.applyFuncs (TacPackIL.ILAlgoTypes.Env ext) types (Env.repr (bedrock_funcs_r types) nil)) in
  let preds := reduce_repr ext tt (ILAlgoTypes.PACK.applyPreds (TacPackIL.ILAlgoTypes.Env ext) types nil) in
  let all_props := ReifyExpr.collect_props ltac:(ILTacCommon.reflectable shouldReflect) in
  let pures := all_props in

  let L := eval unfold empB, injB, injBX, starB, exB, hvarB in L in
  let R := eval unfold empB, injB, injBX, starB, exB, hvarB in R in

      let k :=
            (fun types funcs uvars preds L R pures proofs =>
               (*TIME         stop_timer "sep_canceler:reify" ; *)

               ((** TODO: for some reason the partial application to proofs doesn't always work... **)
                 apply (@ApplyCancelSep types funcs preds
                         (ILAlgoTypes.Algos ext types)
                         (@ILAlgoTypes.Algos_correct ext types funcs preds) uvars pures L R);
                [ solve [ apply proofs ] | compute; reflexivity | ]
               (*TIME       ;  stop_timer "sep_canceler:apply_CancelSep" *)
               )
                 || (idtac "failed to apply, generalizing instead!" ;
                    let algos := constr:(ILAlgoTypes.Algos ext types) in
                    let algosC := constr:(@ILAlgoTypes.Algos_correct ext types funcs preds) in
                    generalize (@ApplyCancelSep types funcs preds algos algosC uvars pures L R));

             (*TIME          start_timer "sep_canceler:simplify" ; *)
           first [ simplifier types funcs preds tt | fail 100000 "canceler: simplifier failed" ] ;
             (*TIME          stop_timer "sep_canceler:simplify" ; *)
             (*TIME          start_timer "sep_canceler:clear" ; *)
           try clear types funcs preds
             (*TIME        ;  stop_timer "sep_canceler:clear"  *)
             )
      in
        (*TIME         start_timer "sep_canceler:reify"; *)

        (((sep_canceler_plugin types funcs preds pures L R k))
          (* || fail 10000 "sep_canceler_plugin failed" *))
    | [ |- ?G ] =>
        idtac "no match" G
  end.

(** Symbolic Execution **)
(************************)
Ltac sym_eval isConst ext simplifier :=
(*TIME  start_timer "sym_eval:init" ; *)
  let rec init_from st :=
    match goal with
      | [ H : evalInstrs _ ?st' _ = Some st |- _ ] => init_from st'
      | [ |- _ ] => st
    end
  in
  let cs :=
    match goal with
      | [ H : PropX.codeSpec _ _ |- _ ] => H
    end
  in
    let finish H  :=
        (*TIME                      start_timer "sym_eval:cleanup" ; *)
        ((try exact H)
           ||
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

  let ext' :=
    match ext with
      | _ => eval cbv delta [ ext ] in ext
      | _ => ext
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
  let types := reduce_repr ext tt (ILAlgoTypes.PACK.applyTypes (TacPackIL.ILAlgoTypes.Env ext) nil) in
  let funcs := reduce_repr ext tt (ILAlgoTypes.PACK.applyFuncs (TacPackIL.ILAlgoTypes.Env ext) types (repr (bedrock_funcs_r types) nil)) in
  let preds := reduce_repr ext tt (ILAlgoTypes.PACK.applyPreds (TacPackIL.ILAlgoTypes.Env ext) types nil) in
  let all_props := ReifyExpr.collect_props ltac:(ILTacCommon.reflectable shouldReflect) in
  let pures := all_props in
  match stn_st_SF with
    | tt => idtac (* nothing to symbolically evluate *)
    | ((?stn, ?st), tt) =>
      match find_reg st Rp with
        | (?rp_v, ?rp_pf) =>
          match find_reg st Sp with
            | (?sp_v, ?sp_pf) =>
              match find_reg st Rv with
                | (?rv_v, ?rv_pf) =>
                    let k :=
                        (fun types funcs uvars preds rp sp rv is isP fin pures proofs =>
                           (*TIME       stop_timer "sym_eval:reify" ; *)
                           (*TIME       start_timer "sym_eval:apply" ; *)

                        generalize (@SymILTac.stateD_proof_no_heap types funcs preds
                                             uvars st sp rv rp
                                             sp_pf rv_pf rp_pf
                                             pures proofs cs stn);
                          let H_stateD := fresh in
                          intro H_stateD ;
                          ((apply (@SymILTac.Apply_sym_eval types funcs preds
                            (@ILAlgoTypes.Algos ext types) (@ILAlgoTypes.Algos_correct ext types funcs preds)
                            stn uvars fin st is isP) in H_stateD)
                             || fail 100000 "couldn't apply sym_eval_any! (non-SF case)");
                           (*TIME       stop_timer "sym_eval:apply" ; *)
                           (*TIME       start_timer "sym_eval:simplify" ; *)
                          first [ simplifier types funcs preds H_stateD | fail 100000 "simplifier failed! (non-SF)" ] ;
                          try clear types funcs preds ;
                            (*TIME       stop_timer "sym_eval:simplify" ; *)
                          first [ finish H_stateD (*; clear_instrs all_instrs*) | fail 100000 "finisher failed! (non-SF)" ]
                        )
                    in
                      (*TIME       start_timer "sym_eval:reify"; *)

                    (sym_eval_nosep   types funcs preds pures rp_v sp_v rv_v st k) || fail 10000 "sym_eval_nosep failed"
              end
          end
      end
    | ((?stn, ?st), (?SF, ?H_interp)) =>
        match find_reg st Rp with
          | (?rp_v, ?rp_pf) =>
              match find_reg st Sp with
                | (?sp_v, ?sp_pf) =>
                    match find_reg st Rv with
                      | (?rv_v, ?rv_pf) =>
                        let k := (fun types funcs uvars preds rp sp rv is isP fin pures proofs SF =>
                           (*TIME       stop_timer "sym_eval:reify" ; *)
                           (*TIME       start_timer "sym_eval:apply" ; *)


                                apply (@SymILTac.stateD_proof types funcs preds
                                        uvars _ sp rv rp
                                        sp_pf rv_pf rp_pf pures proofs SF _ _ (refl_equal _)) in H_interp ;
                                  ((apply (@SymILTac.Apply_sym_eval types funcs preds
                                            (@ILAlgoTypes.Algos ext types) (@ILAlgoTypes.Algos_correct ext types funcs preds)
                                        stn uvars fin st is isP) in H_interp)
                                  ) ;
                           (*TIME       stop_timer "sym_eval:apply" ; *)
                           (*TIME       start_timer "sym_eval:simplify" ; *)
                            first [ simplifier types funcs preds H_interp | fail 100000 "simplifier failed! (SF)" ] ;
                            try clear types funcs preds ;
                            (*TIME       stop_timer "sym_eval:simplify" ; *)
                            first [ finish H_interp (* ; clear_instrs all_instrs *) | fail 100000 "finisher failed! (SF)" ])
                        in                         (*TIME       start_timer "sym_eval:reify" ; *)
                          (sym_eval_sep  types funcs preds pures rp_v sp_v rv_v st SF k) || fail 10000  "bad enough"
                    end
              end
        end
    | ?X => idtac X ; fail 100000 "bad"
  end.
