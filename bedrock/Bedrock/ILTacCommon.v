Require Import Bedrock.IL Bedrock.SepIL.
Require Import Bedrock.Word Bedrock.Memory.
Import List.
Require Import Bedrock.DepList Bedrock.EqdepClass.
Require Import Bedrock.PropX.
Require Import Bedrock.Expr Bedrock.SepExpr Bedrock.SepCancel.
Require Import Bedrock.Prover Bedrock.ILEnv.
Require Import Bedrock.Tactics Bedrock.Reflection.
Require Import Bedrock.TacPackIL.
Require Bedrock.ExprUnify.

Require Import Bedrock.SymILTac Bedrock.CancelIL.

Set Implicit Arguments.
Set Strict Implicit.

(*TIME
Add Rec LoadPath "/usr/local/lib/coq/user-contrib/" as Timing.
Add ML Path "/usr/local/lib/coq/user-contrib/".
Declare ML Module "Timing_plugin".
*)

(** isConst **)
(*************)

Ltac isConst_bool e :=
  match e with
    | true => true
    | false => true
    | _ => false
  end.

Ltac isConst e :=
  match e with
    | 0 => true
    | S ?e => isConst e
    | Rp => true
    | Rv => true
    | Sp => true
    | String.EmptyString => true
    | String.String ?e1 ?e2 =>
      match isConst e1 with
        | true => isConst e2
        | _ => false
      end
    | Ascii.Ascii ?a ?b ?c ?d ?e ?f ?g ?h =>
      match isConst_bool a with
        | true =>
          match isConst_bool b with
            | true =>
              match isConst_bool c with
                | true =>
                  match isConst_bool d with
                    | true =>
                      match isConst_bool e with
                        | true =>
                          match isConst_bool f with
                            | true =>
                              match isConst_bool g with
                                | true =>
                                  match isConst_bool h with
                                    | true => true
                                    | _ => false
                                  end
                                | _ => false
                              end
                            | _ => false
                          end
                        | _ => false
                      end
                    | _ => false
                  end
                | _ => false
              end
            | _ => false
          end
        | _ => false
      end
    | _ => false
  end.

(** Should reflect **)
(** TODO: This is probably deprecated **)
Ltac reflectable shouldReflect P :=
  match P with
    | @PropX.interp _ _ _ _ => false
    | @PropX.valid _ _ _ _ _ => false
    | forall x, _ => false
    | context [ PropX.PropX _ _ ] => false
    | context [ PropX.spec _ _ ] => false
    | _ => match type of P with
             | Prop => shouldReflect P
           end
  end.

Ltac shouldReflect P :=
  match P with
    | evalInstrs _ _ _ = _ => false
    | Structured.evalCond _ _ _ _ _ = _ => false
    | @PropX.interp _ _ _ _ => false
    | @PropX.valid _ _ _ _ _ => false
    | @eq ?X _ _ =>
      match X with
        | context [ PropX.PropX ] => false
        | context [ PropX.spec ] => false
      end
    | forall x, _ => false
    | exists x, _ => false
    | _ => true
  end.

(** Reduce Repr **)
Ltac reduce_repr ext sym ls :=
  match sym with
    | tt =>
      eval cbv beta iota zeta delta [
        ext
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core
      ] in ls
    | tt =>
      eval cbv beta iota zeta delta [
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core
      ] in ls
    | _ =>
      eval cbv beta iota zeta delta [
        sym ext
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core
      ] in ls
    | _ =>
      eval cbv beta iota zeta delta [
        sym
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core
      ] in ls
  end.

(** Cancellation **)
(******************)
Section canceller.
  Variable ts : list type.
  Let types := Env.repr BedrockCoreEnv.core ts.
  Variable funcs : functions types.
  Variable preds : SEP.predicates types BedrockCoreEnv.pc BedrockCoreEnv.st.
  Variable algos : ILAlgoTypes.AllAlgos ts.

  Lemma ApplyCancelSep_with_eq :
    forall (algos_correct : ILAlgoTypes.AllAlgos_correct funcs preds algos),
    forall (meta_env : Expr.env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_)),

    forall (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st) res,
    Expr.AllProvable funcs meta_env nil hyps ->
    canceller preds algos (typeof_env meta_env) hyps l r = Some res ->
    forall (WTR : SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env meta_env) nil r = true) cs,
    match res with
      | {| AllExt := new_vars
         ; ExExt  := new_uvars
         ; Lhs    := lhs'
         ; Rhs    := rhs'
         ; Subst  := subst
         |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
          (existsSubst funcs var_env subst 0
            (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
             map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
            (fun meta_env : Expr.env types =>
                (Expr.AllProvable_and funcs meta_env var_env
                  (himp cs
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures lhs') nil (SH.other lhs'))))
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) ))
            (SH.pures lhs'))
    end ->
    himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
            (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
  Proof. intros. eapply ApplyCancelSep_with_eq'; eauto. Qed.

  Lemma ApplyCancelSep :
    forall (algos_correct : ILAlgoTypes.AllAlgos_correct funcs preds algos),
    forall (meta_env : env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_)),
    forall (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st),
      Expr.AllProvable funcs meta_env nil hyps ->
    forall (WTR : SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env meta_env) nil r = true) cs,
    match canceller preds algos (typeof_env meta_env) hyps l r with
      | Some {| AllExt := new_vars
         ; ExExt  := new_uvars
         ; Lhs    := lhs'
         ; Rhs    := rhs'
         ; Subst  := subst
         |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
          (existsSubst funcs var_env subst 0
            (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
             map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
            (fun meta_env : Expr.env types =>
                (Expr.AllProvable_and funcs meta_env var_env
                  (himp cs
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures lhs') nil (SH.other lhs'))))
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) ))
            (SH.pures lhs'))
      | None =>
        himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
                (@SEP.sexprD _ _ _ funcs preds meta_env nil r)
    end ->
    himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
            (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
  Proof.
    intros. consider (canceller preds algos (typeof_env meta_env) hyps l r); intros; auto.
    eapply ApplyCancelSep_with_eq; eauto.
  Qed.

End canceller.

Lemma ignore_regs : forall p specs stn st rs,
  interp specs (![ p ] (stn, st))
  -> interp specs (![ p ] (stn, {| Regs := rs; Mem := Mem st |})).
Proof.
  rewrite sepFormula_eq; auto.
Qed.

Lemma interp_interp_himp : forall cs P Q stn_st,
  interp cs (![ P ] stn_st) ->
  (himp cs P Q) ->
  interp cs (![ Q ] stn_st).
Proof.
  unfold himp. intros. destruct stn_st.
  rewrite sepFormula_eq in *. unfold sepFormula_def in *. simpl in *.
  eapply Imply_E; eauto.
Qed.

Theorem change_Imply_himp : forall (specs : codeSpec W (settings * state)) p q s,
  himp specs p q
  -> interp specs (![p] s ---> ![q] s)%PropX.
Proof.
  rewrite sepFormula_eq.
  unfold himp, sepFormula_def.
  eauto.
Qed.


Ltac change_to_himp := try apply ignore_regs;
  match goal with
    | [ H : interp ?specs (![ _ ] ?X)
      |- interp ?specs (![ _ ] ?X) ] =>
      eapply (@interp_interp_himp _ _ _ _ H)
    | [ |- _ ===> _ ] => hnf; intro
    | _ => apply change_Imply_himp
  end.

Definition smem_read stn := SepIL.ST.HT.smem_get_word (IL.implode stn).
Definition smem_write stn := SepIL.ST.HT.smem_set_word (IL.explode stn).

(** Symbolic Execution **)
(************************)
Require Import Bedrock.ReifyIL.
Lemma Some_cong : forall A (x y : A),
  x = y
  -> Some x = Some y.
  congruence.
Qed.

Ltac find_reg st r :=
  match goal with
    | [ H : Regs st r = ?x |- _ ] => constr:((x, Some_cong (eq_sym H)))
    | _ => constr:((Regs st r, @refl_equal (option W) (Some (Regs st r))))
  end.

Ltac open_stateD H0 :=
  cbv beta iota zeta delta
    [ SymIL.stateD Expr.exprD Expr.applyD
      EquivDec.equiv_dec
      Expr.Range Expr.Domain Expr.Denotation
      Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
      sumbool_rec sumbool_rect
      Peano_dec.eq_nat_dec nat_rec nat_rect eq_rec_r eq_rec eq_rect eq_sym
      nth_error map value
      f_equal

      Expr.AllProvable Expr.Provable Expr.tvarD comparator
    ] in H0;
    let a := fresh in
    let b := fresh in
    let zz := fresh in destruct H0 as [ a [ b zz ] ] ;
    destruct a as [ ? [ ? ? ] ];
    repeat match type of zz with
             | True => clear zz
             | _ /\ _ => let v := fresh in destruct zz as [ v zz ]
           end.

Ltac get_instrs st :=
  let rec find_exact H Hs :=
    match Hs with
      | tt => false
      | (H, _) => true
      | (_, ?Hs) => find_exact H Hs
    end
  in
  let rec get_instrs st ignore :=
    match goal with
      | [ H : Structured.evalCond ?l _ ?r _ st = Some _ |- _ ] =>
        match find_exact H ignore with
          | false =>
            let ignore := constr:((H, ignore)) in
            let v := get_instrs st ignore in
            constr:((((l,r), H), v))
        end
      | [ H : Structured.evalCond ?l _ ?r _ st = None |- _ ] =>
        constr:((((l,r), H), tt))
      | [ H : evalInstrs _ st ?is = Some ?X |- _ ] =>
        let v := get_instrs X tt in
        constr:(((is, H), v))
      | [ H : evalInstrs _ st ?is = None |- _ ] =>
        constr:(((is, H), tt))
      | [ |- _ ] => tt
    end
  in get_instrs st tt.

Ltac clear_instrs ins :=
  match ins with
    | tt => idtac
    | ((_,?H), ?ins) => clear H; clear_instrs ins
  end.

Ltac collectAllTypes_instrs is Ts k :=
  match is with
    | tt => k Ts
    | (((?l,?r), _), ?is) =>
       collectTypes_rvalue ltac:(isConst) l Ts ltac:(fun Ts =>
         collectTypes_rvalue ltac:(isConst) r Ts ltac:(fun Ts =>
          collectAllTypes_instrs is Ts k))
    | ((?i, _), ?is) =>
      collectTypes_instrs ltac:(isConst) i Ts ltac:(fun Ts =>
        collectAllTypes_instrs is Ts k)
  end.

Ltac build_path types instrs st uvars vars funcs k :=
  match instrs with
    | tt =>
      let is := constr:(nil : @SymIL.istream types) in
      let pf := constr:(refl_equal (Some st)) in
      k uvars funcs is (Some st) pf
    | ((?i, ?H), ?is) =>
      match type of H with
        | Structured.evalCond ?l ?t ?r _ ?st = ?st' =>
          reify_rvalue ltac:(isConst) l types funcs uvars vars ltac:(fun uvars funcs l =>
            reify_rvalue ltac:(isConst) r types funcs uvars vars ltac:(fun uvars funcs r =>
              match st' with
                | None =>
                  let i := constr:(inr (@SymIL.SymAssertCond types l t r st') :: (nil : @SymIL.istream types)) in
                  k uvars funcs i (@None state) H
                | Some ?st'' =>
                  build_path types is st uvars vars funcs ltac:(fun uvars funcs is sf pf =>
                    let i := constr:(inr (@SymIL.SymAssertCond types l t r st') :: is) in
                    let pf := constr:(@conj _ _ H pf) in
                    k uvars funcs i sf pf)
              end))
        | evalInstrs _ ?st _ = ?st' =>
          reify_instrs ltac:(isConst) i types funcs uvars vars ltac:(fun uvars funcs sis =>
            match st' with
              | None =>
                let i := constr:(inl (sis, None) :: (nil : @SymIL.istream types)) in
                  k uvars funcs i (@None state) H
              | Some ?st'' =>
                build_path types is st'' uvars vars funcs ltac:(fun uvars funcs is sf pf =>
                  let i := constr:(inl (sis, st') :: is) in
                  let pf := constr:(@conj _ _ H pf) in
                  k uvars funcs i sf pf)
            end)
      end
  end.
