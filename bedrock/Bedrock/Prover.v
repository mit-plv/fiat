Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Bedrock.Expr Bedrock.Env.
Require Import Bedrock.Reflection.

Set Implicit Arguments.
Set Strict Implicit.

(** Provers that establish [expr]-encoded facts *)

Definition ProverCorrect types (fs : functions types) (summary : Type)
    (** Some prover work only needs to be done once per set of hypotheses,
       so we do it once and save the outcome in a summary of this type. *)
  (valid : env types -> env types -> summary -> Prop)
  (prover : summary -> expr types -> bool) : Prop :=
  forall vars uvars sum,
    valid uvars vars sum ->
    forall goal,
      prover sum goal = true ->
      ValidProp fs uvars vars goal ->
      Provable fs uvars vars goal.

Record ProverT (types : list type) : Type :=
{ Facts : Type
; Summarize : exprs types -> Facts
; Learn : Facts -> exprs types -> Facts
; Prove : Facts -> expr types -> bool
}.

Record ProverT_correct (types : list type) (P : ProverT types) (funcs : functions types) : Type :=
{ Valid : env types -> env types -> Facts P -> Prop
; Valid_weaken : forall u g f ue ge,
  Valid u g f -> Valid (u ++ ue) (g ++ ge) f
; Summarize_correct : forall uvars vars hyps,
  AllProvable funcs uvars vars hyps ->
  Valid uvars vars (Summarize P hyps)
; Learn_correct : forall uvars vars facts,
  Valid uvars vars facts -> forall hyps,
  AllProvable funcs uvars vars hyps ->
  Valid uvars vars (Learn P facts hyps)
; Prove_correct : ProverCorrect funcs Valid (Prove P)
}.

Record ProverPackage : Type :=
{ ProverTypes : Repr type
; ProverFuncs : forall ts, Repr (signature (repr ProverTypes ts))
; Prover : forall ts, ProverT (repr ProverTypes ts)
; Prover_correct : forall ts fs,
  ProverT_correct (Prover ts) (repr (ProverFuncs ts) fs)
}.


(** Generic lemmas/tactis to prove things about provers **)

Hint Rewrite EquivDec_refl_left SemiDec_EquivDec_refl_left : provers.

(* Everything looks like a nail?  Try this hammer. *)
Ltac t1 := match goal with
             | _ => discriminate
             | _ => progress (hnf in *; simpl in *; intuition; subst)
             | [ x := _ : _ |- _ ] => subst x || (progress (unfold x in * ))
             | [ H : ex _ |- _ ] => destruct H
             | [ H : context[nth_error (updateAt ?new ?ls ?n) ?n] |- _ ] =>
               rewrite (nth_error_updateAt new ls n) in H
                 || rewrite nth_error_updateAt in H
             | [ s : signature _ |- _ ] => destruct s
             | [ H : Some _ = Some _ |- _ ] => injection H; clear H
             | [ H : _ = Some _ |- _ ] => rewrite H in *
             | [ H : _ === _ |- _ ] => rewrite H in *

             | [ |- context[match ?E with
                              | Const _ _ => _
                              | Var _ => _
                              | UVar _ => _
                              | Func _ _ => _
                              | Equal _ _ _ => _
                              | Not _ => _
                            end] ] => destruct E
             | [ |- context[match ?E with
                              | None => _
                              | Some _ => _
                            end] ] => destruct E
             | [ |- context[if ?E then _ else _] ] =>
               consider E; intro
             | [ |- context[match ?E with
                              | nil => _
                              | _ :: _ => _
                            end] ] => destruct E
             | [ H : _ || _ = true |- _ ] => apply orb_true_iff in H; destruct H
             | [ _ : context[match ?E with
                               | Const _ _ => _
                               | Var _ => _
                               | UVar _ => _
                               | Func _ _ => _
                               | Equal _ _ _ => _
                               | Not _ => _
                             end] |- _ ] => destruct E
             | [ _ : context[match ?E with
                               | nil => _
                               | _ :: _ => _
                             end] |- _ ] => destruct E
             | [ H : context[if ?E then _ else _] |- _ ] =>
               revert H; consider E; try do 2 intro
             | [ _ : context[match ?E with
                               | left _ => _
                               | right _ => _
                             end] |- _ ] => destruct E
             | [ _ : context[match ?E with
                               | tvProp => _
                               | tvType _ => _
                             end] |- _ ] => destruct E
             | [ _ : context[match ?E with
                               | None => _
                               | Some _ => _
                             end] |- _ ] => match E with
                                              | context[match ?E with
                                                          | None => _
                                                          | Some _ => _
                                                  end] => fail 1
                                              | _ => destruct E
                                            end

             | [ _ : context[match ?E with (_, _) => _ end] |- _ ] => destruct E
           end.

Ltac t := repeat t1; eauto.

(** Composite Prover **)
Section composite.
  Variable types : list type.
  Variables pl pr : ProverT types.

  Definition composite_ProverT : ProverT types :=
  {| Facts := Facts pl * Facts pr
   ; Summarize := fun hyps =>
     (Summarize pl hyps, Summarize pr hyps)
   ; Learn := fun facts hyps =>
     let (fl,fr) := facts in
     (Learn pl fl hyps, Learn pr fr hyps)
   ; Prove := fun facts goal =>
     let (fl,fr) := facts in
     (Prove pl fl goal) || (Prove pr fr goal)
   |}.

  Variable funcs : functions types.
  Variable pl_correct : ProverT_correct pl funcs.
  Variable pr_correct : ProverT_correct pr funcs.

  Theorem composite_ProverT_correct : ProverT_correct composite_ProverT funcs.

    refine (
      {| Valid := fun uvars vars (facts : Facts composite_ProverT) =>
        let (fl,fr) := facts in
          Valid pl_correct uvars vars fl /\ Valid pr_correct uvars vars fr
      |}); destruct pl_correct; destruct pr_correct; simpl; try destruct facts; intuition eauto.
    unfold ProverCorrect. destruct sum; intuition.
    apply orb_true_iff in H.
    destruct H; eauto.
  Qed.
End composite.
