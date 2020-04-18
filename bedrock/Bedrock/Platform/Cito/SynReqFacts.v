Require Import Bedrock.Platform.Cito.CompileStmtSpec.
Require Import Bedrock.StringSet.
Import StringSet.
Require Import Bedrock.Platform.Cito.FreeVars.
Require Import Bedrock.Platform.Cito.SynReqFactsUtil.

Local Infix ";;" := Syntax.Seq (right associativity, at level 95).

Local Hint Resolve Subset_singleton.
Local Hint Resolve In_to_set.
Local Hint Resolve to_set_In.
Local Hint Resolve Subset_union_right Max.max_lub.

Require Bedrock.Platform.Cito.CompileExpr Bedrock.Platform.Cito.CompileExprs Bedrock.Platform.Cito.SaveRet.

Ltac t := unfold syn_req, CompileExpr.syn_req, CompileExprs.syn_req, SaveRet.syn_req,
  in_scope, WellFormed.wellformed;
  simpl; intuition;
    repeat (match goal with
              | [ H : Subset _ _ |- _ ] => apply Subset_union_left in H
              | [ H : (max _ _ <= _)%nat |- _ ] =>
                generalize (Max.max_lub_l _ _ _ H);
                  generalize (Max.max_lub_r _ _ _ H);
                    clear H
              | [ H : WellFormed.args_not_too_long _ |- _ ] => inversion_clear H; []
              | [ |- match ?E with Some _ => _ | None => _ end ] => destruct E
            end; intuition).

Local Hint Constructors WellFormed.args_not_too_long.

Lemma Subset_syn_req_In : forall x vars temp_size s, syn_req vars temp_size s -> Subset (singleton x) (free_vars s) -> List.In x vars.
  t.
Qed.

Lemma syn_req_Seq_Seq : forall vars temp_size a b c, syn_req vars temp_size ((a ;; b) ;; c) -> syn_req vars temp_size (a ;; b ;; c).
  t.
Qed.

Lemma syn_req_Seq : forall vars temp_size a b c, syn_req vars temp_size ((a ;; b) ;; c) -> syn_req vars temp_size (b ;; c).
  t.
Qed.

Lemma syn_req_If_true : forall vars temp_size e t f k, syn_req vars temp_size (Syntax.If e t f ;; k) -> syn_req vars temp_size (t ;; k).
  t.
Qed.

Lemma syn_req_If_false : forall vars temp_size e t f k, syn_req vars temp_size (Syntax.If e t f ;; k) -> syn_req vars temp_size (f ;; k).
  t.
Qed.

Lemma syn_req_If_e : forall vars temp_size e t f k, syn_req vars temp_size (Syntax.If e t f ;; k) -> CompileExpr.syn_req vars temp_size e 0.
  t.
Qed.

Lemma syn_req_While_e : forall vars temp_size e s k, syn_req vars temp_size (Syntax.While e s ;; k) -> CompileExpr.syn_req vars temp_size e 0.
  t.
Qed.

Lemma syn_req_While : forall vars temp_size e s k, syn_req vars temp_size (Syntax.While e s ;; k) -> syn_req vars temp_size (s ;; Syntax.While e s ;; k).
  t.
Qed.

Lemma syn_req_Call_f : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> CompileExpr.syn_req vars temp_size f 0.
  t.
Qed.

Local Hint Resolve Max.le_max_l Max.le_max_r.

Lemma max_more : forall n m k,
  (n <= m)%nat
  -> (n <= max m k)%nat.
  intros; transitivity m; eauto.
Qed.

Local Hint Resolve max_more.

Require Import Coq.Lists.List.

Lemma args_bound' : forall x args,
  In x args
  -> (DepthExpr.depth x <= fold_right max 0 (map DepthExpr.depth args))%nat.
  induction args; simpl; intuition (subst; auto).
  eapply Le.le_trans; [ | eapply Max.le_max_r]; eauto.
Qed.

Lemma args_bound : forall args,
  List.Forall (fun e => (DepthExpr.depth e <= CompileExprs.depth args)%nat) args.
  intros; apply Forall_forall; intros.
  apply args_bound'; auto.
Qed.

Local Hint Resolve args_bound.

Lemma syn_req_Call_args : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> CompileExprs.syn_req vars temp_size args args 0.
  t.
Qed.

Lemma syn_req_Call_ret : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> SaveRet.syn_req vars x.
  t.
Qed.

Require Import Bedrock.Platform.AutoSep.

Lemma syn_req_goodSize : forall vars temp_size x f args k, syn_req vars temp_size (Syntax.Call x f args ;; k) -> goodSize (2 + List.length args).
  t.
Qed.

Lemma syn_req_Seq_Skip : forall vars temp_size s, syn_req vars temp_size s -> syn_req vars temp_size (s ;; Syntax.Skip).
  t.
Qed.
