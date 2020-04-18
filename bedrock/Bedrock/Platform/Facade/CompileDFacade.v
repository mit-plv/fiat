Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.FacadeFacts.
Require Import Bedrock.Platform.Facade.DFacadeFacts.
Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Platform.Facade.DFacade.

Require Import Bedrock.Platform.Facade.NameDecoration.
Require Import Bedrock.Platform.Cito.SyntaxExpr.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import Bedrock.Platform.Cito.Option.
Require Import Coq.Bool.Bool.

Require Import Bedrock.Platform.Cito.GeneralTactics.
Require Import Bedrock.Platform.Cito.GeneralTactics3.
Require Import Bedrock.Platform.Cito.GeneralTactics4.
Require Import Bedrock.Platform.Cito.GeneralTactics5.

Require Import Bedrock.StringSet.
Import StringSet.
Require Import Bedrock.Platform.Cito.StringSetFacts.

Local Notation PRE := tmp_prefix.
Definition fun_ptr_varname := PRE ++ "fptr".

Fixpoint compile (s : Stmt) : Facade.Stmt :=
  match s with
    | Skip => Facade.Skip
    | Seq a b => Facade.Seq (compile a) (compile b)
    | If e t f => Facade.If e (compile t) (compile f)
    | While e c => Facade.While e (compile c)
    | Assign x e => Facade.Assign x e
    | Call x f args =>
      Facade.Seq
        (Facade.Label fun_ptr_varname f)
        (Facade.Call x (Var fun_ptr_varname) args)
  end.

Lemma compile_assigned s : forall x, is_good_varname x = true -> In x (Facade.assigned (compile s)) -> In x (assigned s).
Proof.
  induction s; simpl; intros x Hgn Hin.
  - eapply empty_iff in Hin; intuition.
  - eapply union_iff in Hin; openhyp; eapply union_iff; eauto.
  - eapply union_iff in Hin; openhyp; eapply union_iff; eauto.
  - eauto.
  - eapply union_iff in Hin; openhyp; eauto.
    eapply singleton_iff in H; subst.
    discriminate.
  - eauto.
Qed.

Lemma compile_no_assign_to_args (spec : OperationalSpec) : is_disjoint (Facade.assigned (compile (Body spec))) (of_list (ArgVars spec)) = true.
Proof.
  destruct spec; simpl.
  eapply is_disjoint_iff.
  eapply is_disjoint_iff in no_assign_to_args.
  unfold Disjoint in *.
  intros x [Hinass Hinavars].
  eapply no_assign_to_args.
  split; eauto.
  eapply compile_assigned; eauto.
  eapply of_list_spec in Hinavars.
  eapply List.forallb_forall in args_name_ok; eauto.
Qed.

Definition compile_op (spec : OperationalSpec) : Facade.OperationalSpec.
  refine
    (Facade.Build_OperationalSpec (ArgVars spec) (RetVar spec) (compile (Body spec)) (args_no_dup spec) (ret_not_in_args spec) _).
  eapply compile_no_assign_to_args.
Defined.
