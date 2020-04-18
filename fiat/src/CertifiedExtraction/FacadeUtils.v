Require Export
        Bedrock.Memory
        Bedrock.Platform.Cito.StringMap
        Bedrock.Platform.Cito.StringMapFacts
        Bedrock.Platform.Cito.SyntaxExpr
        Bedrock.Platform.Cito.GLabelMap
        Bedrock.Platform.Facade.DFacade.
Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.PureUtils
        CertifiedExtraction.FMapUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.PureFacadeLemmas.
Require Import
        Coq.Strings.String.

Require Export CertifiedExtraction.FacadeWrappers.

Definition nat_as_word n : Word.word 32 := Word.natToWord 32 n.
Coercion nat_as_word : nat >-> Word.word.

Definition string_as_var str : Expr := Var str.
Coercion string_as_var : string >-> Expr.

Definition word_as_constant w : Expr := Const w.
Coercion word_as_constant : W >-> Expr.

Definition nat_as_constant n : Expr := Const (Word.natToWord 32 n).
Coercion nat_as_constant : nat >-> Expr.

Require Import CertifiedExtraction.FacadeNotations.

Definition Fold (head is_empty seq: StringMap.key)
                _pop_ _empty_ loop_body := (
    Call is_empty _empty_ (seq :: nil);
    While (!is_empty) (
        Call head _pop_ (seq :: nil);
        loop_body;
        Call is_empty _empty_ (seq :: nil)
    )
)%facade.

Definition isTrueExpr var :=
  TestE IL.Eq (Const (bool2w true)) (Var var).

Ltac unfold_coercions :=
  unfold string_as_var, nat_as_constant, nat_as_word, word_as_constant in *.

Module GLabelMapUtils := WMoreFacts_fun (GLabelMap.E) (GLabelMap).

Ltac facade_inversion :=
  progress match goal with
  | [ H: Safe _ ?p _ |- _ ]     => isSafelyInvertibleStmtConstructor p; inversion H; unfold_and_subst; clear H
  | [ H: RunsTo _ ?p _ _ |- _ ] => isSafelyInvertibleStmtConstructor p; inversion H; unfold_and_subst; clear H
  | [ H: Some _ = Some _ |- _ ] => inversion H; unfold_and_subst; clear H
  | [ H: SCA _ _ = SCA _ _ |- _ ] => inversion H; unfold_and_subst; clear H
  end.

Ltac facade_construction_if_helper test trueLemma falseLemma :=
  match test with
  | true => apply trueLemma
  | false => apply falseLemma
  | _ => destruct test
  end.

Ltac facade_construction :=
  progress match goal with
           | [  |- Safe _ ?p _]          => isDeterministicStmtConstructor p; econstructor
           | [  |- RunsTo _ ?p _ _ ]     => isDeterministicStmtConstructor p; econstructor
           | [ H: GLabelMap.MapsTo ?fname (@Axiomatic _ ?spec) ?env |- Safe ?env (Call ?retv ?fname ?args) ?st ] =>
             eapply (@SafeCallAx _ env retv fname args st spec)
           | [ H: GLabelMap.MapsTo ?fname (@Operational _ ?spec) ?env |- Safe ?env (Call ?retv ?fname ?args) ?st ] =>
             eapply (@SafeCallOp _ env retv fname args st spec)
           | [ H: StringMap.MapsTo ?k (wrap (bool2w ?test)) ?st |- Safe _ (DFacade.If (isTrueExpr ?k) _ _) ?st ] =>
             facade_construction_if_helper test SafeIfTrue SafeIfFalse
           | [ H: StringMap.MapsTo ?k (wrap (bool2w ?test)) ?st |- RunsTo _ (DFacade.If (isTrueExpr ?k) _ _) ?st ] =>
             facade_construction_if_helper test RunsToIfTrue RunsToIfFalse
           end.

Ltac cleanup_facade_pure :=
  match goal with
  | [ H: IL.weqb _ _ = true |- _ ] => learn (IL_weqb_sound _ _ H)
  | [ H: context[IL.weqb ?v ?v] |- _ ] => rewrite IL_weqb_refl in H
  | [  |- context[IL.weqb ?v ?v] ] => rewrite IL_weqb_refl
  end.

Ltac spec_t :=
  abstract (repeat match goal with
                   | _ => red
                   | _ => progress intros
                   | _ => progress subst
                   | [ H: exists t, _ |- _ ] => destruct H
                   end; intuition).

Notation "trunk ### name ->> function" := (GLabelMap.add name function trunk) (at level 20).