Require Export Bedrock.Platform.Cito.StringMap Bedrock.Platform.Cito.StringMapFacts.
Require Export Bedrock.Platform.Cito.SyntaxExpr Bedrock.Platform.Facade.DFacade.
Require Import Coq.Setoids.Setoid.

Add Parametric Morphism {av} : (@eval av)
    with signature (StringMap.Equal ==> eq ==> eq)
      as eval_Morphism.
Proof.
  intros;
  match goal with
  | [ e: Expr |- _ ] => induction e
  end; simpl;
  repeat match goal with
         | [ H: _ |- _ ] => rewrite H
         end;
  reflexivity.
Qed.

Lemma IL_weqb_refl : forall x,
    IL.weqb x x = true.
Proof.
  unfold IL.weqb.
  intros; rewrite Word.weqb_true_iff; reflexivity.
Qed.

Lemma IL_weqb_sound : forall x y,
    IL.weqb x y = true -> x = y.
Proof.
  eauto using Word.weqb_sound.
Qed.

Add Parametric Morphism {av} {env} {prog} : (@Safe av env prog)
    with signature (StringMap.Equal ==> iff)
      as Safe_Morphism.
Proof.
Admitted.

Add Parametric Morphism {av} {env} {prog} : (@RunsTo av env prog)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as RunsTo_Morphism.
Proof.
Admitted.

Ltac isDeterministicStmtConstructor stmt :=
  match stmt with
  | Skip => idtac
  | Seq _ _ => idtac
  | Assign _ _ => idtac
  | _ => fail 1 "This statement has multiple RunsTo and Safe constructors"
  end.

Ltac isSafelyInvertibleStmtConstructor stmt :=
  match stmt with
  | Skip => idtac
  | Seq _ _ => idtac
  | If _ _ _ => idtac
  | Call _ _ _ => idtac
  | Assign _ _ => idtac
  | _ => fail 1 "Not a safely invertible constructor"
  end.
