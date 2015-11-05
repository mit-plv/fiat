Require Import
        Computation.Core.
Require Export
        CertifiedExtraction.CompUtils
        CertifiedExtraction.PureUtils
        CertifiedExtraction.FacadeUtils.

Lemma wrap_inj `{FacadeWrapper AA A} :
  forall (a1 a2: A),
    wrap a1 = wrap a2 -> a1 = a2.
Proof.
  intros.
  cut (Some a1 = Some a2); [ congruence | ].
  rewrite <- !unwrap_wrap.
  congruence.
Qed.

Ltac cleanup :=
  match goal with
  | _ => cleanup_pure
  | _ => cleanup_facade_pure
  | _ => progress computes_to_inv
  | [ H: wrap _ = wrap _ |- _ ] => apply wrap_inj in H
  | [ H: unwrap ?v = Some ?vv |- _ ] => apply wrap_unwrap in H; subst v
  | [  |- context[unwrap (wrap _)] ] => rewrite unwrap_wrap
  | [ H: context[unwrap (wrap _)] |- _ ] => rewrite unwrap_wrap in H
  end.

Ltac wipe :=
  repeat match goal with
         | [ H: ?a = ?a |- _ ] => clear dependent H
         | [ H: forall _: State _, _ |- _ ] => clear dependent H
         | [ H: ?h |- _ ] =>
           let hd := head_constant h in
           match hd with
           | @Learnt => clear dependent H
           | @Safe => clear dependent H
           | @ProgOk => clear dependent H
           end
         end.
