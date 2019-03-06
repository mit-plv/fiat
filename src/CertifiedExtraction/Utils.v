Require Import
        Computation.Core.
Require Export
        CertifiedExtraction.Core
        CertifiedExtraction.PureUtils
        CertifiedExtraction.FacadeUtils.

Ltac cleanup :=
  match goal with
  | _ => cleanup_pure
  | _ => cleanup_facade_pure
  | _ => progress computes_to_inv
  | [ H: wrap _ = wrap _ |- _ ] => apply wrap_inj in H
  | [ H: NTSome _ = NTSome _ |- _ ] => inversion H; unfold_and_subst; clear H
  | [  |- context[NameTagAsStringOption NTNone] ]     => cbv [NameTagAsStringOption]
  | [ H: context[NameTagAsStringOption NTNone] |- _ ] => may_touch H; cbv [NameTagAsStringOption] in H
  | [  |- context[NameTagAsStringOption (NTSome _)] ]     => cbv [NameTagAsStringOption]
  | [ H: context[NameTagAsStringOption (NTSome _)] |- _ ] => may_touch H; cbv [NameTagAsStringOption] in H
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
