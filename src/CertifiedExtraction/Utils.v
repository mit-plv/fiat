Require Import
        Computation.Core.
Require Export
        CertifiedExtraction.CompUtils
        CertifiedExtraction.PureUtils
        CertifiedExtraction.FacadeUtils.

Ltac cleanup :=
  match goal with
  | _ => cleanup_pure
  | _ => cleanup_facade_pure
  | _ => progress computes_to_inv
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
