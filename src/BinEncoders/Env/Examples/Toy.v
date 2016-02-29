Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.BinLib.FixInt.

Set Implicit Arguments.

Record test_t :=
  { f1 : { n : N | (n < exp2 32)%N };
    f2 : { n : N | (n < exp2 8)%N };
    f3 : { n : N | (n < exp2 4)%N };
    f4 : { n : N | (n < exp2 16)%N } }.

Definition enc_ctx := unit.
Definition dec_ctx := unit.

Definition envequiv (e : enc_ctx) (d : dec_ctx) := True.

Definition encode_test (t : test_t) (ctx : bctx enc_ctx) :=
  compose btransformer (FixInt_encode (f1 t)) (
  compose btransformer (FixInt_encode (f2 t)) (
  compose btransformer (FixInt_encode (f3 t)) (
  compose btransformer (FixInt_encode (f4 t)) (
                       (fun e => (nil, e)))))) ctx.

Global Instance test_decoder
  : decoder (bctx_equiv envequiv) btransformer (fun _ => True) encode_test.
Proof.
  unfold encode_test.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eapply compose_decoder; eauto with typeclass_instances; intuition.
  instantiate (1:=fun _ => True); eauto.

  eexists. unfold encode_decode_correct.
  instantiate (1:=fun b e => (Build_test_t proj proj0 proj1 proj2, b, e)).
  intuition. inversion H1. inversion H2. subst. eauto. inversion H2.
  subst. destruct data. eauto. inversion H1. subst. inversion H2. eauto.
Defined.