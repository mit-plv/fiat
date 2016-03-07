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

Instance test_cache : Cache :=
  {| CacheEncode := unit;
     CacheDecode := unit;
     Equiv := fun _ _ => True |}.

Instance test_cache_add_nat : CacheAdd test_cache nat :=
  {| addE := fun ce _ => ce;
     addD := fun cd _ => cd;
     add_correct := fun _ _ _ => id |}.

Definition encode_test (t : test_t) (ce : CacheEncode) :=
  compose btransformer (FixInt_encode test_cache_add_nat (f1 t)) (
  compose btransformer (FixInt_encode test_cache_add_nat (f2 t)) (
  compose btransformer (FixInt_encode test_cache_add_nat (f3 t)) (
  compose btransformer (FixInt_encode test_cache_add_nat (f4 t)) (
                       (fun e => (nil, e)))))) ce.

Global Instance test_decoder
  : decoder test_cache btransformer (fun _ => True) encode_test.
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