Require Import
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Sig.

Set Implicit Arguments.

Section EnumEncoder.

  Variable size : nat.
  Variable A : Type.
  Variable cache : Cache.
  Variable cacheAdd : CacheAdd cache nat.

  Variable A_encode : A -> FixInt size.
  Variable A_decode : FixInt size -> A.

  Definition Enum_encode (data : A) := FixInt_encode cacheAdd (A_encode data).

  Definition Enum_decode (b : list bool) (cd : CacheDecode) :=
    match FixInt_decode size cacheAdd b cd with
    | (i, b', cd') => (A_decode i, b', cd')
    end.

  Hypothesis A_encode_decode_correct : forall data, A_decode (A_encode data) = data.

  Theorem Enum_encode_correct :
    forall predicate, encode_decode_correct cache btransformer predicate Enum_encode Enum_decode.
  Proof.
  Admitted.

  Global Instance Enum_decoder predicate
    : decoder cache btransformer predicate Enum_encode :=
    { decode := Enum_decode;
      decode_correct := Enum_encode_correct _ }.

End EnumEncoder.