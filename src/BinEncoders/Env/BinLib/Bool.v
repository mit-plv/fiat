Require Import
        Coq.NArith.BinNat
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.BinLib.Core.

Set Implicit Arguments.

Section BoolBinEncoder.
  Variable cache : Cache.
  Variable cacheAdd : CacheAdd cache N.

  Definition Bool_encode (b : bool) (ce : CacheEncode) :=
    (b :: nil, addE ce 1%N).

  Definition Bool_decode (b : list bool) (cd : CacheDecode) :=
    match b with
    | nil => (false, nil, cd) (* bogus *)
    | x :: xs => (x, xs, addD cd 1%N)
    end.

  Theorem Bool_encode_correct :
    forall predicate, encode_decode_correct cache btransformer predicate Bool_encode Bool_decode.
  Proof.
    unfold encode_decode_correct, Bool_encode, Bool_decode.
    intros pred env env' xenv xenv' data data' bin ext ext' Peq Ppred Penc Pdec. simpl in *.
    inversion Penc; clear Penc; subst.
    inversion Pdec; clear Pdec; subst.
    intuition. apply add_correct. auto.
  Qed.
End BoolBinEncoder.

Arguments Bool_encode {_ _} _ _.