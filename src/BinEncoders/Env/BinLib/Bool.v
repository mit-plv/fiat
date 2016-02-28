Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.BinLib.Core.

Set Implicit Arguments.

Section BoolBinEncoder.
  Variable E E' : Type.
  Variable Eequiv : E -> E' -> Prop.

  Definition Bool_encode (b : bool) (e : bctx E) : bin * bctx E := (b :: nil, (fst e, 1 + snd e)).

  Definition Bool_decode (b : bin) (e : bctx E') : bool * bin * bctx E':=
    match b with
    | nil => (false, nil, e) (* bogus *)
    | x :: xs => (x, xs, (fst e, 1 + snd e))
    end.

  Theorem Bool_encode_correct :
    forall predicate, encode_decode_correct (bctx_equiv Eequiv) bapp predicate Bool_encode Bool_decode.
  Proof.
    unfold encode_decode_correct, Bool_encode, Bool_decode.
    intros pred env env' xenv xenv' data data' bin ext ext' Peq Ppred Penc Pdec. simpl in *.
    inversion Penc; clear Penc; subst. simpl in *.
    inversion Pdec; clear Pdec; inversion Peq; clear Peq; subst; intuition.
    split; simpl; auto.
  Qed.
End BoolBinEncoder.

Global Instance Bool_decoder E E' ctxequiv predicate
  : decoder (bctx_equiv ctxequiv) bapp predicate (Bool_encode (E:=E)) :=
  { decode := @Bool_decode E';
    decode_correct := @Bool_encode_correct _ _ _ _ }.
