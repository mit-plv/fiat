Require Export List.

Definition bin := list bool.

Record encode_decode_R {A : Type} :=
  { encode_R : A -> (bin -> bin) -> bin;
    decode_R : forall B, bin -> (A -> bin -> B) -> B;
    proof_R  : forall data encode data ( ) =              }.

Section Specifications.

  Context {A : Type}.
  Variable predicate : A -> Prop.
  Variable encode : A -> bin.
  Variable decode : bin -> A.
  bin -> nat.

  decode (encode a) = a

  length (decode' (encode a ++ ext)) = length (encode a)

  Definition encode_correct :=
    forall val ext, predicate val -> decode ((encode val) ++ ext) = (val, ext).

  Definition decode_shorten :=
    forall ls, length (snd (decode ls)) <= pred (length ls).

  Definition encode_nonnil :=
    forall val, encode val <> nil.

End Specifications.

Record encode_decode_R {A : Type} :=
  { predicate_R : A -> Prop;
    encode_R    : A -> bin;
    decode_R    : bin -> A * bin;
    proof_R     : encode_correct predicate_R encode_R decode_R;
    shorten_R   : decode_shorten decode_R }.

encode forall A B, A -> (bin -> B) -> B
decode forall A B, bin -> (A -> bin -> B) -> B

forall k a, encode a (\b. decode b k) = k a


Arguments encode_decode_R : clear implicits.
