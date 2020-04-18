Require Export Coq.Lists.List.

Set Implicit Arguments.

Section Specifications.

  Variable (data_t : Type)
           (bin_t  : Type).

  Definition encode_decode_correct
             (predicate : data_t -> Prop)
             (encode : data_t -> bin_t)
             (decode : bin_t -> data_t) :=
    forall data, predicate data -> decode (encode data) = data.

  Class decoder
        (predicate : data_t -> Prop)
        (encode : data_t -> bin_t) :=
  { decode : bin_t -> data_t;
    decode_correct :
      forall data, predicate data -> decode (encode data) = data }.

End Specifications.

Notation "'Decoder' 'of' encode" := (decoder (fun _ => True) encode) (at level 20, no associativity).
