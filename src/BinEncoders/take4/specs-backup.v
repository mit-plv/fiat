Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Set Implicit Arguments.

Definition bin := list bool.

Class Decoder
      (A : Type)
      (encode : A -> bin) :=
  { decode : bin -> A * bin;
    decode_correct : forall data ext, decode (encode data ++ ext) = (data, ext) }.

Class Decoder_wf
      (A : Type)
      (encode : A -> bin)
      (decoder : Decoder encode) :=
  { decode_wf : forall bin, length (snd (decode bin)) <= pred (length bin) }.

Fixpoint exp2 (n : nat) :=
  match n with
  | O => S O
  | S n' => exp2 n' + exp2 n'
  end.

Variable FixNat_encode : forall size, {n | n < exp2 size} -> bin.

Global Instance FixNat_decoder
       (size : nat)
  : Decoder (FixNat_encode size). Admitted.

Variable List1_encode :
  forall (A : Type) (encode_A : A -> bin) (size : nat),
    {ls : list A | length ls < exp2 size} -> bin.

Global Instance List1_decoder
       (size : nat)
       (A : Type)
       (encode_A : A -> bin)
       (A_Decoder : Decoder encode_A)
  : Decoder (List1_encode encode_A size). Admitted.

Record SSRecord :=
  { field1 : { n | n < exp2 4 };
    field2 : { ls : list { n | n < exp2 16 } | length ls < exp2 8 };
    field3 : { n | n < exp2 2 } }.

Definition SS_encode (s : SSRecord) :=
  FixNat_encode _ (field1 s) ++
  List1_encode (FixNat_encode _) _ (field2 s) ++
  FixNat_encode _ (field3 s).

Lemma decode_app_l' (data_t proj_t : Type) :
  forall (proj : data_t -> proj_t)
         (encode1 : proj_t -> bin)
         (encode2 : data_t -> bin),
  (exists decode, forall data ext,
    decode (encode1 (proj data) ++ ext) = (proj data, ext)) ->
  (exists decode, forall data ext,
    decode (proj data) (encode2 data ++ ext) = (data, ext)) ->
  exists decode, forall data ext,
    decode (encode1 (proj data) ++ (encode2 data) ++ ext) = (data, ext).
Proof.
Admitted.

Lemma decode_app_l'' (data_t proj_t T T' : Type) (f : data_t -> T -> T') :
  forall (proj : data_t -> proj_t)
         (encode1 : proj_t -> bin)
         (encode2 : data_t -> bin),
  (exists (decode : T' -> bin -> proj_t * bin), forall t data ext,
    decode (f data t) (encode1 (proj data) ++ ext) = (proj data, ext)) ->
  (exists (decode : T' * _ -> bin -> data_t * bin), forall t data ext,
    decode (f data t, (proj data)) (encode2 data ++ ext) = (data, ext)) ->
  exists (decode : T' -> bin -> data_t * bin), forall t data ext,
    decode (f data t) (encode1 (proj data) ++ (encode2 data) ++ ext) = (data, ext).
Proof.
Admitted.


Definition SS_decode :
  { decode : bin -> SSRecord | forall data, decode (SS_encode data) = data }.
Proof.
  eexists.

  unfold SS_encode.
  eapply decode_app_l''.

Lemma SS_decoder' :
  exists decode,
    forall (t : unit) data ext, decode t (SS_encode data ++ ext) = (data, ext).
Proof.
  unfold SS_encode.


  setoid_rewrite <- app_assoc.
  eapply decode_app_l''.

  eexists; intros data ext; destruct data; simpl. Focus 2. setoid_rewrite <- app_assoc.

  eapply decode_app_l'' .

  instantiate (1:=fun _ => _). simpl.
  eapply decode_correct.

  assert (exists
     decode0 : unit * {n : nat | n < exp2 4} -> bin -> SSRecord * bin,
     forall (t : unit) (data : SSRecord) (ext : list bool),
     decode0 (t, field1 data)
       ((List1_encode (FixNat_encode 16) 8 (field2 data) ++
         FixNat_encode 2 (field3 data)) ++ ext) = (data, ext)).

  setoid_rewrite <- app_assoc.


Abort.

Lemma decode_app_l (data_t proj1_t : Type) (proj2_t : proj1_t -> Type) :
  forall (proj1 : data_t -> proj1_t)
         (proj2 : data_t -> proj2_t)
         (build : proj1_t -> proj2_t -> data_t)
         (encode1 : proj1_t -> bin)
         (decode1 : bin -> proj1_t * bin)
         (encode2 : data_t -> bin)
         (decode2 : bin -> data_t * bin),
  (forall data ext, decode1 (encode1 (proj1 data) ++ ext) = (proj1 data, ext)) ->
  (exists decode, forall data ext,
    decode (proj1 data) (encode2 data ++ ext) = (data, ext)) ->
  exists decode, forall data ext,
    decode (encode1 (proj1 data) ++ (encode2 data) ++ ext) = (data, ext).
Proof.
Admitted.


Lemma decode_app' (X Y Z : Type) :
  forall (data : Z)
         (ext bin_x bin_y : bin)
         (build : X -> Y -> Z),
  exists (data_x : X)
         (data_y : Y),
    (exists decode_x, decode_x (bin_x ++ (bin_y ++ ext)) = (data_x, bin_y ++ ext)) ->
    (exists decode_y, decode_y (bin_y ++ ext) = (data_y, ext)) ->
    build data_x data_y = data ->
    exists decode, decode ((bin_x ++ bin_y) ++ ext) = (data, ext).
Proof.
  admit.
Qed.

Global Instance SS_decoder : Decoder SS_encode :=
  {| decode := _;
     decode_correct := _ |}.
Proof.
  intros data ext.

  unfold SS_encode.
  repeat rewrite <- app_assoc.



 (* define a logical representation of a record *)
 Record SSRecord :=
   { field1 : uint4;
     field2 : list uint16 where length is uint8;
     field3 : string;
   }.

 (* define an arbitrary encode function corresponding a network protocol *)
 Definition SS_encode (s : SSRecord) : bin :=
   FixNat_encode (field1 s) ++
   List_encode (FixNat_encode) (field2 s) ++
   String_encode (field3 s).

 (* define a specification of the parse function *)
 Definition SS_parse :
   { parse : bin -> SSRecord | forall data, de (encode data) = data }.
 Proof.
   (* begin synthesis process *)
   solve_decode.
   (* finish! *)
 Defined.