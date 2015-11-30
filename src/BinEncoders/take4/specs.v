Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

Set Implicit Arguments.

Definition bin := list bool.

(* Notation "encode ⇹ decode" := *)
Notation "encode <+> decode" :=
  (forall data, decode (encode data) = data)
    (at level 20, no associativity).

(* Notation "encode ⇼ decode" := *)
Notation "encode <++> decode" :=
  (forall data ext, decode (encode data ++ ext) = (data, ext))
    (at level 20, no associativity).

Notation "<$ decode" :=
  (forall bin, length (snd (decode bin)) <= pred (length bin))
    (at level 20, no associativity).

Class decoder
      (A : Type)
      (encode : A -> bin) :=
  { decode : bin -> A;
    decode_correct : encode <+> decode }.

Class decoder_block
      (A : Type)
      (encode : A -> bin) :=
  { decode_block : bin -> A * bin;
    decode_block_app : encode <++> decode_block;
    decode_block_wellfounded  : <$ decode_block }.

Fixpoint exp2 (n : nat) :=
  match n with
  | O => S O
  | S n' => exp2 n' + exp2 n'
  end.

Variable FixNat_encode : forall size, {n | n < exp2 size} -> bin.

Global Instance FixNat_decoder
       (size : nat)
  : decoder_block (FixNat_encode size). Admitted.

Variable List1_encode :
  forall (A : Type) (encode_A : A -> bin) (size : nat),
    {ls : list A | length ls < exp2 size} -> bin.

Global Instance List1_decoder
       (size : nat)
       (A : Type)
       (encode_A : A -> bin)
       (A_Decoder : decoder_block encode_A)
  : decoder_block (List1_encode encode_A size). Admitted.

Record SSRecord :=
  { field1 : { n | n < exp2 4 };
    field2 : { ls : list { n | n < exp2 16 } | length ls < exp2 8 };
    field3 : { n | n < exp2 2 } }.

Definition SS_encode (s : SSRecord) :=
  FixNat_encode _ (field1 s) ++
  List1_encode (FixNat_encode _) _ (field2 s) ++
  FixNat_encode _ (field3 s).

Lemma decode_app_l (data_t proj_t prev_t : Type) :
  forall (prev : data_t -> prev_t)
         (proj : data_t -> proj_t)
         (encode1 : proj_t -> bin)
         (encode2 : data_t -> bin),
  { decode : prev_t -> bin -> proj_t * bin |
      forall data ext,
        decode (prev data) (encode1 (proj data) ++ ext) = (proj data, ext) } ->
  { decode : prev_t * proj_t -> bin -> data_t * bin |
      forall data ext,
        decode (prev data, proj data) (encode2 data ++ ext) = (data, ext) } ->
  { decode : prev_t -> bin -> data_t * bin |
      forall data ext,
        decode (prev data) (encode1 (proj data) ++ (encode2 data) ++ ext) =
        (data, ext) }.
Proof.
Admitted.

Lemma decode_inject_unit (T : Type) (P : T -> Prop) :
  { decode : unit -> T | P (decode tt) } -> { decode : T | P decode }.
Proof.
Admitted.

Lemma decode_resolve_hyp (data_t proj_t prev_t goal_t : Type) :
  forall (prev : data_t -> prev_t)
         (proj : data_t -> proj_t)
         (goal : data_t -> goal_t)
         (encode : proj_t -> bin),
  { constr : prev_t -> proj_t -> goal_t |
      forall data, constr (prev data) (proj data) = goal data } ->
  { decode : bin -> proj_t * bin |
      forall data ext, decode (encode data ++ ext) = (data, ext) } ->
  { decode : prev_t -> bin -> goal_t * bin |
      forall data ext,
        decode (prev data) (encode (proj data) ++ ext) = (goal data, ext) }.
Proof.
Admitted.

Lemma decode_generalize (data_t : Type) :
  forall (encode : data_t -> bin),
    { decode | encode <++> decode } -> { decode | encode <+> decode }.
Proof.
Admitted.

Lemma sig_rewrite (T : Type) (P P' : T -> Prop) :
  P = P' ->
  { x | P x } = { x | P' x }.
Proof.
Admitted.

Definition SS_decode :
  { decode : bin -> SSRecord | forall data, decode (SS_encode data) = data }.
Proof.
  unfold SS_encode.

  eapply decode_generalize.
  eapply decode_inject_unit.

  (* rewrite sig_rewrite with
    (P:=fun decode =>
           forall data ext, decode tt
             ((FixNat_encode 4 (field1 data) ++
               List1_encode (FixNat_encode 16) 8 (field2 data) ++
               FixNat_encode 2 (field3 data)) ++ ext) = (data, ext))
    (P':=fun decode =>
           forall data ext, decode tt
             ((FixNat_encode 4 (field1 data)) ++
               (List1_encode (FixNat_encode 16) 8 (field2 data) ++
                FixNat_encode 2 (field3 data) ++ ext)) = (data, ext)). *)
  assert ({decode0 : unit -> list bool -> SSRecord * list bool |
           forall (data : SSRecord) (ext : list bool),
             decode0 tt
                     (FixNat_encode 4 (field1 data) ++
                      (List1_encode (FixNat_encode 16) 8 (field2 data) ++
                       FixNat_encode 2 (field3 data)) ++ ext) = (data, ext)}).
  Focus 2. admit.

  eapply decode_app_l.

  eapply decode_resolve_hyp.
  eexists. intros. instantiate (1:=fun _ x => x). reflexivity.
  eexists. intros. eapply decode_block_app.

  assert ({decode : unit * {n : nat | n < exp2 4} -> bin -> SSRecord * bin |
           forall (data : SSRecord) (ext : list bool),
             decode (tt, field1 data)
                     (List1_encode (FixNat_encode 16) 8 (field2 data) ++
                      FixNat_encode 2 (field3 data) ++ ext) = (data, ext)}).
  Focus 2. admit.

  eapply decode_app_l.

  eapply decode_resolve_hyp.
  eexists. intros. instantiate (1:=fun _ x => x). reflexivity.
  eexists. intros. eapply decode_block_app.

  eapply decode_resolve_hyp.
  eexists. intros. instantiate (1:=fun prev proj =>
                                     let (prev', f2) := prev in
                                     let (_, f1)     := prev' in
                                     Build_SSRecord f1 f2 proj).
  destruct data; reflexivity.
  eexists. intros. eapply decode_block_app.
Defined.