Require Import Fiat.BinEncoders.NoEnv.Specs.

Set Implicit Arguments.

Global Instance unpacking_decoder
       (data_t : Type)
       (bin_t  : Type)
       (proj_t : Type)
       (project : data_t -> proj_t)
       (predicate  : data_t -> Prop)
       (predicate' : proj_t -> Prop)
       (encode1 : proj_t * bin_t -> bin_t)
       (encode2 : data_t -> bin_t)
       (decoder1 : decoder (fun data => predicate' (fst data)) encode1)
       (pred_pf : forall data, predicate data -> predicate' (project data))
       (decoder2 : forall proj, decoder (fun data => predicate data /\ project data = proj) encode2)
: decoder predicate (fun data => encode1 (project data, encode2 data)) :=
    { decode := fun bin => let (proj, ext) := @decode _ _ _ _ decoder1 bin
                           in  @decode _ _ _ _ (decoder2 proj) ext }.
Proof.
  unfold encode_decode_correct.
  destruct decoder1 as [ decode1 decode1_pf ]. simpl.
  intros data pred.
  destruct (decode1 (encode1 (project data, encode2 data))) as [_proj _bin] eqn: eq.
  rewrite decode1_pf in eq; [ | eapply pred_pf; eauto ].
  destruct (decoder2 _proj) as [ decode2 decode2_pf ]. simpl.
  inversion eq; subst.
  rewrite decode2_pf; eauto.
Defined.

Global Instance strengthening_decoder
       (data_t : Type)
       (bin_t : Type)
       (predicate : data_t -> Prop)
       (predicate' : data_t -> Prop)
       (encode_data : data_t -> bin_t)
       (data_decoder : decoder predicate encode_data)
       (predicate_pf : forall data, predicate' data -> predicate data)
  : decoder predicate' encode_data :=
  { decode := @decode _ _ _ _ data_decoder }.
Proof.
  destruct data_decoder.
  unfold encode_decode_correct in *. eauto.
Defined.

Global Instance nesting_decoder A B C
       (encodeA : A -> B)
       (encodeB : B -> C)
       (A_decoder : decoder (fun _ => True) encodeA)
       (B_decoder : decoder (fun _ => True) encodeB)
  : decoder (fun _ => True) (fun a => encodeB (encodeA a)) :=
  { decode := fun c => @decode _ _ _ _ A_decoder (@decode _ _ _ _ B_decoder c);
    decode_correct := _ }.
Proof.
  intros data _.
  repeat rewrite decode_correct; eauto.
Defined.

Global Instance unproding_decoder A B Z
       (encodeA : A -> B)
       (A_decoder : decoder (fun _ => True) encodeA)
  : decoder (fun _ => True) (fun bundle : A * Z => (encodeA (fst bundle), snd bundle)) :=
  { decode := fun bundle : B * Z => (@decode _ _ _ _ A_decoder (fst bundle), snd bundle);
    decode_correct := _ }.
Proof.
  intros [data_a data_z] _. f_equal; eauto; simpl.
  rewrite decode_correct; eauto.
Defined.