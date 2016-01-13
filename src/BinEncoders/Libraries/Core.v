Require Import Fiat.BinEncoders.Specs.

Definition bin := list bool.

Section Lemmas.

  Lemma decode_unpack
         (data_t : Type)
         (bin_t  : Type)
         (proj_t : Type) :
    forall (project : data_t -> proj_t)
           (predicate  : data_t -> Prop)
           (predicate' : proj_t -> Prop)
           (encode1 : proj_t * bin_t -> bin_t)
           (encode2 : data_t -> bin_t)
           (decode1 : bin_t -> proj_t * bin_t)
           (decode2 : proj_t -> bin_t -> data_t),
      (forall data, predicate data -> predicate' (project data)) ->
      (encode_decode_correct
         (fun data => predicate' (fst data)) encode1 decode1) ->
      (forall proj,
          encode_decode_correct
            (fun data => predicate data /\ project data = proj) encode2 (decode2 proj)) ->
      (encode_decode_correct
         predicate
         (fun data => encode1 (project data, encode2 data))
         (fun bin  => let (_proj, _bin) := decode1 bin
                      in  decode2 _proj _bin)).
  Proof.
    unfold encode_decode_correct.
    intros project predicate predicate' encode1 encode2 decode1 decode2
           predicate_pf decode1_pf decode2_pf data pred.
    destruct (decode1 (encode1 (project data, encode2 data))) as [_proj _bin] eqn: eq.
    specialize (decode1_pf (project data, encode2 data)).
    specialize (decode2_pf _proj data).
    rewrite decode1_pf in eq; [ | eapply predicate_pf; eauto ].
    rewrite <- decode2_pf.
    inversion eq. eauto. inversion eq. eauto.
  Qed.

End Lemmas.
