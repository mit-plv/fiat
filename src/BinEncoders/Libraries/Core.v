Require Import Fiat.BinEncoders.Specs.

Definition bin := list bool.

Section Instances.

  Global Instance Nested_decoder A B C
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

  Global Instance Unprod_decoder A
         (encodeP : A * bin -> bin)
         (P_decoder : decoder (fun _ => True) encodeP)
    : decoder (fun _ => True) (fun a => encodeP (a, nil)) :=
    { decode := fun b => fst (@decode _ _ _ _ P_decoder b);
      decode_correct := _ }.
  Proof.
    intros data _.
    rewrite decode_correct; eauto.
  Defined.
(*
  Global Instance Unprod_decoder2 A B
         (encodeA : A -> bin)
         (A_decoder : decoder (fun _ => True) encodeA)
    : decoder (fun _ => True) (fun _bundle : A * B => let (_a, _) := _bundle in encodeA _a) :=
    { decode := fun b

(fun _bundle : RRecordClass * bin =>
    let (_proj, _) := _bundle in
    FixInt_encode 16 (RRecordClassToFixInt _proj)) <+>
   ?222*)


End Instances.

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

  Lemma decode_moveproj
         (data_t : Type)
         (bin_t  : Type)
         (proj_t : Type) :
    forall (project : data_t -> proj_t)
           (predicate  : data_t -> Prop)
           (predicate' : proj_t -> Prop)
           (encode : proj_t -> bin_t)
           (decode : bin_t -> proj_t)
           (constr : proj_t -> data_t),
      (forall data, predicate data -> predicate' (project data)) ->
      (encode_decode_correct
         (fun data => predicate' data) encode decode) ->
      (forall proj,
          forall data, predicate data /\ project data = proj -> constr proj = data) ->
      (encode_decode_correct
         predicate
         (fun data => encode (project data))
         (fun bin  => constr (decode bin))).
  Proof.
    unfold encode_decode_correct.
    intros project predicate predicate' encode decode constr
           predicate_pf decode_pf constr_pf data pred.
    eapply constr_pf; intuition eauto.
    rewrite decode_pf; eauto.
  Qed.

End Lemmas.
