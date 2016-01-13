Load Helpers.

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


Variable a b c : bin.
Check ((a ++ b) ++ c).
Check (a ++ (b ++ c)).

Definition SS_decode :
  { decode : bin -> SSRecord | SS_encode <+> decode }.
Proof.
  unfold SS_encode.

  eexists.
  eapply decode_generalize'.
(*
  Set Printing Implicit. idtac.
*)
  (* setoid_rewrite <- app_assoc. *)
  eapply decode_app_l.

  eapply decode_resolve_hyp.
  eexists; intros; instantiate (1:=fun _ x => x); reflexivity.
  eexists; intros; eapply decode_block_app.

  eapply decode_app_assoc.
  eapply decode_app_l.

  eapply decode_resolve_hyp.
  eexists; intros; instantiate (1:=fun _ x => x); reflexivity.
  eexists; intros; eapply decode_block_app.

  eapply decode_resolve_hyp.
  eexists; intros; instantiate (1:=fun prev proj =>
                                     let (prev', f2) := prev in
                                     let (_, f1)     := prev' in
                                     Build_SSRecord f1 f2 proj).
  destruct data; reflexivity.
  eexists; intros; eapply decode_block_app.
Defined.

Extraction SS_decode.

Goal forall x, (proj1_sig SS_decode) = x.
unfold proj1_sig. simpl. unfold SS_decode. simpl.