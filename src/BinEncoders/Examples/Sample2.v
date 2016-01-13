Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Core
               Fiat.BinEncoders.Libraries.FixInt
               Fiat.BinEncoders.Libraries.List.

Set Implicit Arguments.

Section Sample2.

  Variable Nat_encode : nat -> bin.
  Variable Nat_pairencode : nat * bin -> bin.

  Global Instance Nat_decoder
    : decoder (fun _ => True) Nat_encode.
  Admitted.

  Global Instance Nat_pairdecoder
    : decoder (fun _ => True) Nat_pairencode.
  Admitted.

  Global Instance App_decoder2
         (A : Type)
         (encode_A : A -> bin)
         (A_Decoder : decoder (fun _ => True) encode_A)
    : decoder (fun _ => True)
              (fun _bundle : A * bin => let (_data, _bin) := _bundle in encode_A _data ++ _bin).
  Admitted.

  Global Instance App_decoder'
         (A : Type)
         (encode_A : A -> bin)
         (predicate : A -> Prop)
         (A_Decoder : decoder predicate encode_A)
    : decoder (fun data => predicate (fst data))
              (fun _bundle : A * bin => let (_data, _) := _bundle in encode_A _data).
  Admitted.

  Definition DepSS_encode (data : list nat) :=
    Nat_encode (length data) ++ (List_encode Nat_pairencode data).

  Definition DepSS_decode :
    { DepSS_decode | DepSS_encode <+> DepSS_decode }.
  Proof.
    unfold DepSS_encode.
    eexists.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (_ data) ++ @?e2 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _bin) := _bundle
                       in  e1 _proj ++ _bin)
           (encode2:=e2)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro len.


    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _) := _bundle
                       in  e1 _proj)
           (encode2:=fun _ => nil)
    end.
    instantiate (1:=fun data => length data = len).
    intuition. cbv beta.
    (* eapply decode_correct without the following line does not solve it. *)
    change (fun data : list nat * bin => length (fst data) = len) with
            (fun data : list nat * bin => (fun ls => length ls = len) (fst data)).
    eapply decode_correct. intro ls.

    unfold encode_decode_correct.
    intros.
    instantiate (1:=fun _ _ => _).
    simpl in *. intuition. subst. reflexivity.
  Defined.

End Sample2.
