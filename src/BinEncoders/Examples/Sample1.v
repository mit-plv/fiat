Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Core
               Fiat.BinEncoders.Libraries.FixInt.

Set Implicit Arguments.

Section Sample1.

  Variable List_encode : forall (A : Type) (encode_A : A -> bin), list A -> bin.

  Global Instance List_decoder
         (A : Type)
         (encode_A : A -> bin)
         (A_Decoder : decoder (fun _ => True) encode_A)
    : decoder (fun _ => True) (List_encode encode_A).
  Admitted.

  Global Instance App_decoder
         (A : Type)
         (encode_A : A -> bin)
         (A_Decoder : decoder (fun _ => True) encode_A)
    : decoder (fun _ => True)
              (fun _bundle : A * bin => let (_data, _bin) := _bundle in encode_A _data ++ _bin).
  Admitted.

  Global Instance App_decoder'
         (A : Type)
         (encode_A : A -> bin)
         (A_Decoder : decoder (fun _ => True) encode_A)
    : decoder (fun _ => True)
              (fun _bundle : A * bin => let (_data, _) := _bundle in encode_A _data).
  Admitted.

  Record SSRecord :=
    { field1 : { n | N.lt n (exp2 4) };
      field2 : list {n | N.lt n (exp2 3)};
      field3 : { n | N.lt n (exp2 2) } }.

  Definition SS_encode (data : SSRecord) :=
   FixInt_encode _ (field1 data) ++
   List_encode (FixInt_encode _) (field2 data) ++
   FixInt_encode _ (field3 data).

  Definition SS_decode :
    { SS_decode | SS_encode <+> SS_decode }.
  Proof.
    unfold SS_encode.
    eexists.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (_ data) ++ @?e2 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _bin) := _bundle
                       in  e1 _proj ++ _bin)
           (encode2:=e2)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro f1.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (_ data) ++ @?e2 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _bin) := _bundle
                       in  e1 _proj ++ _bin)
           (encode2:=e2)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro f2.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (_ data)) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _) := _bundle
                       in  e1 _proj)
           (encode2:=fun _ => nil)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro f3.

    unfold encode_decode_correct.
    intros. destruct data.
    instantiate (1:=fun _ _ => Build_SSRecord _ _ _). simpl.
    simpl in *. intuition. subst. reflexivity.
  Defined.

End Sample1.
