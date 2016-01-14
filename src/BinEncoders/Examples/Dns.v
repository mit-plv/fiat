Require Import Coq.Strings.String
               Coq.Bool.Bvector.
Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Core
               Fiat.BinEncoders.Libraries.FixInt
               Fiat.BinEncoders.Libraries.Char.

Set Implicit Arguments.

Section DnsPacket.

  Variable List_encode : forall (A : Type) (encode_A : A -> bin), list A -> bin.

  Inductive RRecordType := A | CNAME | NS | MX.
  Inductive RRecordClass := IN | CH | HS.

  Record question :=
    { qname : list (list ascii);
      qtype : RRecordType;
      qclass : RRecordClass }.

  Definition RRecordTypeToFixInt (t : RRecordType) : {n | (n < exp2 16)%N}.
    refine (match t with
            | A     => exist _ (1%N) _
            | CNAME => exist _ (5%N) _
            | NS    => exist _ (2%N) _
            | MX    => exist _ (15%N) _
            end); admit.
  Defined.

  Definition RRecordClassToFixInt (c : RRecordClass) : {n | (n < exp2 16)%N}.
    refine (match c with
            | IN => exist _ (1%N) _
            | CH => exist _ (3%N) _
            | HS => exist _ (4%N) _
            end); admit.
  Defined.

  Global Instance T_decoder
    : decoder (fun _ => True) RRecordTypeToFixInt.
  Admitted.

  Global Instance C_decoder
    : decoder (fun _ => True) RRecordClassToFixInt.
  Admitted.

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

  Global Instance NestedDecoder A B C
         (encodeA : A -> B)
         (encodeB : B -> C)
         (A_decoder : decoder (fun _ => True) encodeA)
         (B_decoder : decoder (fun _ => True) encodeB)
    : decoder (fun _ => True) (fun data => encodeB (encodeA data)).
  Admitted.

  Definition question_encode (q : question) :=
    List_encode (List_encode Char_encode) (qname q) ++
    FixInt_encode _ (RRecordTypeToFixInt (qtype q)) ++
    FixInt_encode _ (RRecordClassToFixInt (qclass q)).

  Definition question_decode :
    { question_decode | question_encode <+> question_decode }.
  Proof.
    unfold question_encode.
    eexists.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (_ data) ++ @?e2 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _bin) := _bundle
                       in  e1 _proj ++ _bin)
           (encode2:=e2)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (?p1 (qtype data)) ++ @?e2 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _bin) := _bundle
                       in  e1 (p1 _proj) ++ _bin)
           (encode2:=e2)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (?p1 (qclass data))) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _) := _bundle
                       in  e1 (p1 _proj))
           (encode2:=fun _ => nil)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro.

    unfold encode_decode_correct.
    intros. destruct data.
    instantiate (1:=fun _ _ => Build_question _ _ _). simpl.
    simpl in *. intuition. subst. reflexivity.
  Defined.

  Record packet :=
    { id : Bvector 16;
      flags : Bvector 16;
      questions : nat;
      answers : nat;
      authority : list nat;
      additional : list nat }.

End DnsPacket.
