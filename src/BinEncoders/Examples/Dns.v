Require Import Coq.Strings.String
               Coq.Bool.Bvector.
Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Core
               Fiat.BinEncoders.Libraries.FixInt
               Fiat.BinEncoders.Libraries.Char
               Fiat.BinEncoders.Libraries.VList.

Set Implicit Arguments.

Section DnsPacket.

  Inductive RRecordType := A | CNAME | NS | MX.
  Inductive RRecordClass := IN | CH | HS.

  (* find a way to do this systematically *)
  Definition RRecordTypeToFixInt (t : RRecordType) : {n | (n < exp2 16)%N}.
    refine (match t with
            | A     => exist _ (1%N) _
            | CNAME => exist _ (5%N) _
            | NS    => exist _ (2%N) _
            | MX    => exist _ (15%N) _
            end); rewrite <- N.compare_lt_iff; eauto.
  Defined.

  Definition RRecordClassToFixInt (c : RRecordClass) : {n | (n < exp2 16)%N}.
    refine (match c with
            | IN => exist _ (1%N) _
            | CH => exist _ (3%N) _
            | HS => exist _ (4%N) _
            end); rewrite <- N.compare_lt_iff; eauto.
  Defined.

  Global Instance RRType_decoder
    : decoder (fun _ => True) RRecordTypeToFixInt :=
    { decode := fun n => if N.eq_dec (proj1_sig n) (1%N) then A
                         else if N.eq_dec (proj1_sig n) (5%N) then CNAME
                         else if N.eq_dec (proj1_sig n) (2%N) then NS
                         else MX;
      decode_correct := _ }.
  Proof.
    intros data _; destruct data; eauto.
  Defined.

  Global Instance RRClass_decoder
    : decoder (fun _ => True) RRecordClassToFixInt :=
    { decode := fun n => if N.eq_dec (proj1_sig n) (1%N) then IN
                         else if N.eq_dec (proj1_sig n) (3%N) then CH
                         else HS;
      decode_correct := _ }.
  Proof.
    intros data _; destruct data; eauto.
  Defined.


  Record question :=
    { qname : list (list ascii);
      qtype : RRecordType;
      qclass : RRecordClass }.

  Global Instance App_decoder
         (A : Type)
         (encode_A : A -> bin)
         (A_Decoder : decoder (fun _ => True) encode_A)
    : decoder (fun _ => True)
              (fun _bundle : A * bin => let (_data, _bin) := _bundle in encode_A _data ++ _bin).
  Admitted.

  Definition question_encode (q : question) :=
    VList_encode (VList_encode_pair Char_encode_pair) (qname q) ++
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
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro.

    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (?p1 (_ data)) ++ @?e2 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _bin) := _bundle
                       in  e1 (p1 _proj) ++ _bin)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro.

    (* final step! *)
    eapply decode_moveproj with
      (encode:=fun c => FixInt_encode 16 (RRecordClassToFixInt c))
      (constr:=fun _ => Build_question _ _ _).
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro.
    intros. destruct data.
    intuition. simpl in *. subst. reflexivity.

    (*
    match goal with
    | |- encode_decode_correct _ (fun data => ?e1 (?p1 (_ data)) ++ @?e2 data) _ =>
        eapply decode_unpack with
           (encode1:=fun (_bundle : _ * bin) =>
                       let (_proj, _bin) := _bundle
                       in  e1 (p1 _proj) ++ _bin)
    end.
    instantiate (1:=fun _ => True). intuition. cbv beta. eapply decode_correct. intro.
    unfold encode_decode_correct.
    intros. destruct data.
    instantiate (1:=fun _ _ => Build_question _ _ _). simpl.
    simpl in *. intuition. subst. reflexivity. *)

  Defined.

  Record packet :=
    { id : Bvector 16;
      flags : Bvector 16;
      questions : list question;
      answers : list question;
      authority : list question;
      additional : list question }.

End DnsPacket.
