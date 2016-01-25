Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Helpers
               Fiat.BinEncoders.Libraries.Sig
               Fiat.BinEncoders.Libraries.BinCore
               Fiat.BinEncoders.Libraries.FixInt
               Fiat.BinEncoders.Libraries.SteppingList
               Fiat.BinEncoders.Libraries.FixList
               Fiat.BinEncoders.Libraries.FixList2
               Fiat.BinEncoders.Libraries.Char
               Fiat.BinEncoders.Libraries.Bool
               Coq.Strings.Ascii.

Set Implicit Arguments.

Definition word_t := { s : list ascii | length s < exp2_nat 8 }.

Definition halt : word_t.
  refine (exist _ nil _).
  rewrite Compare_dec.nat_compare_lt; eauto.
Defined.

Definition halt_dec (a : word_t) : {a = halt} + {a <> halt}.
  unfold halt; destruct a as [word word_pf].
  destruct word eqn: eq; subst.
  - left. subst. eapply sig_equivalence. eauto.
  - right. intro. inversion H.
Defined.

Definition name_t := { s : list word_t | length s <= 255 /\ forall x, In x s -> x <> halt }.

Definition encode_word (bundle : word_t * bin_t) :=
  bin_encode_transform_pair (@FixInt_encode _) (FixList_getlength (fst bundle),
    FixList_encode (bin_encode_transform_pair Char_encode) bundle).

Global Instance word_decoder
  : decoder (fun _ => True) encode_word.
Proof.
  unfold encode_word.
  eapply decode_unpack.
  instantiate (1:=fun _ => True). intuition. cbv beta.
  eapply bin_encode_transform_pair_Decoder. eapply FixInt_encode_correct.
  intro proj.
  eapply strengthen_Decoder.
  eapply FixList_decoder with (size:=8) (len:=proj).
  instantiate (1:=fun _ => True). intuition. cbv beta.
  eapply bin_encode_transform_pair_Decoder. eapply Char_encode_correct.
  firstorder.
Defined.

Definition encode_name := @SteppingList_encode _ _ halt 255 encode_word.

Global Instance name_decoder
  : decoder (SteppingList_predicate (fun _ => True)) encode_name.
Proof.
  eapply SteppingList_decoder.
  eapply halt_dec.
  eapply word_decoder.
Defined.

Inductive type_t := A | CNAME | NS | MX.
Inductive class_t := IN | CH | HS.

Definition FixInt_of_type (t : type_t) : {n | (n < exp2 16)%N}.
  refine (match t with
          | A     => exist _ (1%N) _
          | CNAME => exist _ (5%N) _
          | NS    => exist _ (2%N) _
          | MX    => exist _ (15%N) _
          end); rewrite <- N.compare_lt_iff; eauto.
Defined.

Definition FixInt_of_class (c : class_t) : {n | (n < exp2 16)%N}.
  refine (match c with
          | IN => exist _ (1%N) _
          | CH => exist _ (3%N) _
          | HS => exist _ (4%N) _
          end); rewrite <- N.compare_lt_iff; eauto.
Defined.

Global Instance type_to_FixInt_decoder
  : decoder (fun _ => True) FixInt_of_type :=
  { decode := fun n => if N.eq_dec (proj1_sig n) (1%N) then A
                       else if N.eq_dec (proj1_sig n) (5%N) then CNAME
                       else if N.eq_dec (proj1_sig n) (2%N) then NS
                       else MX }.
Proof.
  intros data _; destruct data; eauto.
Defined.

Global Instance class_to_FixInt_decoder
  : decoder (fun _ => True) FixInt_of_class :=
  { decode := fun n => if N.eq_dec (proj1_sig n) (1%N) then IN
                       else if N.eq_dec (proj1_sig n) (3%N) then CH
                       else HS }.
Proof.
  intros data _; destruct data; eauto.
Defined.

Record question_t :=
  { qname : name_t;
    qtype : type_t;
    qclass : class_t }.

Definition encode_question (bundle : question_t * bin_t) :=
  encode_name (qname (fst bundle),
    bin_encode_transform_pair (@FixInt_encode _) (FixInt_of_type (qtype (fst bundle)),
      bin_encode_transform_pair (@FixInt_encode _) (FixInt_of_class (qclass (fst bundle)), snd bundle))).

Global Instance question_decoder
  : decoder (fun _ => True) encode_question.
Proof.
  unfold encode_question.

  eapply decode_unpack.
  instantiate (1:=fun ls => True /\ (forall x, In x (proj1_sig ls) -> True)). intuition. cbv beta.
  eapply name_decoder.
  intro.

  eapply decode_unpack with
    (encode1:=fun bundle => bin_encode_transform_pair (FixInt_encode (size:=16))
                              (FixInt_of_type (fst bundle), snd bundle))
    (encode2:=fun data => bin_encode_transform_pair (FixInt_encode (size:=16))
                            (FixInt_of_class (qclass (fst data)), snd data)).
  instantiate (1:=fun _ => True). intuition. cbv beta.
  eapply Nested_decoder with
    (encodeA:=fun data => (FixInt_of_type (fst data), snd data))
    (encodeB:=bin_encode_transform_pair (FixInt_encode (size:=16))).
  eapply Unprod_decoder. eapply type_to_FixInt_decoder.
  eapply bin_encode_transform_pair_Decoder. eapply FixInt_encode_correct.
  intro.

  eapply decode_unpack with
    (encode1:=fun bundle => bin_encode_transform_pair (FixInt_encode (size:=16))
                              (FixInt_of_class (fst bundle), snd bundle)).
  instantiate (1:=fun _ => True). intuition. cbv beta.
  eapply Nested_decoder with
    (encodeA:=fun data => (FixInt_of_class (fst data), snd data))
    (encodeB:=bin_encode_transform_pair (FixInt_encode (size:=16))).
  eapply Unprod_decoder. eapply class_to_FixInt_decoder.
  eapply bin_encode_transform_pair_Decoder. eapply FixInt_encode_correct.
  intro.

  eexists. instantiate (1:=fun b => (Build_question_t _ _ _, b)).
  intro. intuition. destruct data as [rdata bin]. destruct rdata. simpl in *. subst. eauto.
Defined.

Record packet_t :=
  { pid : { s : list bool | length s = 16 };
    pmask : { s : list bool | length s = 16 };
    pquestion : { s : list question_t | length s < exp2_nat 16 };
    panswer : { s : list question_t | length s < exp2_nat 16 };
    pauthority : { s : list question_t | length s < exp2_nat 16 };
    padditional : { s : list question_t | length s < exp2_nat 16 } }.

Definition encode_packet (bundle : packet_t * bin_t) :=
  FixList2_encode (bin_encode_transform_pair Bool_encode) (pid (fst bundle),
  FixList2_encode (bin_encode_transform_pair Bool_encode) (pmask (fst bundle),
  bin_encode_transform_pair (@FixInt_encode _) (FixList_getlength (pquestion (fst bundle)),
  bin_encode_transform_pair (@FixInt_encode _) (FixList_getlength (panswer (fst bundle)),
  bin_encode_transform_pair (@FixInt_encode _) (FixList_getlength (pauthority (fst bundle)),
  bin_encode_transform_pair (@FixInt_encode _) (FixList_getlength (padditional (fst bundle)),
  FixList_encode encode_question (pquestion (fst bundle),
  FixList_encode encode_question (panswer (fst bundle),
  FixList_encode encode_question (pauthority (fst bundle),
  FixList_encode encode_question (padditional (fst bundle), snd bundle)))))))))).

Global Instance packet_decoder
  : decoder (fun _ => True) encode_packet.
Proof.
  unfold encode_packet.

  eapply decode_unpack.
  instantiate (1:=fun ls => forall x, In x (proj1_sig ls) -> True). intuition. cbv beta.
  eapply FixList2_decoder.
  eapply bin_encode_transform_pair_Decoder. eapply Bool_encode_correct.
  intro.

  eapply decode_unpack.
  instantiate (1:=fun ls => forall x, In x (proj1_sig ls) -> True). intuition. cbv beta.
  eapply FixList2_decoder.
  eapply bin_encode_transform_pair_Decoder. eapply Bool_encode_correct.
  intro.

  eapply decode_unpack.
  instantiate (1:=fun _ => True). intuition. cbv beta.
  eapply bin_encode_transform_pair_Decoder. eapply FixInt_encode_correct.
  intro.

  eapply decode_unpack.
  instantiate (1:=fun _ => True). intuition. cbv beta.
  eapply bin_encode_transform_pair_Decoder. eapply FixInt_encode_correct.
  intro.

  eapply decode_unpack.
  instantiate (1:=fun _ => True). intuition. cbv beta.
  eapply bin_encode_transform_pair_Decoder. eapply FixInt_encode_correct.
  intro.

  eapply decode_unpack.
  instantiate (1:=fun _ => True). intuition. cbv beta.
  eapply bin_encode_transform_pair_Decoder. eapply FixInt_encode_correct.
  intro.

  eapply decode_unpack with
    (encode1:=FixList_encode encode_question).
  instantiate (1:=fun data => FixList_getlength data = proj1 /\
                              forall x, In x (proj1_sig data) -> True). intuition. cbv beta.
  eapply FixList_decoder.
  eapply question_decoder.
  intro.
  eapply decode_unpack with
    (encode1:=FixList_encode encode_question).
  instantiate (1:=fun data => FixList_getlength data = proj2 /\
                              forall x, In x (proj1_sig data) -> True). intuition. cbv beta.
  eapply FixList_decoder.
  eapply question_decoder.
  intro.
  eapply decode_unpack with
    (encode1:=FixList_encode encode_question).
  instantiate (1:=fun data => FixList_getlength data = proj3 /\
                              forall x, In x (proj1_sig data) -> True). intuition. cbv beta.
  eapply FixList_decoder.
  eapply question_decoder.
  intro.
  eapply decode_unpack with
    (encode1:=FixList_encode encode_question).
  instantiate (1:=fun data => FixList_getlength data = proj4 /\
                              forall x, In x (proj1_sig data) -> True). intuition. cbv beta.
  eapply FixList_decoder.
  eapply question_decoder.
  intro.

  eexists. instantiate (1:=fun b => (Build_packet_t _ _ _ _ _ _, b)).
  intro. intuition. destruct data as [rdata bin]. destruct rdata. simpl in *. subst. eauto.
Defined.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive ascii => char [
"(* If this appears, you're using Ascii internals. Please don't *) (fun (b0,b1,b2,b3,b4,b5,b6,b7) → let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(* If this appears, you're using Ascii internals. Please don't *) (fun f c → let n = Char.code c in let h i = (n land (1 lsl i)) ≠ 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".
Recursive Extraction packet_decoder.