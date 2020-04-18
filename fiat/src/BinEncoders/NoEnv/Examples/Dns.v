Require Import Fiat.BinEncoders.NoEnv.Specs
               Fiat.BinEncoders.NoEnv.Libraries.Helpers
               Fiat.BinEncoders.NoEnv.Libraries.Sig
               Fiat.BinEncoders.NoEnv.Libraries.BinCore
               Fiat.BinEncoders.NoEnv.Libraries.FixInt
               Fiat.BinEncoders.NoEnv.Libraries.SteppingList
               Fiat.BinEncoders.NoEnv.Libraries.FixList
               Fiat.BinEncoders.NoEnv.Libraries.FixList2
               Fiat.BinEncoders.NoEnv.Libraries.Char
               Fiat.BinEncoders.NoEnv.Libraries.Bool
               Fiat.BinEncoders.NoEnv.Automation.Solver
               Coq.Strings.Ascii.

Set Implicit Arguments.

Inductive type_t := A | CNAME | NS | MX.
Inductive class_t := IN | CH | HS.

Record word_t :=
  { word_attr : { s : list ascii | length s < exp2_nat 8 } }.

Definition halt : word_t.
  refine (Build_word_t (exist _ nil _)); rewrite Compare_dec.nat_compare_lt; eauto. Defined.

Definition halt_dec (a : word_t) : {a = halt} + {a <> halt}.
  unfold halt; destruct a as [word word_pf];
  destruct word as [ w ]; destruct w eqn: eq; subst.
  - left; subst; f_equal; eapply sig_equivalence; eauto.
  - right; inversion 1.
Defined. Hint Resolve halt_dec.

Record name_t :=
  { name_attr : { s : list word_t | length s <= 255 /\ forall x, In x s -> x <> halt } }.

Record question_t :=
  { qname  : name_t;
    qtype  : type_t;
    qclass : class_t }.

Record resource_t :=
  { rname  : name_t;
    rtype  : type_t;
    rclass : class_t;
    rttl   : uint 32;
    rdata  : { s : list bool |  length s < exp2_nat 16 } }.

Record packet_t :=
  { pid         : { s : list bool | length s = 16 };
    pmask       : { s : list bool | length s = 16 };
    pquestion   : { s : list question_t | length s < exp2_nat 16 };
    panswer     : { s : list resource_t | length s < exp2_nat 16 };
    pauthority  : { s : list resource_t | length s < exp2_nat 16 };
    padditional : { s : list resource_t | length s < exp2_nat 16 } }.

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

Definition encode_word (bundle : word_t * bin_t) :=
  FixInt_encode (FixList_getlength (word_attr (fst bundle)),
  FixList_encode Char_encode (word_attr (fst bundle), snd bundle)).

Definition encode_name (bundle : name_t * bin_t) :=
  @SteppingList_encode _ _ halt _ encode_word (name_attr (fst bundle), snd bundle).

Definition encode_question (bundle : question_t * bin_t) :=
  encode_name (qname (fst bundle),
  FixInt_encode (FixInt_of_type (qtype (fst bundle)),
  FixInt_encode (FixInt_of_class (qclass (fst bundle)), snd bundle))).

Definition encode_resource (bundle : resource_t * bin_t) :=
  encode_name (rname (fst bundle),
  FixInt_encode (FixInt_of_type (rtype (fst bundle)),
  FixInt_encode (FixInt_of_class (rclass (fst bundle)),
  FixInt_encode (rttl (fst bundle),
  FixInt_encode (FixList_getlength (rdata (fst bundle)),
  FixList_encode Bool_encode (rdata (fst bundle), snd bundle)))))).

Definition encode_packet (bundle : packet_t * bin_t) :=
  FixList2_encode Bool_encode (pid (fst bundle),
  FixList2_encode Bool_encode (pmask (fst bundle),
  FixInt_encode (FixList_getlength (pquestion (fst bundle)),
  FixInt_encode (FixList_getlength (panswer (fst bundle)),
  FixInt_encode (FixList_getlength (pauthority (fst bundle)),
  FixInt_encode (FixList_getlength (padditional (fst bundle)),
  FixList_encode encode_question (pquestion (fst bundle),
  FixList_encode encode_resource (panswer (fst bundle),
  FixList_encode encode_resource (pauthority (fst bundle),
  FixList_encode encode_resource (padditional (fst bundle), snd bundle)))))))))).

Global Instance packet_decoder
  : Decoder of encode_packet.
Proof.
  decoder_from_encoder.
Defined.

Section Example.
  Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..).
  Definition packet1 := [true; true; false; true; true; false; true; true; false; true;
                         false; false; false; false; true; false; false; false; false; false;
                         false; false; false; true; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; true; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; true; true; false; true; true; true; false; true;
                         true; true; false; true; true; true; false; true; true; true;
                         false; true; true; true; false; true; true; true; false; false;
                         false; false; true; true; false; false; false; true; true; false;
                         true; true; true; false; false; true; true; false; true; true;
                         true; true; false; true; true; true; false; false; true; false;
                         false; true; true; true; false; true; false; false; false; true;
                         true; false; true; false; false; false; false; true; true; false;
                         false; true; false; true; false; true; true; false; false; false;
                         false; true; false; true; true; true; false; false; true; true;
                         false; true; true; true; false; true; false; false; false; true;
                         true; false; false; true; false; true; false; true; true; true;
                         false; false; true; false; false; true; true; false; true; true;
                         true; false; false; false; false; false; false; false; true; true;
                         false; true; true; false; false; true; false; true; false; true;
                         true; false; false; true; false; false; false; true; true; true;
                         false; true; false; true; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; false; false; false; false; true; false; false;
                         false; false; false; false; false; false; false; false; false; false;
                         false; false; false; true].
End Example.


Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive ascii => char [
"(fun (b0,b1,b2,b3,b4,b5,b6,b7) -> let f b i = if b then 1 lsl i else 0 in Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))"
]
"(fun f c -> let n = Char.code c in let h i = (n land (1 lsl i)) <> 0 in f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))".

(*Print packet_decoder.
Extraction "extracted.ml" encode_packet packet_decoder packet1.*)
