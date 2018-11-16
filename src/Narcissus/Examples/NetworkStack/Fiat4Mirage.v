Require Import Fiat.Narcissus.Examples.NetworkStack.TestInfrastructure.

(* Require Import *)
(*         Fiat.Narcissus.BinLib.AlignedDecodeMonad *)
(*         Fiat.Narcissus.BinLib.AlignedEncodeMonad. *)

Open Scope string_scope.

Require Import Fiat.Common.EnumType.

Section Ethernet.
  Inductive fiat_ethernet_type := ARP | IP | IPV6 | RARP.

  Definition fiat_ethernet_type_of_enum (enum: EnumType ["ARP"; "IP"; "IPV6"; "RARP"]) : fiat_ethernet_type :=
    InjectEnum [ARP; IP; IPV6; RARP] enum.

  Definition fiat_ethernet_type_to_enum (type: fiat_ethernet_type) : EnumType ["ARP"; "IP"; "IPV6"; "RARP"] :=
    match type with
    | ARP => ```"ARP"
    | IP => ```"IP"
    | IPV6 => ```"IPV6"
    | RARP => ```"RARP"
    end.
End Ethernet.

Section ARP.
  Inductive fiat_arp_hardtype := Ethernet | IEEE802 | Chaos.
  Definition fiat_arp_hardtype_of_enum (enum: EnumType ["Ethernet"; "IEEE802"; "Chaos"]) :=
    InjectEnum [Ethernet; IEEE802; Chaos] enum.
  Definition fiat_arp_hardtype_to_enum (hardtype: fiat_arp_hardtype)
    : EnumType ["Ethernet"; "IEEE802"; "Chaos"] :=
    match hardtype with
    | Ethernet => ```"Ethernet"
    | IEEE802 => ```"IEEE802"
    | Chaos => ```"Chaos"
    end.

  Inductive fiat_arp_prottype := IPv4 | IPv6.
  Definition fiat_arp_prottype_of_enum (enum: EnumType ["IPv4"; "IPv6"]) :=
    InjectEnum [IPv4; IPv6] enum.
  Definition fiat_arp_prottype_to_enum (prottype: fiat_arp_prottype)
    : EnumType ["IPv4"; "IPv6"] :=
    match prottype with
    | IPv4 => ```"IPv4"
    | IPv6 => ```"IPv6"
    end.

  Inductive fiat_arp_operation := Request | Reply | RARPRequest | RARPReply.
  Definition fiat_arp_operation_of_enum (enum: EnumType ["Request"; "Reply"; "RARPRequest"; "RARPReply"]) :=
    InjectEnum [Request; Reply; RARPRequest; RARPReply] enum.
  Definition fiat_arp_operation_to_enum (operation: fiat_arp_operation)
    : EnumType ["Request"; "Reply"; "RARPRequest"; "RARPReply"] :=
    match operation with
    | Request => ```"Request"
    | Reply => ```"Reply"
    | RARPRequest => ```"RARPRequest"
    | RARPReply => ```"RARPReply"
    end.
End ARP.

Section IPv4.
  Inductive fiat_ipv4_protocol :=
  | ICMP | TCP | UDP.
  Definition fiat_ipv4_protocol_of_enum (proto: EnumType ["ICMP"; "TCP"; "UDP"]) : fiat_ipv4_protocol :=
    InjectEnum [ICMP; TCP; UDP] proto.
  Definition fiat_ipv4_protocol_to_enum (proto: fiat_ipv4_protocol)
    : EnumType ["ICMP"; "TCP"; "UDP"] :=
    match proto with
    | ICMP => ```"ICMP"
    | TCP => ```"TCP"
    | UDP => ```"UDP"
    end.
End IPv4.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.

(* Work around the fact that Decimal declares a type "int" *)
Extract Inductive nat => "OCamlNativeInt.t" [ "0" "Pervasives.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive prod => "(*)"  [ "(,)" ].

Extract Inlined Constant NPeano.ltb => "(<)".
Extract Inlined Constant NPeano.leb => "(<=)".
(* ExtrOCamlNatInt uses Pervasives.max, which is slow *)
Extract Constant Nat.sub =>
  "fun (x: OCamlNativeInt.t) (y: OCamlNativeInt.t) ->
if x <= y then 0 else (x - y)".

(** * Inline a few functions *)
Require Import
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedEncodeMonad.
Extraction Inline fst snd Basics.compose.
Extraction Inline AlignedEncodeMonad.Projection_AlignedEncodeM.
Extraction Inline BindAlignedDecodeM ReturnAlignedDecodeM ThrowAlignedDecodeM.
Extraction Inline AppendAlignedEncodeM ReturnAlignedEncodeM ThrowAlignedEncodeM.
Extraction Inline Common.If_Opt_Then_Else AlignedDecoders.LetIn_If_Opt_Then_Else.

(** * Extract words as int64
      (Only works for words with length < 64) *)

Extract Inductive Word.word =>
"Int64Word.t"
  ["(Int64Word.w0)" "Int64Word.ws"]
  "Int64Word.destruct".

Extract Inlined Constant whd => "Int64Word.whd".
Extract Inlined Constant wtl => "Int64Word.wtl".
Extract Inlined Constant zext => "Int64Word.zext".
Extract Inlined Constant wplus => "Int64Word.wplus".
Extract Inlined Constant wmult => "Int64Word.wmult".
Extract Inlined Constant wminus => "Int64Word.wminus".
Extract Inlined Constant weq => "Int64Word.weq".
Extract Inlined Constant weqb => "Int64Word.weqb".
Extract Inlined Constant wlt => "Int64Word.wlt".
Extract Inlined Constant wlt_dec => "Int64Word.wlt_dec".
Extract Inlined Constant wand => "Int64Word.wand".
Extract Inlined Constant wor => "Int64Word.wor".
Extract Inlined Constant wnot => "Int64Word.wnot".
Extract Inlined Constant wneg => "Int64Word.wneg".
Extract Inlined Constant wordToNat => "Int64Word.wordToNat".
Extract Inlined Constant natToWord => "Int64Word.natToWord".
Extract Inlined Constant wzero => "Int64Word.wzero".
Extract Inlined Constant wzero' => "Int64Word.wzero'".
Extract Inlined Constant wones => "Int64Word.wones".

Extract Inlined Constant WordOpt.word_split_hd => "Int64Word.word_split_hd".
Extract Inlined Constant WordOpt.word_split_tl => "Int64Word.word_split_tl".
Extract Inlined Constant AlignWord.split1' => "Int64Word.split1'".
Extract Inlined Constant AlignWord.split2' => "Int64Word.split2'".
Extract Inlined Constant split1 => "Int64Word.split1".
Extract Inlined Constant split2 => "Int64Word.split2".
Extract Inlined Constant WordOpt.SW_word => "Int64Word.SW_word".
Extract Inlined Constant combine => "Int64Word.combine".
Extract Inlined Constant Core.append_word => "Int64Word.append".

Definition word_split_hd_test := WordOpt.word_split_hd (natToWord 5 30).
Definition word_split_tl_test := wordToNat (WordOpt.word_split_tl (natToWord 5 30)).
Definition alignword_split1'_test := wordToNat (AlignWord.split1' 2 3 (natToWord 5 30)).
Definition alignword_split2'_test := wordToNat (AlignWord.split2' 2 3 (natToWord 5 30)).
Definition split1_test := wordToNat (split1 3 2 (natToWord 5 30)).
Definition split2_test := wordToNat (split2 3 2 (natToWord 5 30)).
Definition combine_test := wordToNat (combine (natToWord 5 30) (natToWord 7 14)).
Definition append_word_test := wordToNat (Core.append_word (@natToWord 8 5) (@natToWord 12 126)).

(** * Special case of internet checksum *)
Extract Constant InternetChecksum.OneC_plus => "Int64Word.onec_plus".

(** Efficient bytestrings *)

Extract Inductive Fin.t =>
"ArrayVector.idx_t"
  ["ArrayVector.zero" "ArrayVector.succ"]
  "ArrayVector.destruct_idx".

Extract Inlined Constant Fin.L => "(fun _ n p -> p)".
Extract Inlined Constant Fin.R => "(fun _ n p -> n + p)".

Extract Inductive Vector.t =>
"StackVector.t"
  ["StackVector.empty ()" "StackVector.cons"]
  "StackVector.destruct".

Extract Inductive VectorDef.t =>
"StackVector.t"
  ["StackVector.empty ()" "StackVector.cons"]
  "StackVector.destruct".

Extract Inlined Constant Vector.nth => "StackVector.nth".
Extract Inlined Constant VectorDef.nth => "StackVector.nth".
Extract Inlined Constant Vector_nth_opt => "StackVector.nth_opt".
Extract Inlined Constant EnumOpt.word_indexed => "StackVector.index".

(*
Extract Inductive Vector.t =>
"ArrayVector.storage_t"
  ["ArrayVector.empty ()" "ArrayVector.cons"]
  "ArrayVector.destruct_storage".
Extract Inductive VectorDef.t =>
"ArrayVector.storage_t"
  ["ArrayVector.empty ()" "ArrayVector.cons"]
  "ArrayVector.destruct_storage".

Extract Inlined Constant Vector.hd => "ArrayVector.hd".
Extract Inlined Constant VectorDef.hd => "ArrayVector.hd".
Extract Inlined Constant Vector.tl => "ArrayVector.tl".
Extract Inlined Constant VectorDef.tl => "ArrayVector.tl".
Extract Inlined Constant Vector.to_list => "ArrayVector.to_list".
Extract Inlined Constant VectorDef.to_list => "ArrayVector.to_list".
Extract Inlined Constant Vector.append => "ArrayVector.append".
Extract Inlined Constant VectorDef.append => "ArrayVector.append".
Extract Inlined Constant Vector.nth => "ArrayVector.nth".
Extract Inlined Constant VectorDef.nth => "ArrayVector.nth".
Extract Inlined Constant Vector.replace => "ArrayVector.set_nth".
Extract Inlined Constant VectorDef.replace => "ArrayVector.set_nth".
Extract Inlined Constant Vector_nth_opt => "ArrayVector.nth_opt".
Extract Inlined Constant EnumOpt.word_indexed => "ArrayVector.index".

Extract Inlined Constant nth_opt => "ArrayVector.nth_opt".
Extract Inlined Constant set_nth' => "ArrayVector.set_nth".
Extract Inlined Constant InternetChecksum.ByteBuffer_fold_left_pair => "ArrayVector.fold_left_pair".
Extract Inlined Constant AlignedList.buffer_blit_buffer => "ArrayVector.blit_array".
Extract Inlined Constant AlignedList.bytebuffer_of_bytebuffer_range =>
  "(fun sz from len v ->
    let b = ArrayVector.array_of_range sz from len v in
    ExistT (ArrayVector.length b, b))".
*)

(* CPC clean up CstructBytestring.ml to remove unneeded stuff *)

Import AlignedByteString.
Extract Constant AlignedByteString.ByteBuffer.t => "CstructBytestring.storage_t".
Extract Inlined Constant ByteBuffer.t => "CstructBytestring.storage_t".
Extract Inlined Constant ByteBuffer.nil => "CstructBytestring.nil".
Extract Inlined Constant ByteBuffer.cons => "CstructBytestring.cons".
Extract Inlined Constant ByteBuffer.hd => "CstructBytestring.hd".
Extract Inlined Constant ByteBuffer.tl => "CstructBytestring.tl".
Extract Inlined Constant ByteBuffer.to_list => "CstructBytestring.to_list".
Extract Inlined Constant ByteBuffer.of_vector => "CstructBytestring.of_vector".
Extract Inlined Constant ByteBuffer.to_vector => "CstructBytestring.to_vector".
Extract Inlined Constant ByteBuffer.append => "CstructBytestring.append".
Extract Inlined Constant nth_opt => "CstructBytestring.nth_opt".
Extract Inlined Constant set_nth' => "CstructBytestring.set_nth".
Extract Inlined Constant initialize_Aligned_ByteString => "CstructBytestring.create".
Extract Inlined Constant InternetChecksum.ByteBuffer_checksum_bound => "CstructBytestring.checksum_bound".
Extract Inlined Constant AlignedList.buffer_blit_buffer => "CstructBytestring.blit_buffer".
Extract Constant AlignedList.bytebuffer_of_bytebuffer_range =>
  "(fun sz from len v ->
    let b = CstructBytestring.slice_range sz from len v in
    ExistT (CstructBytestring.length b, b))".

Compute
  match IPv4Header.IPv4_decoder_impl IPv4Header.bin_pkt with
  | Some (p, _, _) =>
    match IPv4Header.IPv4_encoder_impl (AlignedByteString.initialize_Aligned_ByteString 20) p with
    | Some (bytes, _, _) => Some (Vector.map (@wordToNat 8) bytes)
    | None => None
    end
  | None => None
  end.

Definition fiat_ipv4_decode_bench (_: unit) :=
  fiat_ipv4_decode IPv4Header.bin_pkt.
Definition fiat_ipv4_encode_bench (_: unit) :=
  fiat_ipv4_encode IPv4Header.pkt (MakeBuffer 20).

Extraction "Fiat4Mirage"
           (* fiat_ipv4_decode_bench *)
           (* fiat_ipv4_encode_bench *)

           fiat_ethernet_type_of_enum
           fiat_ethernet_type_to_enum
           fiat_ethernet_encode
           fiat_ethernet_decode
           fiat_arp_hardtype_of_enum
           fiat_arp_hardtype_to_enum
           fiat_arp_prottype_of_enum
           fiat_arp_prottype_to_enum
           fiat_arp_operation_of_enum
           fiat_arp_operation_to_enum
           fiat_arp_decode
           fiat_arp_encode
           fiat_ipv4_protocol_of_enum
           fiat_ipv4_protocol_to_enum
           fiat_ipv4_decode
           fiat_ipv4_encode
           fiat_tcp_encode
           fiat_tcp_decode
           fiat_udp_encode
           fiat_udp_decode

           projT2
           existT.

