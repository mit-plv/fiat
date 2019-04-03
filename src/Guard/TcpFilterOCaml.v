Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Fiat.Narcissus.Examples.NetworkStack.IPv4Header.
Require Import Fiat.Narcissus.Examples.NetworkStack.TCP_Packet.
Require Import ByteBuffer.
Require Import Fiat.Guard.TcpFilter.

Notation "⸨ x , y ⸩" := {| prim_fst := x; prim_snd := y |}.

Require Import QueryStructureNotations.

Arguments ilist2_hd : simpl nomatch.
Arguments ilist2_tl : simpl nomatch.


Set Printing Implicit.
Print GuardImpl.

Definition guard_init : ComputationalADT.cRep GuardImpl :=
  Eval simpl in (CallConstructor GuardImpl "Init").

Definition guard_process_packet (bs: bytes) (rep: ComputationalADT.cRep GuardImpl) : (_ * bool) :=
  Eval simpl in CallMethod GuardImpl "ProcessPacket" rep bs.

Require Import Narcissus.OCamlExtraction.Extraction.
Import String_as_OT OrderedTypeEx.

Extraction Inline negb.
Extract Inductive reflect => bool [ true false ].

Extract Constant string_dec  => "(=)".
Extract Constant String_as_OT.eq_dec  => "(=)".
Extract Constant Nat_as_OT.eq_dec => "(=)".

Extract Constant String_as_OT.compare => "fun a b -> let comp = compare a b in
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".
Extract Constant Nat_as_OT.compare    => "fun (a: int) (b: int) -> let comp = compare a b in
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".
Extract Constant String_as_OT.string_compare => "fun a b -> let comp = compare a b in
                                                 if comp = 0 then Eq else if comp < 0 then Lt else Gt".

Print IPv4_decoder_impl.

Extract Constant Nat.ltb => "(<)".
Extract Constant Nat.leb => "(<=)".
Extract Constant IPChecksum.IPChecksum_Valid_dec =>
  "(fun _ -> failwith ""FIXME"")".
Extract Constant AlignedByteString.build_aligned_ByteString =>
  "(fun _ -> failwith ""FIXME"")".

Require Import Fiat.Common.EnumType.

Require Import Word.

Definition make_tcp_syn_packet (src_addr dst_addr: word 32) (src_port dst_port: word 16) : option bytes :=
  let ip_bs := AlignedByteString.initialize_Aligned_ByteString 20 in
  let tcp_bs := AlignedByteString.initialize_Aligned_ByteString 20 in
  match IPv4_encoder_impl ip_bs
                          {| IPv4Header.TotalLength := natToWord _ (40);
                             IPv4Header.ID := wzero _;
                             IPv4Header.DF := false; (* Don't fragment flag *)
                             IPv4Header.MF := false; (*  Multiple fragments flag *)
                             IPv4Header.FragmentOffset := wzero _;
                             IPv4Header.TTL := natToWord _ 8;
                             IPv4Header.Protocol := ```"TCP";
                             IPv4Header.SourceAddress := src_addr;
                             IPv4Header.DestAddress := dst_addr;
                             IPv4Header.Options := [] |}
  with
  | None => None
  | Some (hdr, _, _) =>
    match TCP_encoder_impl (ipv4ToByteBuffer src_addr) (ipv4ToByteBuffer dst_addr) (natToWord _ 20)
                           {| SourcePort := natToWord _ 42;
                              DestPort := natToWord _ 42;
                              SeqNumber := wzero _;
                              AckNumber := wzero _;
                              NS := false; (* ECN-nonce concealment protection flag *)
                              CWR := false; (* Congestion Window Reduced (CWR) flag *)
                              ECE := false; (* ECN-Echo flag *)
                              (* We can infer the URG flag from the Urgent Pointer field *)
                              ACK := false; (* Acknowledgment field is significant flag *)
                              PSH := false; (* Push function flag *)
                              RST := false; (* Reset the connection flag *)
                              SYN := true; (* Synchronize sequence numbers flag *)
                              FIN := false; (* No more data from sender flag*)
                              WindowSize := natToWord _ 42;
                              UrgentPointer := None;
                              Options := [];
                              Payload := existT _ 0 (AlignedByteString.initialize_Aligned_ByteString 0) |}

                           tcp_bs with
    | None => None
    | Some (pkt, _, _) =>
      Some (existT _ 40 (ByteBuffer.append hdr pkt))
    end
  end.

Extract Inlined Constant Core.char => "Int64Word.t".

Extract Inductive Vector.t => "ListVector.t" ["(ListVector.empty ())" "ListVector.cons"] "ListVector.destruct".
Extract Inductive VectorDef.t => "ListVector.t" ["(ListVector.empty ())" "ListVector.cons"] "ListVector.destruct".
Extract Inlined Constant Vector.nth => "ListVector.nth".
Extract Inlined Constant AlignedDecodeMonad.Vector_nth_opt => "ListVector.nth_opt".
Extract Inlined Constant ith => "ListVector.ith".
Extract Inlined Constant ith2 => "ListVector.ith2".

Extraction "tcpfilter.ml" guard_init guard_process_packet make_tcp_syn_packet.


(* Fast

     = (cADTRep (prim_prod ADTImplRep ())
        { Def Constructor StringId: rep :=
            ⸨ callConstructor ADTImplMethods BagEmpty, () ⸩ ,
          Def Method StringId0 (p : rep) (s : bytes) : rep * bool :=
            Ifopt ipv4_decode s as a
            Then Ifopt tcp_decode a s as t
                 Then If is_conn_end t
                      Then (⸨ fst
                                (callMethod ADTImplMethods BagDelete (prim_fst p)
                                   (Some (ipv4ToString (SourceAddress a)),
                                    Some (ipv4ToString (DestAddress a)),
                                    (fun row =>
                                      row!"src_port" ==  t.(SourcePort) &&
                                      row!"dst_port" ==  t.(DestPort)))),
                            prim_snd p ⸩, ACCEPT)
                      Else (If Datatypes.length
                                 (snd
                                    (callMethod ADTImplMethods BagFind (prim_fst p)
                                       (Some (ipv4ToString (SourceAddress a)), (Some (ipv4ToString (DestAddress a)), fun _ : RawTuple => true)))) <?
                               MAX_OPEN_CONNECTIONS
                            Then If is_conn_start t
                                 Then (⸨ callMethod ADTImplMethods BagInsert (prim_fst p)
                                           (icons2 (ipv4ToString (SourceAddress a))
                                              (icons2 (port_to_nat (SourcePort t))
                                                 (icons2 (ipv4ToString (DestAddress a)) (icons2 (port_to_nat (DestPort t)) inil2)))), 
                                       prim_snd p ⸩, ACCEPT) Else (p, ACCEPT) Else (p, REJECT)) Else (p, REJECT) Else (p, REJECT)  })%ADT
     : ComputationalADT.cADT GuardSig
*)

(* Slow (indexed on ports):

     = (cADTRep (prim_prod ADTImplRep ())
        { Def Constructor StringId: rep :=
            ⸨ callConstructor ADTImplMethods BagEmpty, () ⸩ ,
          Def Method StringId0 (p : rep) (s : bytes) : rep * bool :=
            Ifopt ipv4_decode s as a
            Then Ifopt tcp_decode a s as t
                 Then If is_conn_end t
                      Then (⸨ fst
                                (callMethod ADTImplMethods BagDelete (prim_fst p)
                                   (Some t.(SourcePort),
                                    Some t.(DestPort),
                                    (fun row =>
                                      row!"src_addr" == a.(SourceAddress) &&
                                      row!"dst_addr" == a.(DestAddress)))), prim_snd p ⸩, ACCEPT)
                      Else (If Datatypes.length
                                 (snd
                                    (callMethod ADTImplMethods BagFind (prim_fst p)
                                       (None,
                                        None,
                                        (fun row =>
                                          row!"src_addr" == a.(SourceAddress) &&
                                          row!"dst_addr" == a.(DestAddress))))) <? MAX_OPEN_CONNECTIONS
                            Then If is_conn_start t
                                 Then (⸨ callMethod ADTImplMethods BagInsert (prim_fst p)
                                           (icons2 (ipv4ToString (SourceAddress a))
                                              (icons2 (port_to_nat (SourcePort t))
                                                 (icons2 (ipv4ToString (DestAddress a)) (icons2 (port_to_nat (DestPort t)) inil2)))), 
                                       prim_snd p ⸩, ACCEPT) Else (p, ACCEPT) Else (p, REJECT)) Else (p, REJECT) Else (p, REJECT)  })%ADT
     : ComputationalADT.cADT GuardSig

 *)

