Require Import Narcissus.Examples.Guard.Guard.
Require Import Narcissus.OCamlExtraction.Extraction.

Open Scope string_scope.

Notation simp x :=
  ltac:(let x := (eval red in x) in
        let x := (eval cbn in x) in
        exact x).

Definition guard_init : ComputationalADT.cRep GuardImpl :=
  simp (CallConstructor GuardImpl "Init").

Definition guard_process_packet (bs: bytes) (rep: ComputationalADT.cRep GuardImpl) : (_ * result) :=
  simp (CallMethod GuardImpl "ProcessPacket" rep bs).

Definition make_tcp_syn_packet (src_addr dst_addr: word 32) (src_port dst_port: word 16) : option bytes :=
  let ip_bs := AlignedByteString.initialize_Aligned_ByteString 20 in
  let tcp_bs := AlignedByteString.initialize_Aligned_ByteString 20 in
  match IPv4Header.IPv4_encoder_impl ip_bs
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
    match TCP_Packet.TCP_encoder_impl (ipv4ToByteBuffer src_addr) (ipv4ToByteBuffer dst_addr) (natToWord _ 20)
                           {| TCP_Packet.SourcePort := natToWord _ 42;
                              TCP_Packet.DestPort := natToWord _ 42;
                              TCP_Packet.SeqNumber := wzero _;
                              TCP_Packet.AckNumber := wzero _;
                              TCP_Packet.NS := false; (* ECN-nonce concealment protection flag *)
                              TCP_Packet.CWR := false; (* Congestion Window Reduced (CWR) flag *)
                              TCP_Packet.ECE := false; (* ECN-Echo flag *)
                              (* We can infer the URG flag from the Urgent Pointer field *)
                              TCP_Packet.ACK := false; (* Acknowledgment field is significant flag *)
                              TCP_Packet.PSH := false; (* Push function flag *)
                              TCP_Packet.RST := false; (* Reset the connection flag *)
                              TCP_Packet.SYN := true; (* Synchronize sequence numbers flag *)
                              TCP_Packet.FIN := false; (* No more data from sender flag*)
                              TCP_Packet.WindowSize := natToWord _ 42;
                              TCP_Packet.UrgentPointer := None;
                              TCP_Packet.Options := [];
                              TCP_Packet.Payload := existT _ 0 (AlignedByteString.initialize_Aligned_ByteString 0) |}

                           tcp_bs with
    | None => None
    | Some (pkt, _, _) =>
      Some (existT _ 40 (ByteBuffer.ByteBuffer.append hdr pkt))
    end
  end.

Extraction "guard.ml" guard_init guard_process_packet make_tcp_syn_packet.
