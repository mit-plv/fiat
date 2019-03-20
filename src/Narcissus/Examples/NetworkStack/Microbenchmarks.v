Require Import Fiat.Narcissus.Examples.NetworkStack.TestInfrastructure.

Definition buf := MakeBuffer 4096.

Transparent weqb.
Transparent natToWord.

Definition arp_request_ether_decode_42_input :=
  Eval compute in Vector.map (@natToWord 8) [72;81;183;14;152;89;80;199;191;62;218;205;8;6;0;1;8;0;6;4;0;1;80;199;191;62;218;205;192;168;1;1;0;0;0;0;0;0;192;168;1;109].

Definition arp_request_ether_encode_42_input :=
  Eval compute in (must (fiat_ethernet_decode arp_request_ether_decode_42_input 42) I).

Definition arp_request_arp_decode_28_input :=
  Eval compute in Vector.map (@natToWord 8) [0;1;8;0;6;4;0;1;80;199;191;62;218;205;192;168;1;1;0;0;0;0;0;0;192;168;1;109].

Definition arp_request_arp_encode_28_input :=
  Eval compute in (must (fiat_arp_decode arp_request_arp_decode_28_input) I).

Definition arp_response_ether_decode_42_input :=
  Eval compute in Vector.map (@natToWord 8) [80;199;191;62;218;205;72;81;183;14;152;89;8;6;0;1;8;0;6;4;0;2;72;81;183;14;152;89;192;168;1;109;80;199;191;62;218;205;192;168;1;1].

Definition arp_response_ether_encode_42_input :=
  Eval compute in (must (fiat_ethernet_decode arp_response_ether_decode_42_input 42) I).

Definition arp_response_arp_decode_28_input :=
  Eval compute in Vector.map (@natToWord 8) [0;1;8;0;6;4;0;2;72;81;183;14;152;89;192;168;1;109;80;199;191;62;218;205;192;168;1;1].

Definition arp_response_arp_encode_28_input :=
  Eval compute in (must (fiat_arp_decode arp_response_arp_decode_28_input) I).

Definition http_request_ether_decode_141_input :=
  Eval compute in Vector.map (@natToWord 8) [80;199;191;62;218;205;72;81;183;14;152;89;8;0;69;0;0;127;27;241;64;0;64;6;67;105;192;168;1;109;151;101;129;164;144;42;0;80;19;125;120;241;243;111;68;47;128;24;0;229;29;216;0;0;1;1;8;10;228;110;2;137;80;206;41;110;71;69;84;32;47;32;72;84;84;80;47;49;46;49;13;10;72;111;115;116;58;32;110;121;116;105;109;101;115;46;99;111;109;13;10;85;115;101;114;45;65;103;101;110;116;58;32;99;117;114;108;47;55;46;52;55;46;48;13;10;65;99;99;101;112;116;58;32;42;47;42;13;10;13;10].

Definition http_request_ether_encode_141_input :=
  Eval compute in (must (fiat_ethernet_decode http_request_ether_decode_141_input 141) I).

Definition http_request_ip_decode_127_input :=
  Eval compute in Vector.map (@natToWord 8) [69;0;0;127;27;241;64;0;64;6;67;105;192;168;1;109;151;101;129;164;144;42;0;80;19;125;120;241;243;111;68;47;128;24;0;229;29;216;0;0;1;1;8;10;228;110;2;137;80;206;41;110;71;69;84;32;47;32;72;84;84;80;47;49;46;49;13;10;72;111;115;116;58;32;110;121;116;105;109;101;115;46;99;111;109;13;10;85;115;101;114;45;65;103;101;110;116;58;32;99;117;114;108;47;55;46;52;55;46;48;13;10;65;99;99;101;112;116;58;32;42;47;42;13;10;13;10].

Definition http_request_ip_encode_127_input :=
  Eval compute in (must (fiat_ipv4_decode http_request_ip_decode_127_input) I).

Definition http_request_tcp_decode_107_input :=
  Eval compute in Vector.map (@natToWord 8) [144;42;0;80;19;125;120;241;243;111;68;47;128;24;0;229;29;216;0;0;1;1;8;10;228;110;2;137;80;206;41;110;71;69;84;32;47;32;72;84;84;80;47;49;46;49;13;10;72;111;115;116;58;32;110;121;116;105;109;101;115;46;99;111;109;13;10;85;115;101;114;45;65;103;101;110;116;58;32;99;117;114;108;47;55;46;52;55;46;48;13;10;65;99;99;101;112;116;58;32;42;47;42;13;10;13;10].

Definition http_request_tcp_encode_107_input :=
  Eval compute in (must (fiat_tcp_decode http_request_tcp_decode_107_input (Vector.map (@natToWord 8) [192;168;1;109]) (Vector.map (@natToWord 8) [151;101;129;164]) (natToWord 16 107)) I).

Definition http_response_ether_decode_372_input :=
  Eval compute in Vector.map (@natToWord 8) [72;81;183;14;152;89;80;199;191;62;218;205;8;0;69;32;1;102;109;95;64;0;59;6;245;243;151;101;129;164;192;168;1;109;0;80;144;42;243;111;68;47;19;125;121;60;128;24;0;55;33;1;0;0;1;1;8;10;80;206;41;115;228;110;2;137;72;84;84;80;47;49;46;49;32;51;48;49;32;77;111;118;101;100;32;80;101;114;109;97;110;101;110;116;108;121;13;10;83;101;114;118;101;114;58;32;86;97;114;110;105;115;104;13;10;82;101;116;114;121;45;65;102;116;101;114;58;32;48;13;10;67;111;110;116;101;110;116;45;76;101;110;103;116;104;58;32;48;13;10;76;111;99;97;116;105;111;110;58;32;104;116;116;112;115;58;47;47;119;119;119;46;110;121;116;105;109;101;115;46;99;111;109;47;13;10;65;99;99;101;112;116;45;82;97;110;103;101;115;58;32;98;121;116;101;115;13;10;68;97;116;101;58;32;84;104;117;44;32;49;50;32;74;117;108;32;50;48;49;56;32;48;49;58;52;54;58;49;57;32;71;77;84;13;10;88;45;83;101;114;118;101;100;45;66;121;58;32;99;97;99;104;101;45;98;111;115;56;50;51;48;45;66;79;83;13;10;88;45;67;97;99;104;101;58;32;72;73;84;13;10;88;45;67;97;99;104;101;45;72;105;116;115;58;32;48;13;10;88;45;70;114;97;109;101;45;79;112;116;105;111;110;115;58;32;68;69;78;89;13;10;67;111;110;110;101;99;116;105;111;110;58;32;99;108;111;115;101;13;10;88;45;65;80;73;45;86;101;114;115;105;111;110;58;32;70;45;48;13;10;13;10].

Definition http_response_ether_encode_372_input :=
  Eval compute in (must (fiat_ethernet_decode http_response_ether_decode_372_input 372) I).

Definition http_response_ip_decode_358_input :=
  Eval compute in Vector.map (@natToWord 8) [69;32;1;102;109;95;64;0;59;6;245;243;151;101;129;164;192;168;1;109;0;80;144;42;243;111;68;47;19;125;121;60;128;24;0;55;33;1;0;0;1;1;8;10;80;206;41;115;228;110;2;137;72;84;84;80;47;49;46;49;32;51;48;49;32;77;111;118;101;100;32;80;101;114;109;97;110;101;110;116;108;121;13;10;83;101;114;118;101;114;58;32;86;97;114;110;105;115;104;13;10;82;101;116;114;121;45;65;102;116;101;114;58;32;48;13;10;67;111;110;116;101;110;116;45;76;101;110;103;116;104;58;32;48;13;10;76;111;99;97;116;105;111;110;58;32;104;116;116;112;115;58;47;47;119;119;119;46;110;121;116;105;109;101;115;46;99;111;109;47;13;10;65;99;99;101;112;116;45;82;97;110;103;101;115;58;32;98;121;116;101;115;13;10;68;97;116;101;58;32;84;104;117;44;32;49;50;32;74;117;108;32;50;48;49;56;32;48;49;58;52;54;58;49;57;32;71;77;84;13;10;88;45;83;101;114;118;101;100;45;66;121;58;32;99;97;99;104;101;45;98;111;115;56;50;51;48;45;66;79;83;13;10;88;45;67;97;99;104;101;58;32;72;73;84;13;10;88;45;67;97;99;104;101;45;72;105;116;115;58;32;48;13;10;88;45;70;114;97;109;101;45;79;112;116;105;111;110;115;58;32;68;69;78;89;13;10;67;111;110;110;101;99;116;105;111;110;58;32;99;108;111;115;101;13;10;88;45;65;80;73;45;86;101;114;115;105;111;110;58;32;70;45;48;13;10;13;10].

Definition http_response_ip_encode_358_input :=
  Eval compute in (must (fiat_ipv4_decode http_response_ip_decode_358_input) I).

Definition http_response_tcp_decode_338_input :=
  Eval compute in Vector.map (@natToWord 8) [0;80;144;42;243;111;68;47;19;125;121;60;128;24;0;55;33;1;0;0;1;1;8;10;80;206;41;115;228;110;2;137;72;84;84;80;47;49;46;49;32;51;48;49;32;77;111;118;101;100;32;80;101;114;109;97;110;101;110;116;108;121;13;10;83;101;114;118;101;114;58;32;86;97;114;110;105;115;104;13;10;82;101;116;114;121;45;65;102;116;101;114;58;32;48;13;10;67;111;110;116;101;110;116;45;76;101;110;103;116;104;58;32;48;13;10;76;111;99;97;116;105;111;110;58;32;104;116;116;112;115;58;47;47;119;119;119;46;110;121;116;105;109;101;115;46;99;111;109;47;13;10;65;99;99;101;112;116;45;82;97;110;103;101;115;58;32;98;121;116;101;115;13;10;68;97;116;101;58;32;84;104;117;44;32;49;50;32;74;117;108;32;50;48;49;56;32;48;49;58;52;54;58;49;57;32;71;77;84;13;10;88;45;83;101;114;118;101;100;45;66;121;58;32;99;97;99;104;101;45;98;111;115;56;50;51;48;45;66;79;83;13;10;88;45;67;97;99;104;101;58;32;72;73;84;13;10;88;45;67;97;99;104;101;45;72;105;116;115;58;32;48;13;10;88;45;70;114;97;109;101;45;79;112;116;105;111;110;115;58;32;68;69;78;89;13;10;67;111;110;110;101;99;116;105;111;110;58;32;99;108;111;115;101;13;10;88;45;65;80;73;45;86;101;114;115;105;111;110;58;32;70;45;48;13;10;13;10].

Definition http_response_tcp_encode_338_input :=
  Eval compute in (must (fiat_tcp_decode http_response_tcp_decode_338_input (Vector.map (@natToWord 8) [151;101;129;164]) (Vector.map (@natToWord 8) [192;168;1;109]) (natToWord 16 338)) I).

Definition ntp_request_ether_decode_90_input :=
  Eval compute in Vector.map (@natToWord 8) [80;199;191;62;218;205;72;81;183;14;152;89;8;0;69;0;0;76;42;91;64;0;64;17;104;140;192;168;1;109;132;163;97;1;0;123;0;123;0;56;213;93;227;0;3;250;0;1;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;222;241;103;36;233;43;107;49].

Definition ntp_request_ether_encode_90_input :=
  Eval compute in (must (fiat_ethernet_decode ntp_request_ether_decode_90_input 90) I).

Definition ntp_request_ip_decode_76_input :=
  Eval compute in Vector.map (@natToWord 8) [69;0;0;76;42;91;64;0;64;17;104;140;192;168;1;109;132;163;97;1;0;123;0;123;0;56;213;93;227;0;3;250;0;1;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;222;241;103;36;233;43;107;49].

Definition ntp_request_ip_encode_76_input :=
  Eval compute in (must (fiat_ipv4_decode ntp_request_ip_decode_76_input) I).

Definition ntp_request_udp_decode_56_input :=
  Eval compute in Vector.map (@natToWord 8) [0;123;0;123;0;56;213;93;227;0;3;250;0;1;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;222;241;103;36;233;43;107;49].

Definition ntp_request_udp_encode_56_input :=
  Eval compute in (must (fiat_udp_decode ntp_request_udp_decode_56_input (Vector.map (@natToWord 8) [192;168;1;109]) (Vector.map (@natToWord 8) [132;163;97;1]) (natToWord 16 56)) I).

Definition ntp_response_ether_decode_90_input :=
  Eval compute in Vector.map (@natToWord 8) [72;81;183;14;152;89;80;199;191;62;218;205;8;0;69;32;0;76;130;236;0;0;54;17;89;219;132;163;97;1;192;168;1;109;0;123;0;123;0;56;247;218;28;1;13;227;0;0;0;16;0;0;0;32;78;73;83;84;222;241;102;203;0;0;0;0;222;241;103;36;233;43;107;49;222;241;103;36;241;94;157;42;222;241;103;36;241;94;166;251].

Definition ntp_response_ether_encode_90_input :=
  Eval compute in (must (fiat_ethernet_decode ntp_response_ether_decode_90_input 90) I).

Definition ntp_response_ip_decode_76_input :=
  Eval compute in Vector.map (@natToWord 8) [69;32;0;76;130;236;0;0;54;17;89;219;132;163;97;1;192;168;1;109;0;123;0;123;0;56;247;218;28;1;13;227;0;0;0;16;0;0;0;32;78;73;83;84;222;241;102;203;0;0;0;0;222;241;103;36;233;43;107;49;222;241;103;36;241;94;157;42;222;241;103;36;241;94;166;251].

Definition ntp_response_ip_encode_76_input :=
  Eval compute in (must (fiat_ipv4_decode ntp_response_ip_decode_76_input) I).

Definition ntp_response_udp_decode_56_input :=
  Eval compute in Vector.map (@natToWord 8) [0;123;0;123;0;56;247;218;28;1;13;227;0;0;0;16;0;0;0;32;78;73;83;84;222;241;102;203;0;0;0;0;222;241;103;36;233;43;107;49;222;241;103;36;241;94;157;42;222;241;103;36;241;94;166;251].

Definition ntp_response_udp_encode_56_input :=
  Eval compute in (must (fiat_udp_decode ntp_response_udp_decode_56_input (Vector.map (@natToWord 8) [132;163;97;1]) (Vector.map (@natToWord 8) [192;168;1;109]) (natToWord 16 56)) I).

(* arp_request_ether_encode_42 *)
Compute (must (fiat_ethernet_encode arp_request_ether_encode_42_input (FreshBuffer 42 buf)) I).

(* arp_request_ether_decode_42 *)
Compute (must (fiat_ethernet_decode arp_request_ether_decode_42_input 42) I).

(* arp_request_arp_encode_28 *)
Compute (must (fiat_arp_encode arp_request_arp_encode_28_input (FreshBuffer 28 buf)) I).

(* arp_request_arp_decode_28 *)
Compute (must (fiat_arp_decode arp_request_arp_decode_28_input) I).

(* arp_response_ether_encode_42 *)
Compute (must (fiat_ethernet_encode arp_response_ether_encode_42_input (FreshBuffer 42 buf)) I).

(* arp_response_ether_decode_42 *)
Compute (must (fiat_ethernet_decode arp_response_ether_decode_42_input 42) I).

(* arp_response_arp_encode_28 *)
Compute (must (fiat_arp_encode arp_response_arp_encode_28_input (FreshBuffer 28 buf)) I).

(* arp_response_arp_decode_28 *)
Compute (must (fiat_arp_decode arp_response_arp_decode_28_input) I).

(* http_request_ether_encode_141 *)
Compute (must (fiat_ethernet_encode http_request_ether_encode_141_input (FreshBuffer 141 buf)) I).

(* http_request_ether_decode_141 *)
Compute (must (fiat_ethernet_decode http_request_ether_decode_141_input 141) I).

(* http_request_ip_encode_127 *)
Compute (must (fiat_ipv4_encode http_request_ip_encode_127_input (FreshBuffer 127 buf)) I).

(* http_request_ip_decode_127 *)
Compute (must (fiat_ipv4_decode http_request_ip_decode_127_input) I).

(* http_request_tcp_encode_107 *)
Compute (must (fiat_tcp_encode http_request_tcp_encode_107_input (Vector.map (@natToWord 8) [192;168;1;109]) (Vector.map (@natToWord 8) [151;101;129;164]) (natToWord 16 107) (FreshBuffer 107 buf)) I).

(* http_request_tcp_decode_107 *)
Compute (must (fiat_tcp_decode http_request_tcp_decode_107_input (Vector.map (@natToWord 8) [192;168;1;109]) (Vector.map (@natToWord 8) [151;101;129;164]) (natToWord 16 107)) I).

(* http_response_ether_encode_372 *)
Compute (must (fiat_ethernet_encode http_response_ether_encode_372_input (FreshBuffer 372 buf)) I).

(* http_response_ether_decode_372 *)
Compute (must (fiat_ethernet_decode http_response_ether_decode_372_input 372) I).

(* http_response_ip_encode_358 *)
Compute (must (fiat_ipv4_encode http_response_ip_encode_358_input (FreshBuffer 358 buf)) I).

(* http_response_ip_decode_358 *)
Compute (must (fiat_ipv4_decode http_response_ip_decode_358_input) I).

(* http_response_tcp_encode_338 *)
Compute (must (fiat_tcp_encode http_response_tcp_encode_338_input (Vector.map (@natToWord 8) [151;101;129;164]) (Vector.map (@natToWord 8) [192;168;1;109]) (natToWord 16 338) (FreshBuffer 338 buf)) I).

(* http_response_tcp_decode_338 *)
Compute (must (fiat_tcp_decode http_response_tcp_decode_338_input (Vector.map (@natToWord 8) [151;101;129;164]) (Vector.map (@natToWord 8) [192;168;1;109]) (natToWord 16 338)) I).

(* ntp_request_ether_encode_90 *)
Compute (must (fiat_ethernet_encode ntp_request_ether_encode_90_input (FreshBuffer 90 buf)) I).

(* ntp_request_ether_decode_90 *)
Compute (must (fiat_ethernet_decode ntp_request_ether_decode_90_input 90) I).

(* ntp_request_ip_encode_76 *)
Compute (must (fiat_ipv4_encode ntp_request_ip_encode_76_input (FreshBuffer 76 buf)) I).

(* ntp_request_ip_decode_76 *)
Compute (must (fiat_ipv4_decode ntp_request_ip_decode_76_input) I).

(* ntp_request_udp_encode_56 *)
Compute (must (fiat_udp_encode ntp_request_udp_encode_56_input (Vector.map (@natToWord 8) [192;168;1;109]) (Vector.map (@natToWord 8) [132;163;97;1]) (natToWord 16 56) (FreshBuffer 56 buf)) I).

(* ntp_request_udp_decode_56 *)
Compute (must (fiat_udp_decode ntp_request_udp_decode_56_input (Vector.map (@natToWord 8) [192;168;1;109]) (Vector.map (@natToWord 8) [132;163;97;1]) (natToWord 16 56)) I).

(* ntp_response_ether_encode_90 *)
Compute (must (fiat_ethernet_encode ntp_response_ether_encode_90_input (FreshBuffer 90 buf)) I).

(* ntp_response_ether_decode_90 *)
Compute (must (fiat_ethernet_decode ntp_response_ether_decode_90_input 90) I).

(* ntp_response_ip_encode_76 *)
Compute (must (fiat_ipv4_encode ntp_response_ip_encode_76_input (FreshBuffer 76 buf)) I).

(* ntp_response_ip_decode_76 *)
Compute (must (fiat_ipv4_decode ntp_response_ip_decode_76_input) I).

(* ntp_response_udp_encode_56 *)
Compute (must (fiat_udp_encode ntp_response_udp_encode_56_input (Vector.map (@natToWord 8) [132;163;97;1]) (Vector.map (@natToWord 8) [192;168;1;109]) (natToWord 16 56) (FreshBuffer 56 buf)) I).

(* ntp_response_udp_decode_56 *)
Compute (must (fiat_udp_decode ntp_response_udp_decode_56_input (Vector.map (@natToWord 8) [132;163;97;1]) (Vector.map (@natToWord 8) [192;168;1;109]) (natToWord 16 56)) I).
