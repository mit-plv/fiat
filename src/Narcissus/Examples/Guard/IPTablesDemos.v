Require Import Fiat.Narcissus.Examples.Guard.Core.
Require Import Fiat.Narcissus.Examples.Guard.IPTables.
Require Import Fiat.Narcissus.Examples.Guard.Ports.

Open Scope iptables_scope.

Example drop_messages_192_10 :=
  iptables -A FORWARD
           --source 192'0'0'0/8
           --destination 10'0'0'0/8
           -j DROP.

Example drop_dhcp_serverport_from_nonserver :=
  iptables -A FORWARD
           --protocol "UDP"
           --source-port bootps
           ! --source 192'168'0'1
           -j DROP.

Example accept_dhcp_client_broadcast :=
  iptables -A FORWARD
           --protocol "UDP"
           --source-port bootpc
           --destination 255'255'255'255
  -j ACCEPT.

Example drop_dhcp_messages_to_wrong_port :=
  iptables -A FORWARD
           --protocol "UDP"
           --source-port bootpc
           ! --destination-port bootps
           -j DROP.

Example drop_dhcp_messages_to_wrong_address :=
  iptables -A FORWARD
           --protocol "UDP"
           --source-port bootpc
           ! --destination 255'255'255'255/32
           -j DROP.

(** We can apply these filters to packets: *)

Require Import Coq.Vectors.Vector.
Import VectorNotations.
Definition dhcp_offer : Vector.t (word 8) _ :=
  Eval compute in Vector.map (@NToWord 8) [69; 0; 1; 72; 4; 69; 0; 0; 128; 17; 180; 4; 192; 168; 0; 1; 192; 168; 0; 10; 0; 67; 0; 68; 1; 52; 34; 51; 2; 1; 6; 0; 0; 0; 61; 29; 0; 0; 0; 0; 0; 0; 0; 0; 192; 168; 0; 10; 192; 168; 0; 1; 0; 0; 0; 0; 0; 11; 130; 1; 252; 66; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 99; 130; 83; 99; 53; 1; 2; 1; 4; 255; 255; 255; 0; 58; 4; 0; 0; 7; 8; 59; 4; 0; 0; 12; 78; 51; 4; 0; 0; 14; 16; 54; 4; 192; 168; 0; 1; 255; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]%N.

Definition dhcp_request : Vector.t (word 8) _ :=
  Eval compute in Vector.map (@NToWord 8) [69; 0; 1; 44; 168; 55; 0; 0; 250; 17; 23; 138; 0; 0; 0; 0; 255; 255; 255; 255; 0; 68; 0; 67; 1; 24; 159; 189; 1; 1; 6; 0; 0; 0; 61; 30; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 11; 130; 1; 252; 66; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 99; 130; 83; 99; 53; 1; 3; 61; 7; 1; 0; 11; 130; 1; 252; 66; 50; 4; 192; 168; 0; 10; 54; 4; 192; 168; 0; 1; 55; 4; 1; 3; 6; 42; 255; 0]%N.

Definition dhcp_offer_input : input :=
  must (input_of_bytes FORWARD (bytes_of_ByteBuffer dhcp_offer)).

Definition dhcp_request_input : input :=
  must (input_of_bytes FORWARD (bytes_of_ByteBuffer dhcp_request)).

(* The filter that accepts client DHCP broadcasts accepts dhcp_request (a client message): *)
Compute (accept_dhcp_client_broadcast dhcp_request_input).
(* But it doesn't say anything about dhcp_offer (a server message): *)
Compute (accept_dhcp_client_broadcast dhcp_offer_input).

(* We can also observe the implementation of a given filter: *)

Ltac simp x :=
  let xn := fresh in
  let t := type of x in
  pose x as xn;
  repeat autounfold with iptables in xn;
  cbn in xn;
  compute [andb] in xn;
  let xn := (eval unfold xn in xn) in
  exact xn.

Eval cbv zeta in ltac:(simp (iptables -A FORWARD
                              --protocol "UDP"
                              --source-port bootpc
                              --destination 255'255'255'255
                              -j ACCEPT)).

