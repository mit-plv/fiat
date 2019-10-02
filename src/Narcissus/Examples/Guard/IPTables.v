(** This file implements a limited form of iptables syntax. **)

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Fiat.Narcissus.Examples.Guard.Core.

(** We start with some definitions: **)

(* Although we can add rules to each chain, FORWARD will be the only
   meaningful one for us. *)
Inductive chain := INPUT | FORWARD | OUTPUT.
Scheme Equality for chain.

Record ipv4_input_pkt :=
  { ipv4_len : N;
    ipv4_id : N;
    ipv4_df : bool;
    ipv4_mf : bool;
    ipv4_fragment_offset : N;
    ipv4_ttl : N;
    ipv4_protocol : N;
    ipv4_source : N;
    ipv4_dest : N }.

Definition N_of_fin {n} (f: Fin.t n) :=
  N.of_nat (proj1_sig (Fin.to_nat f)).

Definition ipv4_input_pkt_of_pkt pkt :=
  {| ipv4_len := wordToN (pkt.(TotalLength));
     ipv4_id := wordToN (pkt.(ID));
     ipv4_df := pkt.(DF);
     ipv4_mf := pkt.(MF);
     ipv4_fragment_offset := wordToN (pkt.(FragmentOffset));
     ipv4_ttl := wordToN (pkt.(TTL));
     ipv4_protocol := N_of_fin pkt.(Protocol);
     ipv4_source := wordToN (pkt.(SourceAddress));
     ipv4_dest := wordToN (pkt.(DestAddress)) |}.

Record tcp_input_pkt :=
  { tcp_source_port : N;
    tcp_dest_port : N;
    tcp_seq_num : N;
    tcp_ack_num : N;
    tcp_ns : bool; (* ECN-nonce concealment protection flag *)
    tcp_cwr : bool; (* Congestion Window Reduced (CWR) flag *)
    tcp_ece : bool; (* ECN-Echo flag *)
    tcp_ack : bool; (* Acknowledgment field is significant flag *)
    tcp_psh : bool; (* Push function flag *)
    tcp_rst : bool; (* Reset the connection flag *)
    tcp_syn : bool; (* Synchronize sequence numbers flag *)
    tcp_fin : bool; (* No more data from sender flag*)
    tcp_windowsize : N;
    tcp_payload : { n : _ & ByteBuffer.t n }}.

Definition tcp_input_pkt_of_pkt pkt :=
  {| tcp_source_port := wordToN pkt.(SourcePort);
     tcp_dest_port := wordToN pkt.(DestPort);
     tcp_seq_num := wordToN pkt.(SeqNumber);
     tcp_ack_num := wordToN pkt.(AckNumber);
     tcp_ns := pkt.(NS);
     tcp_cwr := pkt.(CWR);
     tcp_ece := pkt.(ECE);
     tcp_ack := pkt.(ACK);
     tcp_psh := pkt.(PSH);
     tcp_rst := pkt.(RST);
     tcp_syn := pkt.(SYN);
     tcp_fin := pkt.(FIN);
     tcp_windowsize := wordToN pkt.(WindowSize);
     tcp_payload := pkt.(Payload) |}.

Record udp_input_pkt :=
  { udp_source_port : N;
    udp_dest_port : N;
    udp_payload : { n : _ & ByteBuffer.t n } }.

Definition udp_input_pkt_of_pkt pkt :=
  {| udp_source_port := wordToN pkt.(UDP_Packet.SourcePort);
     udp_dest_port := wordToN pkt.(UDP_Packet.DestPort);
     udp_payload := pkt.(UDP_Packet.Payload) |}.

Inductive transport_layer_input :=
| TCPInput (pkt: tcp_input_pkt)
| UDPInput (pkt: udp_input_pkt).

(* The guard's filter functions take a decoded packet and a chain
   identifier as input.  *)
Record input :=
  { in_ip4: ipv4_input_pkt;
    in_tsp: transport_layer_input;
    in_chn: chain }.

Definition input_of_bytes (chn: chain) (bs: bytes) : option input :=
  match ipv4_decode bs with
  | Some ip4 =>
    let ip4_in := ipv4_input_pkt_of_pkt ip4 in
    match tcp_decode ip4 bs with
    | Some tcp => Some {| in_ip4 := ip4_in;
                         in_tsp := TCPInput (tcp_input_pkt_of_pkt tcp);
                         in_chn := chn |}
    | None => match udp_decode ip4 bs with
             | Some udp => Some {| in_ip4 := ip4_in;
                                  in_tsp := UDPInput (udp_input_pkt_of_pkt udp);
                                  in_chn := chn |}
             | None => None
             end
    end
  | None => None
  end.

(* Addresses are represented as N. *)
Definition address := N.

(* Conditions are the basic blocks of rules. *)
(* FIXME: This should use props instead of bools *)
Definition condition (A: Type) := A -> bool.

(* A rule takes a packet on a chain and makes a decision about that packet. *)
Definition rule := input -> option result.

(* An iptables invocation either adds a new rule or sets a default policy *)
Inductive invocation :=
  | Rule (r: rule)
  | Policy (c: chain) (p: result).

(* Rules are placed in chains; when a rule does not match a packet (i.e. returns *)
(*    [None], the next rule is evaluated. *)
Definition rulechain := list rule.

Fixpoint rule_of_rulechain (rc: rulechain) : rule :=
  fun i =>
    match rc with
    | [] => None
    | [r] => r i
    | r :: rules =>
      match r i with
      | Some res => Some res
      | None => rule_of_rulechain rules i
      end
    end.

Definition rule_of_invocation (inv: invocation) : input -> option result :=
  match inv with
  | Rule r => r
  | Policy _ _ => (fun _ => None)
  end.
Coercion rule_of_invocation : invocation >-> Funclass.

Definition rule_of_invocations (invs: list invocation) : rule :=
  rule_of_rulechain (map rule_of_invocation invs).

Definition policy_of_invocations (ch: chain) (invs: list invocation) (default: result) : result :=
  fold_left (fun acc inv => match inv with
                         | Rule r => acc
                         | Policy ch' p => if chain_beq ch ch' then p else acc
                         end) invs default.

(* Usual boolean operators can be lifted to conditions: *)
Definition combine_conditions {A} (op: bool -> bool -> bool) (c1 c2: A -> bool) : A -> bool :=
  fun a => op (c1 a) (c2 a).

Definition cond_negate {A} (cond: condition A) : condition A :=
  fun a => negb (cond a).

(* Packet conditions can be turned into input conditions: *)
Definition lift_condition {A B} (fn: A -> B) (cnd: B -> bool)
  : condition A :=
  fun a => cnd (fn a).

Definition lift_condition_opt {A B} (fn: A -> option B) (cnd: B -> bool)
  : condition A :=
  fun a => match (fn a) with
        | Some b => cnd b
        | None => false
        end.

(* Rules can be constructed from a condition and a result: *)
Definition invocation_of_condition (c: condition input) (r: result) :=
  Rule (fun i => if c i then Some r else None).

(** Here are some concrete conditions: **)

(* Check if we're running in a given chain *)
Definition cond_chain (c: chain) : condition chain :=
  fun chn => chain_beq chn c.

Record address_spec :=
  { saddr: address;
    smask: option N }.

(* Check if an address is in a subnet: *)
Definition match_address (spec: address_spec) (addr: address) : bool :=
  match spec.(smask) with
  | Some mask => N.eqb (N.land addr mask) (N.land spec.(saddr) mask)
  | None => N.eqb addr spec.(saddr)
  end.

Delimit Scope addr_scope with addr.

(* Check if the packet's source address is in a subnet *)
Definition cond_srcaddr (spec: address_spec)
  : condition ipv4_input_pkt :=
  fun pkt => match_address spec pkt.(ipv4_source).
Arguments cond_srcaddr spec%addr.

(* Check if the packet's destination address is in a subnet *)
Definition cond_dstaddr (spec: address_spec)
  : condition ipv4_input_pkt :=
  fun pkt => match_address spec pkt.(ipv4_dest).
Arguments cond_dstaddr spec%addr.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

(* Check if the packet encapsulates a given protocol *)
Definition cond_proto (proto: EnumType ["ICMP"; "TCP"; "UDP"])
  : condition ipv4_input_pkt :=
  fun pkt => N.eqb pkt.(ipv4_protocol) (N_of_fin proto).

Definition tcp_or_udp {A} ftcp fudp i : A :=
  match i.(in_tsp) with
  | TCPInput pkt => pkt.(ftcp)
  | UDPInput pkt => pkt.(fudp)
  end.

(* Filter by TCP or UDP source port *)
Definition cond_srcport port
  : condition input :=
  let fn := tcp_or_udp tcp_source_port udp_source_port in
  fun pkt => N.eqb pkt.(fn) port.

(* Filter by TCP or UDP destination port *)
Definition cond_dstport port
  : condition input :=
  let fn := tcp_or_udp tcp_dest_port udp_dest_port in
  fun pkt => Neqb pkt.(fn) port.

(** The following adds syntax for these conditions: **)

Delimit Scope iptables_scope with iptables.

Notation "cf '-P' chain policy" :=
  ((fun cf => Policy chain policy) cf)
    (at level 41, left associativity, chain at level 9, policy at level 9) : iptables_scope.

Record cond_and_flag {A} :=
  { cf_cond : condition A;
    cf_negate_next : bool }.

Definition and_cf {A} (cf: cond_and_flag) (c: condition A) :=
  let c := if cf.(cf_negate_next) then cond_negate c else c in
  {| cf_cond := combine_conditions andb cf.(cf_cond) c;
     cf_negate_next := false |}.

Notation "cf '-A' c" :=
  (and_cf cf (lift_condition in_chn (cond_chain c)))
    (at level 41, left associativity) : iptables_scope.

Notation "cf '--protocol' proto" :=
  (and_cf cf (lift_condition in_ip4 (cond_proto (```proto))))
    (at level 41, left associativity) : iptables_scope.

Definition mask_of_nat (m: nat) : N :=
  N.shiftl (N.ones (N.of_nat m)) (32 - N.of_nat m)%N.
(* Compute (NToWord 32 (mask_of_nat 5)). *)

(* Lemma wand_full_mask: *)
(*   forall w: word 32, (wand w (mask_of_nat 32)) = w. *)
(* Proof. *)
(*   intros. *)
(*   rewrite wand_comm. *)
(*   apply (@wand_unit 32 w). *)
(* Qed. *)

Coercion addr_spec_of_N (n: N) : address_spec :=
  {| saddr := n;
     smask := None |}.

Notation "addr / mask" :=
  {| saddr := addr;
     smask := Some (mask_of_nat mask) |}
    (at level 40, left associativity, format "addr / mask")
  : addr_scope.

Notation "cf '--source' addr" :=
  (and_cf cf (lift_condition in_ip4 (cond_srcaddr addr%addr)))
    (at level 41, left associativity) : iptables_scope.

Notation "cf '--destination' addr" :=
  (and_cf cf (lift_condition in_ip4 (cond_dstaddr addr%addr)))
    (at level 41, left associativity) : iptables_scope.

Notation "cf '--source-port' port" :=
  (and_cf cf (cond_srcport port%N))
    (at level 41, left associativity) : iptables_scope.

Notation "cf '--destination-port' port" :=
  (and_cf cf (cond_dstport port%N))
    (at level 41, left associativity) : iptables_scope.

Notation "cf '-j' result" :=
  (invocation_of_condition cf.(cf_cond) result)
    (at level 41, left associativity) : iptables_scope.

Notation "n ' m" :=
  ((n * (N.of_nat 256) + m)%N)
    (at level 38, format "n ' m", left associativity)
  : addr_scope.
Bind Scope addr_scope with N.

Notation "cf !" :=
  {| cf_cond := cf.(cf_cond);
     cf_negate_next := negb cf.(cf_negate_next) |}
    (at level 41, left associativity) : iptables_scope.

Notation "cf '--not'" :=
  (cf !)%iptables
    (at level 41, left associativity) : iptables_scope.

Definition iptables :=
  {| cf_cond := fun i: input => true;
     cf_negate_next := false |}.

(* The following sets up unfolding to observe implementations of iptables filters *)
Hint Unfold
     Common.option_bind
     rule_of_invocation rule_of_invocations policy_of_invocations
     iptables cond_dstaddr lift_condition lift_condition_opt
     match_address combine_conditions and_cf invocation_of_condition
     cond_proto cond_srcaddr cond_srcport cond_dstaddr cond_dstport
     tcp_or_udp : iptables.
