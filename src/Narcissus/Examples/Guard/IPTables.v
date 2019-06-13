(** This file implements a limited form of iptables syntax. **)

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Fiat.Narcissus.Examples.Guard.Core.

(** We start with some definitions: **)

(* Although we can add rules to each chain, FORWARD will be the only
   meaningful one for us. *)
Inductive chain := INPUT | FORWARD | OUTPUT.
Scheme Equality for chain.

(* The guard's filter functions take a decoded packet and a chain
   identifier as input.  *)
Record input :=
  { in_ip4: option IPv4_Packet;
    in_tcp: option TCP_Packet;
    in_udp: option UDP_Packet;
    in_chn: chain }.

Definition input_of_bytes (chn: chain) (bs: bytes) :=
  let opt_hdr := ipv4_decode bs in
  {| in_ip4 := opt_hdr;
     in_tcp := Common.option_bind (fun hdr => tcp_decode hdr bs) opt_hdr;
     in_udp := Common.option_bind (fun hdr => udp_decode hdr bs) opt_hdr;
     in_chn := chn |}.

(* Addresses are represented as machine words. *)
Definition address := word 32.

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
                         | Policy ch' p => if chain_beq ch' ch then p else acc
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
  fun chn => chain_beq c chn.

Record address_spec :=
  { saddr: address;
    smask: word 32 }.

(* Check if an address is in a subnet: *)
Definition match_address (spec: address_spec) (addr: address) : bool :=
  weqb (addr ^& spec.(smask))
       (spec.(saddr) ^& spec.(smask)).

Delimit Scope addr_scope with addr.

(* Check if the packet's source address is in a subnet *)
Definition cond_srcaddr (spec: address_spec)
  : condition IPv4_Packet :=
  fun pkt => match_address spec pkt.(SourceAddress).
Arguments cond_srcaddr spec%addr.

(* Check if the packet's destination address is in a subnet *)
Definition cond_dstaddr (spec: address_spec)
  : condition IPv4_Packet :=
  fun pkt => match_address spec pkt.(DestAddress).
Arguments cond_dstaddr spec%addr.

Require Import Coq.Vectors.Vector.
Import VectorNotations.

(* Check if the packet encapsulates a given protocol *)
Definition cond_proto (proto: EnumType ["ICMP"; "TCP"; "UDP"])
  : condition IPv4_Packet :=
  fun pkt => Fin.eqb pkt.(Protocol) proto.

Scheme Equality for option.

Definition tcp_or_udp {A} ftcp fudp i : option A :=
  match i.(in_tcp), i.(in_udp) with
  | Some p, _ => Some p.(ftcp)
  | _, Some p => Some p.(fudp)
  | None, None => None
  end.

(* Filter by TCP or UDP source port *)
Definition cond_srcport (port: word 16)
  : condition input :=
  let fn := tcp_or_udp TCP_Packet.SourcePort UDP_Packet.SourcePort in
  fun pkt => option_beq _ (@weqb 16) pkt.(fn) (Some port).

(* Filter by TCP or UDP destination port *)
Definition cond_dstport (port: word 16)
  : condition input :=
  let fn := tcp_or_udp TCP_Packet.DestPort UDP_Packet.DestPort in
  fun pkt => option_beq _ (@weqb 16) pkt.(fn) (Some port).

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
  (and_cf cf (lift_condition_opt in_ip4 (cond_proto (```proto))))
    (at level 41, left associativity) : iptables_scope.

Definition mask_of_nat (m: nat) : word (m + (32 - m)) :=
    wnot (@zext m (wones m) (32 - m)).

(* Definition addr_tuple := (N * N * N * N)%type. *)

(* Coercion addr_of_tuple (tup: addr_tuple) : word 32 := *)
(*   let '(uuuu, uuu, uu, u) := tup in *)
(*   NToWord 32 (uuuu * (Npow2 24) + uuu * (Npow2 16) + uu * (Npow2 8) + u). *)

Coercion addr_spec_of_N (n: N) : address_spec :=
  {| saddr := NToWord 32 n;
     smask := wones 32 |}.

Notation "addr / mask" :=
  {| saddr := NToWord 32 addr;
     smask := mask_of_nat mask |}
    (at level 40, left associativity, format "addr / mask")
  : addr_scope.

Notation "cf '--source' addr" :=
  (and_cf cf (lift_condition_opt in_ip4 (cond_srcaddr addr%addr)))
    (at level 41, left associativity) : iptables_scope.

Notation "cf '--destination' addr" :=
  (and_cf cf (lift_condition_opt in_ip4 (cond_dstaddr addr%addr)))
    (at level 41, left associativity) : iptables_scope.

Notation "cf '--source-port' port" :=
  (and_cf cf (cond_srcport (NToWord 16 port%N)))
    (at level 41, left associativity) : iptables_scope.

Notation "cf '--destination-port' port" :=
  (and_cf cf (cond_dstport (NToWord 16 port%N)))
    (at level 41, left associativity) : iptables_scope.

Notation "cf '-j' result" :=
  (invocation_of_condition cf.(cf_cond) result)
    (at level 41, left associativity) : iptables_scope.

Notation "n * m" :=
  ((n * (N.of_nat 256) + m)%N)
    (at level 40, format "n * m", left associativity)
  : addr_scope.

(* Notation "'ipv4:' a : b : c : d" := : iptables *)
(*   (NToWord 32 (a * (Npow2 24) + b * (Npow2 16) + c * (Npow2 8) + d)) *)
(*     (at level 38, left associativity) *)
(*   : addr_scope. *)

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
