Require Import Fiat.Narcissus.Examples.NetworkStack.IPv4Header.
Require Import Fiat.Narcissus.Examples.NetworkStack.TCP_Packet.
Require Import Bedrock.Word.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import IndexedEnsembles.
Require Import Coq.Strings.String.


Definition sID := "ID".
Definition sPACKET := "Packet".
Definition port (p: nat) : word 16 := (natToWord 16 p).

Record Packet := packet
  { tcp_p: TCP_Packet;
    ip_h: IPv4_Packet; }.

Definition sHISTORY := "Packet History".
Definition PacketHistorySchema :=
  Query Structure Schema
    [ relation sHISTORY has
              schema < sPACKET :: Packet > ]
      enforcing [].

Definition filter_unit : Type := (QueryStructure PacketHistorySchema) -> Packet -> bool.
Definition pass_if_any (conds: list filter_unit) : filter_unit :=
  fun (r: QueryStructure PacketHistorySchema) (p: Packet) => (fold_right orb false (map (fun cond => (cond r p)) conds)).
Definition pass_if_all (conds: list filter_unit) : filter_unit :=
  fun (r: QueryStructure PacketHistorySchema) (p: Packet) => (fold_right andb true (map (fun cond => (cond r p)) conds)).

Definition FilterSig : ADTSig :=
    ADTsignature {
        Constructor "Init" : rep,
        Method "Filter" : rep * Packet -> rep * bool
    }.

(* always -A FORWARD, policy ACCEPT *)

Delimit Scope iptables_scope with iptables.

Notation "'*filter' rule1 , rule2 , .. , rulen" :=
  (Def ADT {
        rep := QueryStructure PacketHistorySchema,
        Def Constructor0 "Init" : rep := empty,,

        Def Method1 "Filter" (r: rep) (p: Packet) : rep * bool :=
            `(r, _) <- Insert < sPACKET :: p > into r!sHISTORY;
            ret (r, ((pass_if_any (rule1 :: (rule2 :: .. (rulen :: nil) .. ))) r p))
  }%methDefParsing) (at level 95) : iptables_scope.

Notation "'*filter' rule" :=
  (Def ADT {
        rep := QueryStructure PacketHistorySchema,
        Def Constructor0 "Init" : rep := empty,,

        Def Method1 "Filter" (r: rep) (p: Packet) : rep * bool :=
            `(r, _) <- Insert < sPACKET :: p > into r!sHISTORY;
            ret (r, (rule r p))
  }%methDefParsing) (at level 95) : iptables_scope.


Notation "'--sport' srcport" :=
  (fun (r: QueryStructure PacketHistorySchema) (p: Packet) => weqb (port srcport) p.(tcp_p).(SourcePort)) (at level 94) : iptables_scope.

Notation "'--dport' dstport" :=
  (fun (r: QueryStructure PacketHistorySchema) (p: Packet) => weqb (port dstport) p.(tcp_p).(DestPort)) (at level 94) : iptables_scope.

Notation "[ ip1 * ip2 * ip3 * ip4 ]" :=
  (((Word.combine (natToWord 8 ip4)) 24 ((Word.combine (natToWord 8 ip3)) 16 ((Word.combine (natToWord 8 ip2)) 8 (natToWord 8 ip1)))), 32) (at level 39, ip1, ip2, ip3, ip4 at next level) : iptables_scope.

Fixpoint make_mask' (zeros: nat) (len: nat) : (word len) :=
  match len with
  | O => WO
  | S len' => match zeros with
              | O => WS true (make_mask' O len')
              | S zeros' => WS false (make_mask' zeros' len')
              end
  end.

Definition make_mask (ones: nat) : word 32 := make_mask' (32 - ones) 32.

Notation "ipaddr // mask" := ((wand (fst ipaddr) (make_mask mask)), mask%nat)
  (at level 40) : iptables_scope.

Notation "'-s' srcaddr" :=
  (match srcaddr with
   | (addr, mask) => (fun (r: QueryStructure PacketHistorySchema) (p: Packet) => weqb (addr) (wand p.(ip_h).(SourceAddress) (make_mask mask)))
   end) (at level 41, only parsing) : iptables_scope.

Notation "'-d' dstaddr" :=
  (match dstaddr with
   | (addr, mask) => (fun (r: QueryStructure PacketHistorySchema) (p: Packet) => weqb (addr) (wand p.(ip_h).(DestAddress) (make_mask mask)))
   end) (at level 41, only parsing) : iptables_scope.

Notation "'-A' 'FORWARD' '-p' 'tcp' cond1 cond2 .. condn '-j' 'ACCEPT'" :=
  (pass_if_all (cond1 :: (cond2 :: .. (condn :: nil) .. ))) (at level 50, only parsing).

Notation "'-A' 'FORWARD' '-p' 'tcp' cond '-j' 'ACCEPT'" := cond (at level 50, only parsing).

(*
Compute ([ 192 * 168 * 1 * 1 ] // 8)%iptables.
Check (-s [ 192 * 168 * 0 * 1 ])%iptables.
Definition myrule := (-A FORWARD -p tcp -s [ 10 * 0 * 0 * 1 ] --dport 22 -j ACCEPT)%iptables.
Definition myfirewall :=
  (
    *filter
       myrule
  )%iptables.

Print myfirewall.
*)