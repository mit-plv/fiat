Require Import Fiat.ADT Fiat.ADTNotation Fiat.ADTRefinement Fiat.ADTRefinement.BuildADTRefinements.
Require Import Fiat.Narcissus.Examples.IPTables.

Definition GuardSig : ADTSig := ADTsignature {
  Constructor "Init" : rep,
  Method "ProcessPacket" : rep * bytes -> rep * result
}.

(* Require Import Fiat.Narcissus.Examples.NetworkStack.IPv4Header. *)
(* Require Import Fiat.Narcissus.Examples.NetworkStack.TCP_Packet. *)
(* Require Import Fiat.Narcissus.Formats.ByteBuffer. *)

Require Import Narcissus.OCamlExtraction.Extraction.

Notation simplified x :=
  ltac:(let xx := (eval simpl in x) in
        exact xx).

Notation zeta x :=
  ltac:(let xx := (eval cbv zeta in x) in
        exact xx).

Require Import List.
Import ListNotations.

(* Require Import Fiat.Computation.Core. *)

Definition protected_let {A B} (a: A) (k: A -> B) : B :=
  k a.

Notation "'IPGuard' {{ inv1 ;;  .. ;;  invn }}" :=
  (Def ADT {
     rep := unit,

     Def Constructor0 "Init" : rep := ret tt,,

     Def Method1 "ProcessPacket" (db : rep) (bs : bytes) : rep * result :=
       let invocations := (List.cons inv1 .. (List.cons invn List.nil) ..) in
       let rule := rule_of_invocations invocations in
       let policy := policy_of_invocations FORWARD invocations DROP in
       ret (protected_let (input_of_bytes FORWARD bs) (fun input =>
               (pair db match rule input with
                        | Some res => res
                        | None => policy
                        end)))
  }%methDefParsing : ADT GuardSig) : guard.

Delimit Scope guard with guard.
Open Scope guard.

Definition GuardSpec :=
  (IPGuard {{
    iptables -P FORWARD DROP;;
    iptables -A FORWARD
             --protocol "UDP"
             --source-port bootpc
             --destination 255*255*255*255
             -j ACCEPT
          }}).

Arguments andb : simpl nomatch.
Arguments Word.NToWord : simpl never.
Arguments Word.wones : simpl never.
Arguments Word.wzero : simpl never.
Arguments Word.zext : simpl never.
Hint Rewrite Bool.andb_true_l : iptables.

Ltac t_ :=
  match goal with
  | _ => progress (subst || cbn)
  | _ => progress (autounfold with iptables || autorewrite with iptables)
  | _ => simplify with monad laws
  | _ => refine pick eq
  end.

Ltac t := repeat t_.

Ltac guardc :=
  start sharpening ADT;
  hone representation using eq; t;
    [ finish honing.. | finish_SharpeningADT_WithoutDelegation ].

Theorem SharpenedGuard :
  FullySharpened GuardSpec.
Proof. guardc. Defined.

Definition GuardImpl :=
  Eval cbn in projT1 SharpenedGuard.

Require Import Coq.Strings.String Coq.Bool.Bool.
Open Scope string_scope.

Notation simp x :=
  ltac:(let x := (eval red in x) in
        let x := (eval cbn in x) in
        exact x).

Definition guard_init : ComputationalADT.cRep GuardImpl :=
  simp (CallConstructor GuardImpl "Init").

Definition guard_process_packet (bs: bytes) (rep: ComputationalADT.cRep GuardImpl) : (_ * result) :=
  simp (CallMethod GuardImpl "ProcessPacket" rep bs).

Require Import Fiat.Common.String_as_OT.
Require Import Coq.Structures.OrderedTypeEx.

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

Extract Constant Nat.ltb => "(<)".
Extract Constant Nat.leb => "(<=)".

Extract Inlined Constant Core.char => "Int64Word.t".

(* Extract Inductive Vector.t => "ListVector.t" ["(ListVector.empty ())" "ListVector.cons"] "ListVector.destruct". *)
(* Extract Inductive VectorDef.t => "ListVector.t" ["(ListVector.empty ())" "ListVector.cons"] "ListVector.destruct". *)
(* Extract Inlined Constant Vector.nth => "ListVector.nth". *)
(* Extract Inlined Constant AlignedDecodeMonad.Vector_nth_opt => "ListVector.nth_opt". *)
(* Extract Inlined Constant ith => "ListVector.ith". *)
(* Extract Inlined Constant ith2 => "ListVector.ith2". *)

Require Import ExtrOcamlZInt.
Extract Inlined Constant Word.NToWord => "Int64Word.of_n".
Extraction "tcpfilter.ml" guard_init guard_process_packet.

