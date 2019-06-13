Require Import Fiat.ADT Fiat.ADTNotation.

Require Import Fiat.Narcissus.Examples.Guard.Core.
Require Export Fiat.Narcissus.Examples.Guard.IPTables.
Require Export Fiat.Narcissus.Examples.Guard.Ports.

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
               (db, match rule input with
                    | Some res => res
                    | None => policy
                    end)))
  }%methDefParsing).
