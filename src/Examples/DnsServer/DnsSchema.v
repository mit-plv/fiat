Require Import
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.Examples.DnsServer.packet.

Definition DnsSchema :=
  Query Structure Schema
        [ relation sCOLLECTIONS has
                   schema
                  <sNAME :: name,
                   sTYPE :: RRecordType,
                   sCLASS :: RRecordClass,
                   sTTL :: nat,
                   sDATA :: string>
          where (fun t t' => t!sNAME = t'!sNAME -> t!sTYPE <> CNAME) ]
        (* constraint on every pair of tuples: an ip address cannot have multiple aliases? *)
        enforcing [ ].

(* TODO recompile and change the other one to use DnsRecSchema *)
(* TODO move string defs elsewhere? *)

Definition sCACHE := "Cache".
Definition sREQUESTS := "Requests".
Definition sSTAGE := "Stage".
Definition sID := "ID".
Definition IP := name.
Definition sIP := "IP".
(* the # prefix it's on, from front? or back? *)
(* Definition sTIME := "Time". *)
(* everything added gets an unique ID already *)

Definition Stage := option nat.
Definition id : Type := nat.

Definition DnsRecSchema :=
  Query Structure Schema
        [ relation sCACHE has
                   schema
                  <sNAME :: name,
                    sIP :: IP,
                    sID :: id> ;            (* proxy for time *)
          relation sREQUESTS has
                   schema
                  < sID :: id,
                    sNAME :: name,
                    sSTAGE :: Stage> ]
          (* where (fun t t' => True) ] *)
        (* can i have an invariant that just works on one tuple?
         i want to encode that Stage <= length name *)
        (* use an attribute constraint TODO *)
        enforcing [ ].