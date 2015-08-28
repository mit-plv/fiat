Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii Coq.Bool.Bool
        Coq.Bool.Bvector Coq.Lists.List.

Require Import
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.Examples.DnsServer.packet_new.

Definition DnsSchema :=
  Query Structure Schema
        [ relation sCOLLECTIONS has
                   schema
                  <sNAME :: name,
                   sTYPE :: RRecordType,
                   sCLASS :: RRecordClass,
                   sTTL :: nat,
                   sDATA :: name>
          where (fun t t' => t!sNAME = t'!sNAME -> t!sTYPE <> CNAME) ]
        (* constraint on every pair of tuples: an ip address cannot have multiple aliases *)
        enforcing [ ].