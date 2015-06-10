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