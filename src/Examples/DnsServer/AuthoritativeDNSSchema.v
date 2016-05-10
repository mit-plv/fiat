Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation.Decidable
        Fiat.Computation.FoldComp
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import
        Fiat.Examples.DnsServer.Packet.

Definition DnsSchema :=
  Query Structure Schema
        [ relation sRRecords has
                   schema resourceRecordHeading
          where (fun t t' => t!sNAME = t'!sNAME -> t!sTYPE <> CNAME) ]
        (* constraint on every pair of tuples: if a domain name is an alias, the CNAME record *)
        (* is the only resource record in the table. *)
        enforcing [ ].
