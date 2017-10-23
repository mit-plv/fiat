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
          where (fun t t' =>
                   (* Constraints on every pair of tuples: *)
                   (t!sNAME = t'!sNAME
                    -> RDataTypeToRRecordType (t!sRDATA) <> CNAME)
                   (* if a domain name is an alias, the CNAME record *)
                   (* is the only resource record in the table. *)
                   /\ (RDataTypeToRRecordType t!sRDATA = NS
                       -> RDataTypeToRRecordType t'!sRDATA <> NS
                       -> prefix (t!sNAME) (t'!sNAME)
                       -> t!sNAME = t'!sNAME)
        (* If the server delegates authority for a zone via a NS record *)
        (* Then any other (non-NS) records about that subzone have to be *)
        (* glue records, i.e. have the same label as the NS record.  *)
        )]
        enforcing [ ].
