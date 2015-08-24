(*Require HintDbTactics.*)          (* plugin to pass a hint db to a tactic *)

Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsSchema
        Fiat.Examples.DnsServer.DnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation.

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "AddData" : rep x DNSRRecord -> rep x bool,
      Method "Process" : rep x packet -> rep x packet
    }.

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

                                               (* in start honing querystructure, it inserts constraints before every insert / decision procedure *)
                                               (* n<- count (For (r in _) where (r = tup) return True); if n > () then.. *)
                                               (* For refines decision procedure *)
    update "AddData" (this : rep, t : DNSRRecord) : bool :=
      Insert t into this!sCOLLECTIONS,

    query "Process" (this : rep, p : packet) : packet :=
      let t := qtype (questions p) in
      Repeat 1 initializing n with qname (questions p)
               defaulting rec with (ret (buildempty p))
         {{ rs <- For (r in this!sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                  Where (IsPrefix r!sNAME n) (* prefixed with [n] to [rs] *)
                  (* prefix: "com.google" is a prefix of "com.google.scholar" *)
                  Return r;
            If (negb (is_empty rs))        (* Are there any matching records? *)
               (* TODO: this does not filter by matching QTYPE *)
            Then
              bfrs <- [[r in rs | upperbound name_length rs r]]; (* Find the best match (largest prefix) in [rs] *)
              b <- { b | decides b (forall r, List.In r bfrs -> n = r!sNAME) };
              if b                (* If the record's QNAME is an exact match  *)
              then
                unique b,                         (* only one match (unique / otherwise) *)
                List.In b bfrs /\ b!sTYPE = CNAME     (* If the record is a CNAME, *)
                               /\ t <> CNAME ->>      (* and the query did not request a CNAME *)

                  p' <- rec b!sNAME;                  (* Recursively find records matching the CNAME *)
                                                    (* ?? Shouldn't this use the sDATA ?? *)
                  ret (addan p' b)
                      (* addan : packet -> DNSRRecord -> packet *)
                otherwise ->>     (* Copy the records into the answer section of an empty response *)
                (* multiple matches -- add them all as answers in the packet *)
                  ret (List.fold_left addan bfrs (buildempty p))
              else              (* prefix but record's QNAME not an exact match *)
                (* return all the prefix records that are nameserver records --
                 ask the authoritative servers *) (* TODO does this return one, or return all? *)
                bfrs' <- [[x in bfrs | x!sTYPE = NS]];
                ret (List.fold_left addns bfrs' (buildempty p))
            Else ret (buildempty p) (* No matching records! *)
          }}}.

Theorem DnsManual :
  FullySharpened DnsSpec.
Proof.

  start sharpening ADT.

  hone method "Process".
  { Time doAnyAll. } (* 241 seconds = 4 minutes *)

  start_honing_QueryStructure'.

  hone method "AddData".
  { Time doAnyAll. } (* 202 seconds = 3.5 minutes *)

  finish_planning ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics)
  ltac:(fun make_index =>
          make_index ({| prim_fst := [("FindPrefixIndex", Fin.F1)]; prim_snd := () |}
                                                : @ilist3 RawHeading
                                  (fun heading : RawHeading => list (prod string (Attributes heading)))
                                  (numRawQSschemaSchemas (QueryStructureSchemaRaw DnsSchema))
                                  (Vector.map rawSchemaHeading (qschemaSchemas DnsSchema)))).

Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).

Print DNSImpl.

(* TODO extraction, examples/messagesextraction.v *)
