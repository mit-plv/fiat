Require HintDbTactics.          (* plugin to pass a hint db to a tactic *)

Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindSuffixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation
        Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsSchema
        Fiat.Examples.DnsServer.DnsLemmas.


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
                                               (* n<- count (For (r in _) where (r = tup) return True); if n > 0 then.. *)
                                               (* For refines decision procedure *)
    update "AddData" (t : DNSRRecord) : bool :=
      Insert t into sCOLLECTIONS,

    query "Process" (p : packet) : packet :=
      let t := qtype (questions p) in
      Repeat 1 initializing n with qname (questions p)
               defaulting rec with (ret (buildempty p))
         {{ rs <- For (r in sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                  Where (IsSuffix n r!sNAME) (* prefixed with [n] to [rs] *)
                  (* prefix: "com.google" is a prefix of "com.google.scholar" *)
                  Return r;
            If (negb (is_empty rs))        (* Are there any matching records? *)
            Then                    (* TODO: reverse these if/then cases *)
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
                 ask the authoritative servers *)
                bfrs' <- [[x in bfrs | x!sTYPE = NS]];
                ret (List.fold_left addns bfrs' (buildempty p))
            Else ret (buildempty p) (* No matching records! *)
          }}}.

(* ---------------- *)

Lemma rewrite_test : forall  (heading : Heading)
  (r_n : UnConstrQueryStructure DnsSchema)
  (n : DNSRRecord)
  (a : nat) (P P' : Ensemble (@Tuple heading)) (R : Ensemble (@IndexedTuple heading)),
    exists x,
      (* try under binder *)
   refine (
      x0 <- ret true;
       For
         (@QueryResultComp heading (@Tuple heading) R
                   (fun tup : Tuple => 
                      Where (P tup /\ P' tup)
                    Return tup ))
      )
     x.
Proof.
  Check @refine_subcheck_to_filter.
  intros.
  eexists.
  simpl.
  (* set_evars. *)
  (* apply refine_bind. *)
  (* reflexivity. *)
  (* apply refine_under_bind; intros. *)
  (* rewrite works with this and fails without it *)
  Check refine_subcheck_to_filter.
  SearchAbout pointwise_relation.
  assert (DecideableEnsemble P) as dec. admit.

  assert (DecideableEnsemble P') as dec'. admit.
assert ( forall l : list Tuple,
       For (QueryResultComp R (fun tup : Tuple => Where (P tup)
                                Return tup )) ↝ l) as comp. admit.

  setoid_rewrite (@refine_subcheck_to_filter _ _ _ _ _ _).
Admitted.

Lemma rewrite_test_ret : forall  (heading : Heading)
  (r_n : UnConstrQueryStructure DnsSchema)
  (n : DNSRRecord)
  (a : nat) (P P' : Ensemble (@Tuple heading)) (R : Ensemble (@IndexedTuple heading)),
    exists x,
   refine (
       ret (For
         (@QueryResultComp heading (@Tuple heading) R
                   (fun tup : Tuple =>
                      Where (P tup /\ P' tup)
                    Return tup ))))
     x.
Proof.
  intros.
  eexists.
  simpl.
  Check refine_subcheck_to_filter.
  set_evars.
  (* returning "set of even numbers"
2 is a valid refinement of this
but returning 

not true: {{2}} c {{e}}

only thing to rewrite with in a ret is an equal thing

 *)
  (* setoid_rewrite refine_subcheck_to_filter. *)
(* different error *)
Admitted.
