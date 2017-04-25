Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Arith.Div2.

Require Import
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation.Decidable
        Fiat.Computation.IfDec
        Fiat.Computation.FoldComp
        Fiat.Computation.FueledFix
        Fiat.Computation.ListComputations
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import
        Bedrock.Word
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Examples.DnsOpt.

Require Import Fiat.Examples.DnsServer.Packet
        Fiat.Examples.DnsServer.DnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation
        Fiat.Examples.DnsServer.AuthoritativeDNSSchema.

Section BinaryDns.

  (* This "unresponsive" variant of an authoritative DNS Server responds*)
   (* by simply flipping the response bit in the packet without adding any *)
  (* records. It is intended as an initial example for Bedrock compilation. *)

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "AddData" : rep * resourceRecord -> rep * bool,
      Method "Process" : rep * ByteString -> rep * (option ByteString)
    }.

Definition DnsSpec : ADT DnsSig :=
  Def ADT {
    rep := QueryStructure DnsSchema,

    Def Constructor "Init" : rep := empty,,

    (* in start honing querystructure, it inserts constraints before *)
    (* every insert / decision procedure *)

    Def Method1 "AddData" (this : rep) (t : resourceRecord) : rep * bool :=
      Insert t into this!sRRecords,

    Def Method1 "Process" (this : rep) (b : ByteString) : rep * (option ByteString) :=
        p <- Pick_Decoder_For DNS_Packet_OK
              encode_packet_Spec b list_CacheEncode_empty;
       Ifopt p as p' Then
         p' <- ret (buildempty true ``"NoError" p');
         b' <- encode_packet_Spec p' list_CacheEncode_empty;
         ret (this, Some (fst b'))
       Else (* Not sure what to do in this case, will return None to *)
            (* the shim *)
       ret (this, None)
      }.

Local Opaque encode_packet_Spec.
Local Opaque packetDecoderImpl.

Instance ADomainName_eq : Query_eq DomainName := Astring_eq.
Instance ARRecordType_eq : Query_eq RRecordType :=
  {| A_eq_dec := fin_eq_dec |}.

Lemma refine_decode_packet
  : forall b,
    refine (Pick_Decoder_For DNS_Packet_OK encode_packet_Spec b list_CacheEncode_empty)
           (ret match fst packetDecoderImpl b list_CacheDecode_empty
                with
                | Some (p, _, _) => Some p
                | None => None
                end).
Proof.
  intros; eapply refine_Pick_Decoder_For with (decoderImpl := packet_decoder); eauto.
  apply list_cache_empty_Equiv.
  simpl.
  unfold GoodCache; simpl; intuition; congruence.
Qed.

Theorem DnsManual :
  {DnsImpl : _ & refineADT DnsSpec DnsImpl}.
Proof.
  eexists; unfold DnsSpec.
  pose_string_hyps; pose_heading_hyps.
  drop_constraintsfrom_DNS.
  { (* Add Data. *)
    etransitivity; set_evars; simpl in *.
    - match goal with
        H : DropQSConstraints_AbsR ?r_o ?r_n
        |- refine (u <- QSInsert ?r_o ?Ridx ?tup;
                   @?k u) _ =>
        eapply (@QSInsertSpec_refine_subgoals _ _ r_o r_n Ridx tup); try exact H
      end; try set_refine_evar.
      + rewrite decides_True; finish honing.
      + simpl; rewrite refine_noDup_CNAME_check_dns by eauto; finish honing.
      + simpl; set_evars; intros; setoid_rewrite refine_count_constraint_broken'; finish honing.
      + simpl; finish honing.
      + simpl; intros; finish honing.
      + intros. refine pick val _; eauto; simplify with monad laws.
        simpl; finish honing.
      + intros. refine pick val _; eauto; simplify with monad laws.
        simpl; finish honing.
    - unfold H1.
      doAny ltac:(drop_constraints)
                   drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
  }
  { (* Process *)
    doAny ltac:(drop_constraints)
                 drop_constraints_drill ltac:(repeat subst_refine_evar; cbv beta; simpl; try finish honing).
  }
  (* We should be doing automatic data structure selection here. *)
  make_simple_indexes ({|prim_fst := [(EqualityIndex, @Fin.F1 4);
                                      (EqualityIndex, Fin.FS (Fin.FS (Fin.FS (@Fin.F1 1))))
                                     ];
                         prim_snd := () |} : prim_prod (list (string * Fin.t 5)) ())
  ltac:(CombineCase6 BuildEarlyFindPrefixIndex ltac:(LastCombineCase6 BuildEarlyEqualityIndex))
         ltac:(CombineCase5 BuildLastFindPrefixIndex ltac:(LastCombineCase5 BuildLastEqualityIndex)).
  + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + doAny implement_insert''
          ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
  + simplify with monad laws.
    rewrite  refine_decode_packet.
    doAny implement_insert''
          ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
  + hone method "AddData".
    subst.
    doAny ltac:(first [rewrite refine_bind_bind
                      | rewrite refine_bind_unit
                      | rewrite refineEquiv_pick_eq'
                      | simplify with monad laws])
                 ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars; simpl) ltac:(finish honing).
    simpl.
    apply reflexivityT.
    Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).
Print DNSImpl.
