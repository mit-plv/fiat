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
        Fiat.BinEncoders.Env.Lib2.DomainNameOpt.

Require Import Fiat.Examples.DnsServer.Packet
        Fiat.Examples.DnsServer.DnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation
        Fiat.Examples.DnsServer.AuthoritativeDNSSchema.

Section BinaryDns.

  (* This "unresponsive" variant of an authoritative DNS Server responds*)
   (* by simply flipping the response bit in the packet without adding any *)
  (* records. It is intended as an initial example for Bedrock compilation. *)

  Definition association_list K V := list (K * V).

  Fixpoint association_list_find_first {K V}
           {K_eq : Query_eq K}
           (l : association_list K V)
           (k : K) : option V :=
    match l with
    | (k', v) :: l' => if A_eq_dec k k' then Some v else association_list_find_first l' k
    | _ => None
    end.

  Fixpoint association_list_find_all {K V}
           {K_eq : Query_eq K}
           (l : association_list K V)
           (k : K) : list V :=
    match l with
    | (k', v) :: l' => if A_eq_dec k k' then v :: association_list_find_all l' k
                       else association_list_find_all l' k
    | _ => nil
    end.

  Fixpoint association_list_add {K V}
           {K_eq : Query_eq K}
           (l : association_list K V)
           (k : K) (v : V) : list (K * V)  :=
    (k, v) :: l.

  Instance dns_list_cache : Cache :=
    {| CacheEncode := nat * association_list string pointerT;
       CacheDecode := nat * association_list pointerT string;
       Equiv ce cd := fst ce = fst cd /\
                      (snd ce) = (map (fun ps => match ps with (p, s) => (s, p) end) (snd cd))
    |}%type.

  Definition list_CacheEncode_empty : CacheEncode := (0, nil).
  Definition list_CacheDecode_empty : CacheDecode := (0, nil).

  Lemma list_cache_empty_Equiv : Equiv list_CacheEncode_empty list_CacheDecode_empty.
  Proof.
    simpl; intuition; simpl; econstructor.
  Qed.

  Instance cacheAddNat : CacheAdd _ nat :=
    {| addE ce n := (fst ce + n , snd ce);
       addD cd n := (fst cd + n, snd cd) |}.
  Proof.
    simpl; intuition eauto.
  Defined.

  Lemma ptr_eq_dec :
    forall (p p' : pointerT),
      {p = p'} + {p <> p'}.
  Proof.
    decide equality.
    apply weq.
    destruct a; destruct s; simpl in *.
    destruct (weq x x0); subst.
    left; apply ptr_eq; reflexivity.
    right; unfold not; intros; apply n.
    congruence.
  Qed.

  Instance : Query_eq pointerT :=
    {| A_eq_dec := ptr_eq_dec |}.

  Lemma natToWord_lt_combine
    : forall higher_bits : word 6,
      wlt (natToWord 8 191)  (combine higher_bits WO~1~1).
  Proof.
    intros.
    shatter_word higher_bits.
    rewrite <- (natToWord_wordToNat (combine _ _)).
    apply WordFacts.natToWord_wlt.
    - apply Nomega.Nlt_in; simpl; unfold Pos.to_nat; simpl; omega.
    - destruct x; destruct x0; destruct x1; destruct x2; destruct x3; destruct x4; simpl;
        apply Nomega.Nlt_in; simpl; unfold Pos.to_nat; simpl; omega.
    - destruct x; destruct x0; destruct x1; destruct x2; destruct x3; destruct x4; simpl;
        omega.
  Qed.

  Definition nat_to_pointerT (n : nat) : pointerT.
    refine (let oct_offset := wtl (wtl (wtl (natToWord 17 n))) in  (* convert bit offset to octet offset. *)
            let lower_bits := split1 8 6 oct_offset in
            let higher_bits := split2 8 6 oct_offset in (exist _ (combine higher_bits (WS true (WS true WO))) _, lower_bits)).
    apply natToWord_lt_combine.
  Qed.

  Instance cachePeekDNPointer : CachePeek _ pointerT :=
    {| peekE ce := nat_to_pointerT (fst ce);
       peekD cd := nat_to_pointerT (fst cd) |}.
  Proof.
    abstract (simpl; intros; intuition; subst).
  Qed.

  Instance cacheAddDNPointer : CacheAdd _ (string * pointerT) :=
    {| addE ce sp := (fst ce, association_list_add (snd ce) (fst sp) (snd sp));
       addD cd sp := (fst cd, association_list_add (snd cd) (snd sp) (fst sp)) |}.
  Proof.
    simpl; intuition eauto; simpl in *; subst; eauto.
  Qed.

  Instance cacheGetDNPointer : CacheGet _ string pointerT :=
    {| getE ce p := association_list_find_all (snd ce) p;
       getD ce p := association_list_find_first (snd ce) p|}.
  Proof.
    simpl.
    intros [? ?] [? ?] ? ?; simpl; intuition eauto; subst.
    - subst; induction a0; simpl in *; try congruence.
      destruct a; simpl in *; find_if_inside; subst.
      + find_if_inside; subst; simpl; eauto.
      + find_if_inside; subst; simpl; eauto; congruence.
    - subst; induction a0; simpl in *; intuition.
      destruct a; simpl in *; find_if_inside.
      + find_if_inside; subst; simpl; eauto; try congruence.
        apply IHa0 in H.
      + find_if_inside; subst; simpl; eauto; try congruence.
        simpl in H; intuition eauto.
        congruence.
  Qed.

  Variable IndependentCaches :
    forall env p (b : nat),
      getD (addD env b) p = getD env p.
  Variable GetCacheAdd_1 :
    forall env (p : pointerT) (domain : string),
      getD (addD env (domain, p)) p = Some domain.
  Variable GetCacheAdd_2 :
    forall env (p p' : pointerT) (domain : string),
      p <> p' -> getD (addD env (domain, p')) p = getD env p.
  Variable GoodCacheDecode :
    GoodCache cache cacheGetDNPointer cacheDecode_empty.

Require Import Fiat.BinEncoders.Env.Examples.DnsOpt.

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
              (encode_packet_Spec cache cacheAddNat cacheAddDNPointer cacheGetDNPointer cachePeekDNPointer) b cacheEncode_empty;
       Ifopt p as p' Then
         p' <- ret (buildempty true ``"NoError" p');
         b' <- encode_packet_Spec cache cacheAddNat cacheAddDNPointer cacheGetDNPointer cachePeekDNPointer p' cacheEncode_empty;
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
    refine (Pick_Decoder_For DNS_Packet_OK
              (encode_packet_Spec cache cacheAddNat cacheAddDNPointer cacheGetDNPointer cachePeekDNPointer) b cacheEncode_empty)
           (ret match fst (@packetDecoderImpl _ cacheAddNat cacheAddDNPointer cacheGetDNPointer cachePeekDNPointer) b cacheDecode_empty
                with
                | Some (p, _, _) => Some p
                | None => None
                end).
Proof.
  intros; eapply refine_Pick_Decoder_For with (decoderImpl := packet_decoder _ _ _ _ _ _ _ _); eauto.
  Grab Existential Variables.
  eauto.
  eauto.
  eauto.
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
