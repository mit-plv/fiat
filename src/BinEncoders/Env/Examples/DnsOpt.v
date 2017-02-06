Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Examples.DnsServer.Packet
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.StringOpt
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt
        Fiat.BinEncoders.Env.Lib2.DomainNameOpt
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant.

Require Import
        Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.

Section DnsPacket.

  Open Scope Tuple_scope.

  Variable cache : Cache.
  Variable cacheAddNat : CacheAdd cache nat.
  Variable cacheAddDNPointer : CacheAdd cache (string * pointerT).
  Variable cacheGetDNPointer : CacheGet cache string pointerT.
  Variable cachePeekDNPointer : CachePeek cache pointerT.
  Variable IndependentCaches :
    forall env p (b : nat),
      getD (addD env b) p = getD env p.
  Variable GetCacheAdd_1 :
    forall env (p : pointerT) (domain : string),
      getD (addD env (domain, p)) p = Some domain.
  Variable GetCacheAdd_2 :
    forall env (p p' : pointerT) (domain : string),
      p <> p' -> getD (addD env (domain, p')) p = getD env p.

  Definition GoodCache (env : CacheDecode) :=
    forall domain p,
      getD env p = Some domain
      -> ValidDomainName domain
         /\ (String.length domain > 0)%nat.

  Lemma cacheIndependent_add
    : forall (b : nat) (cd : CacheDecode),
      GoodCache cd -> GoodCache (addD cd b).
  Proof.
    unfold GoodCache; intros.
    rewrite IndependentCaches in *; eauto.
  Qed.

  Lemma cacheIndependent_add_2
    : forall cd p (b : nat) domain,
      GoodCache cd
      -> getD (addD cd b) p = Some domain
      -> forall pre label post : string,
          domain = (pre ++ label ++ post)%string ->
          ValidLabel label -> (String.length label <= 63)%nat.
  Proof.
    unfold GoodCache; intros.
    rewrite IndependentCaches in *; eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_3
    : forall cd p (b : nat) domain,
      GoodCache cd
      -> getD (addD cd b) p = Some domain
      -> ValidDomainName domain.
  Proof.
    unfold GoodCache; intros.
    rewrite IndependentCaches in *; eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_4
    : forall cd p (b : nat) domain,
      GoodCache cd
      -> getD (addD cd b) p = Some domain
      -> gt (String.length domain) 0.
  Proof.
    unfold GoodCache; intros.
    rewrite IndependentCaches in *; eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_5
    : forall cd p domain,
      GoodCache cd
      -> getD cd p = Some domain
      -> ValidDomainName domain.
  Proof.
    unfold GoodCache; intros.
    eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_6
    : forall cd p domain,
      GoodCache cd
      -> getD cd p = Some domain
      -> gt (String.length domain) 0.
  Proof.
    unfold GoodCache; intros.
    eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_7
    : forall cd p domain,
      GoodCache cd
      -> getD cd p = Some domain
      -> forall pre label post : string,
          domain = (pre ++ label ++ post)%string ->
          ValidLabel label -> (String.length label <= 63)%nat.
  Proof.
    unfold GoodCache; intros.
    eapply H; eauto.
  Qed.

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

  Lemma cacheIndependent_add_8
    : forall cd p p0 domain domain',
      GoodCache cd
      -> ValidDomainName domain' /\ (String.length domain' > 0)%nat
      -> getD (addD cd (domain', p0)) p = Some domain
      -> forall pre label post : string,
          domain = (pre ++ label ++ post)%string ->
          ValidLabel label -> (String.length label <= 63)%nat.
  Proof.
    unfold GoodCache; intros.
    destruct (ptr_eq_dec p p0); subst.
    - rewrite GetCacheAdd_1 in H1; injections.
      destruct H0.
      eapply H0; eauto.
    - rewrite GetCacheAdd_2 in H1 by eauto.
      eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_9
    : forall cd p p0 domain domain',
      GoodCache cd
      -> ValidDomainName domain' /\ (String.length domain' > 0)%nat
      -> getD (addD cd (domain', p0)) p = Some domain
      -> ValidDomainName domain.
  Proof.
    unfold GoodCache; intros.
    destruct (ptr_eq_dec p p0); subst.
    - rewrite GetCacheAdd_1 in H1; injections.
      destruct H0.
      eapply H0; eauto.
    - rewrite GetCacheAdd_2 in H1 by eauto.
      eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_10
    : forall cd p p0 domain domain',
      GoodCache cd
      -> ValidDomainName domain' /\ (String.length domain' > 0)%nat
      -> getD (addD cd (domain', p0)) p = Some domain
      -> gt (String.length domain) 0.
  Proof.
    unfold GoodCache; intros.
    destruct (ptr_eq_dec p p0); subst.
    - rewrite GetCacheAdd_1 in H1; injections.
      destruct H0; apply H1.
    - rewrite GetCacheAdd_2 in H1 by eauto.
      eapply H; eauto.
  Qed.

  Ltac solve_GoodCache_inv foo :=
    lazymatch goal with
      |- cache_inv_Property ?Z _ =>
      unify Z GoodCache;
      unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try match goal with
            H : _ = _ |- _ =>
            try solve [ eapply cacheIndependent_add_3 in H; intuition eauto ];
            try solve [ eapply cacheIndependent_add_9 in H; intuition eauto ];
            try solve [ eapply cacheIndependent_add_5 in H; intuition eauto ]
          end;
      try solve [instantiate (1 := fun _ => True); exact I]
    end.

  Definition transformer : Transformer ByteString := ByteStringQueueTransformer.

  Opaque pow2. (* Don't want to be evaluating this. *)

  Lemma validDomainName_proj1_OK
    : forall domain,
      ValidDomainName domain
      -> decides true
                 (forall pre label post : string,
                     domain = (pre ++ label ++ post)%string ->
                     ValidLabel label -> (String.length label <= 63)%nat).
  Proof.
    simpl; intros; eapply H; eauto.
  Qed.

  Lemma validDomainName_proj2_OK
    : forall domain,
      ValidDomainName domain
      ->
      decides true
              (forall pre post : string,
                  domain = (pre ++ "." ++ post)%string ->
                  post <> ""%string /\
                  pre <> ""%string /\
                  ~ (exists s' : string, post = String "." s') /\
                  ~ (exists s' : string, pre = (s' ++ ".")%string)).
  Proof.
    simpl; intros; apply H; eauto.
  Qed.

  Hint Resolve validDomainName_proj1_OK : decide_data_invariant_db.
  Hint Resolve validDomainName_proj2_OK : decide_data_invariant_db.
  Hint Resolve FixedList_predicate_rest_True : data_inv_hints.

  Definition resourceRecord_OK (rr : resourceRecord) :=
    SumType_index
      ((Memory.W : Type)
         :: DomainName
         :: DomainName
         :: SOA_RDATA
         :: WKS_RDATA :: DomainName :: HINFO_RDATA :: MINFO_RDATA :: MX_RDATA :: [string : Type])
      rr!sRDATA = rr!sTYPE /\
    ith
      (icons (B := fun T => T -> Prop) (fun _ : Memory.W => True)
             (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
                    (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
                           (icons (B := fun T => T -> Prop) (fun a : SOA_RDATA =>
                                                               (True /\ ValidDomainName a!"contact_email") /\ ValidDomainName a!"sourcehost")
                                  (icons (B := fun T => T -> Prop) (fun a : WKS_RDATA => True /\ (lt (|a!"Bit-Map" |)  (pow2 16)))
                                         (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
                                                (icons (B := fun T => T -> Prop) (fun a : HINFO_RDATA =>
                                                                                    (True /\ True /\ (lt (String.length a!"OS") (pow2 8))) /\
                                                                                    True /\ (lt (String.length a!"CPU") (pow2 8)))
                                                       (icons (B := fun T => T -> Prop) (fun a : MINFO_RDATA =>
                                                                                           (True /\ ValidDomainName a!"eMailBx") /\
                                                                                           ValidDomainName a!"rMailBx")
                                                              (icons (B := fun T => T -> Prop) (fun a : MX_RDATA => True /\ ValidDomainName a!"Exchange")
                                                                     (icons (B := fun T => T -> Prop) (fun a : string =>
                                                                                                         True /\ True /\ (lt (String.length a) (pow2 8))) inil))))))))))
      (SumType_index
         ((Memory.W : Type)
            :: DomainName
            :: DomainName
            :: SOA_RDATA
            :: WKS_RDATA
            :: DomainName :: HINFO_RDATA :: MINFO_RDATA :: MX_RDATA :: [string : Type])
         rr!sRDATA)
      (SumType_proj
         ((Memory.W : Type)
            :: DomainName
            :: DomainName
            :: SOA_RDATA
            :: WKS_RDATA
            :: DomainName :: HINFO_RDATA :: MINFO_RDATA :: MX_RDATA :: [string : Type])
         rr!sRDATA)
    /\ ValidDomainName rr!sNAME.

  Lemma resourceRecordOK_1
    : forall data : resourceRecord,
      resourceRecord_OK data -> (fun domain : string => ValidDomainName domain) data!sNAME.
  Proof.
    unfold resourceRecord_OK; intuition eauto.
  Qed.
  Hint Resolve resourceRecordOK_1 : data_inv_hints.

  Lemma resourceRecordOK_2
    : forall data idx,
      data!sTYPE = idx ->
      resourceRecord_OK data -> SumType_index ResourceRecordTypeTypes data!sRDATA = idx.
    unfold resourceRecord_OK; intuition eauto.
    subst.
    apply H1.
  Qed.

  Hint Resolve resourceRecordOK_2 : data_inv_hints.

  Lemma resourceRecordOK_3
    : forall rr : resourceRecord,
      resourceRecord_OK rr ->
      ith
        (icons (B := fun T => T -> Prop) (fun _ : Memory.W => True)
               (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
                      (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
                             (icons (B := fun T => T -> Prop) (fun a : SOA_RDATA =>
                                                                 (True /\ ValidDomainName a!"contact_email") /\ ValidDomainName a!"sourcehost")
                                    (icons (B := fun T => T -> Prop) (fun a : WKS_RDATA => True /\ (lt (|a!"Bit-Map" |)  (pow2 16)))
                                           (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
                                                  (icons (B := fun T => T -> Prop) (fun a : HINFO_RDATA =>
                                                                                      (True /\ True /\ (lt (String.length a!"OS") (pow2 8))) /\
                                                                                      True /\ (lt (String.length a!"CPU") (pow2 8)))
                                                         (icons (B := fun T => T -> Prop) (fun a : MINFO_RDATA =>
                                                                                             (True /\ ValidDomainName a!"eMailBx") /\
                                                                                             ValidDomainName a!"rMailBx")
                                                                (icons (B := fun T => T -> Prop) (fun a : MX_RDATA => True /\ ValidDomainName a!"Exchange")
                                                                       (icons (B := fun T => T -> Prop) (fun a : string =>
                                                                                                           True /\ True /\ (lt (String.length a) (pow2 8))) inil))))))))))
        (SumType_index ResourceRecordTypeTypes rr!sRDATA)
        (SumType_proj ResourceRecordTypeTypes rr!sRDATA).
    intros ? H; apply H.
  Qed.
  Hint Resolve resourceRecordOK_3 : data_inv_hints.

  Lemma length_app_3 {A}
    : forall n1 n2 n3 (l1 l2 l3 : list A),
      length l1 = n1
      -> length l2 = n2
      -> length l3 = n3
      -> length (l1 ++ l2 ++ l3) = n1 + n2 + n3.
  Proof.
    intros; rewrite !app_length; subst; omega.
  Qed.
  Hint Resolve length_app_3 : data_inv_hints .

  Definition DNS_Packet_OK (data : packet) :=
    lt (|data!"answers" |) (pow2 16)
    /\ lt (|data!"authority" |) (pow2 16)
    /\ lt (|data!"additional" |) (pow2 16)
    /\ ValidDomainName (data!"question")!"qname"
    /\ forall (rr : resourceRecord),
        In rr (data!"answers" ++ data!"additional" ++ data!"authority")
        -> resourceRecord_OK rr.

  Ltac decompose_parsed_data :=
    repeat match goal with
           | H : (?x ++ ?y ++ ?z)%list = _ |- _ =>
             eapply firstn_skipn_self in H; try eassumption;
             destruct H as [? [? ?] ]
           | H : WS _ WO = _ |- _ =>
             apply (f_equal (@whd 0)) in H;
             simpl in H; rewrite H in *; clear H
           | H : length _ = _ |- _ => clear H
           end;
    subst.

  Lemma decides_resourceRecord_OK
    : forall l n m o,
      length l = n + m + o
      -> (forall x : resourceRecord, In x l -> resourceRecord_OK x)
      -> decides true
                 (forall rr : resourceRecord,
                     In rr
                        (firstn n l ++
                                firstn m (skipn n l) ++ firstn o (skipn (n + m) l)) ->
                     resourceRecord_OK rr).
  Proof.
    simpl; intros.
    rewrite firstn_skipn_self' in H1; eauto.
  Qed.

  Hint Resolve decides_resourceRecord_OK : decide_data_invariant_db .

  (* Resource Record <character-string>s are a byte, *)
  (* followed by that many characters. *)
  Definition encode_characterString_Spec (s : string) :=
    encode_nat_Spec 8 (String.length s)
                    ThenC encode_string_Spec s
                    DoneC.

  Definition encode_question_Spec (q : question) :=
    encode_DomainName_Spec q!"qname"
                           ThenC encode_enum_Spec QType_Ws q!"qtype"
                           ThenC encode_enum_Spec QClass_Ws q!"qclass"
                           DoneC.


  Definition encode_TXT_Spec (s : string) :=
    encode_unused_word_Spec 16 (* Unusued RDLENGTH Field *)
                            ThenC encode_characterString_Spec s
                            DoneC.

  Definition encode_SOA_RDATA_Spec (soa : SOA_RDATA) :=
    encode_unused_word_Spec 16 (* Unusued RDLENGTH Field *)
                            ThenC encode_DomainName_Spec soa!"sourcehost"
                            ThenC encode_DomainName_Spec soa!"contact_email"
                            ThenC encode_word_Spec soa!"serial"
                            ThenC encode_word_Spec soa!"refresh"
                            ThenC encode_word_Spec soa!"retry"
                            ThenC encode_word_Spec soa!"expire"
                            ThenC encode_word_Spec soa!"minTTL"
                            DoneC.

  Definition encode_WKS_RDATA_Spec (wks : WKS_RDATA) :=
    encode_nat_Spec 16 (length (wks!"Bit-Map"))
                    ThenC encode_word_Spec wks!"Address"
                    ThenC encode_word_Spec wks!"Protocol"
                    ThenC (encode_list_Spec encode_word_Spec wks!"Bit-Map")
                    DoneC.

  Definition encode_HINFO_RDATA_Spec (hinfo : HINFO_RDATA) :=
    encode_unused_word_Spec 16 (* Unusued RDLENGTH Field *)
                            ThenC encode_characterString_Spec hinfo!"CPU"
                            ThenC encode_characterString_Spec hinfo!"OS"
                            DoneC.

  Definition encode_MX_RDATA_Spec (mx : MX_RDATA) :=
    encode_unused_word_Spec 16 (* Unusued RDLENGTH Field *)
                            ThenC encode_word_Spec mx!"Preference"
                            ThenC encode_DomainName_Spec mx!"Exchange"
                            DoneC.

  Definition encode_MINFO_RDATA_Spec (minfo : MINFO_RDATA) :=
    encode_unused_word_Spec 16 (* Unusued RDLENGTH Field *)
                            ThenC encode_DomainName_Spec minfo!"rMailBx"
                            ThenC encode_DomainName_Spec minfo!"eMailBx"
                            DoneC.

  Definition encode_A_Spec (a : Memory.W) :=
    encode_unused_word_Spec 16 (* Unused RDLENGTH Field *)
                            ThenC encode_word_Spec a
                            DoneC.

  Definition encode_NS_Spec (domain : DomainName) :=
    encode_unused_word_Spec 16 (* Unused RDLENGTH Field *)
                            ThenC encode_DomainName_Spec domain
                            DoneC.

  Definition encode_CNAME_Spec (domain : DomainName) :=
    encode_unused_word_Spec 16 (* Unused RDLENGTH Field *)
                            ThenC encode_DomainName_Spec domain
                            DoneC.

  Definition encode_PTR_Spec (domain : DomainName) :=
    encode_unused_word_Spec 16 (* Unused RDLENGTH Field *)
                            ThenC encode_DomainName_Spec domain
                            DoneC.

  Definition encode_rdata_Spec :=
    encode_SumType_Spec ResourceRecordTypeTypes
                        (icons encode_A_Spec (* A; host address 	[RFC1035] *)
                               (icons (encode_NS_Spec) (* NS; authoritative name server 	[RFC1035] *)
                                      (icons (encode_CNAME_Spec)  (* CNAME; canonical name for an alias 	[RFC1035] *)
                                             (icons encode_SOA_RDATA_Spec  (* SOA rks the start of a zone of authority 	[RFC1035] *)
                                                    (icons encode_WKS_RDATA_Spec (* WKS  well known service description 	[RFC1035] *)
                                                           (icons (encode_PTR_Spec) (* PTR domain name pointer 	[RFC1035] *)
                                                                  (icons encode_HINFO_RDATA_Spec (* HINFO host information 	[RFC1035] *)
                                                                         (icons (encode_MINFO_RDATA_Spec) (* MINFO mailbox or mail list information 	[RFC1035] *)
                                                                                (icons encode_MX_RDATA_Spec  (* MX  mail exchange 	[RFC1035] *)
                                                                                       (icons encode_TXT_Spec inil)))))))))). (*TXT text strings 	[RFC1035] *)

  Definition encode_resource_Spec(r : resourceRecord) :=
    encode_DomainName_Spec r!sNAME
                           ThenC encode_enum_Spec RRecordType_Ws r!sTYPE
                           ThenC encode_enum_Spec RRecordClass_Ws r!sCLASS
                           ThenC encode_word_Spec r!sTTL
                           ThenC encode_rdata_Spec r!sRDATA
                           DoneC.

  Definition encode_packet_Spec (p : packet) :=
    encode_word_Spec p!"id"
                     ThenC encode_word_Spec (WS p!"QR" WO)
                     ThenC encode_enum_Spec Opcode_Ws p!"Opcode"
                     ThenC encode_word_Spec (WS p!"AA" WO)
                     ThenC encode_word_Spec (WS p!"TC" WO)
                     ThenC encode_word_Spec (WS p!"RD" WO)
                     ThenC encode_word_Spec (WS p!"RA" WO)
                     ThenC encode_word_Spec (WS false (WS false (WS false WO))) (* 3 bits reserved for future use *)
                     ThenC encode_enum_Spec RCODE_Ws p!"RCODE"
                     ThenC encode_nat_Spec 16 1 (* length of question field *)
                     ThenC encode_nat_Spec 16 (|p!"answers"|)
                     ThenC encode_nat_Spec 16 (|p!"authority"|)
                     ThenC encode_nat_Spec 16 (|p!"additional"|)
                     ThenC encode_question_Spec p!"question"
                     ThenC (encode_list_Spec encode_resource_Spec (p!"answers" ++ p!"additional" ++ p!"authority"))
                     DoneC.

  Ltac decode_DNS_rules g :=
    (* Processes the goal by either: *)
    lazymatch goal with
    | |- appcontext[encode_decode_correct_f _ _ _ _ encode_DomainName_Spec _ _ ] =>
      eapply DomainName_decode_correct
    | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_list_Spec encode_resource_Spec) _ _] =>
      intros; apply FixList_decode_correct with (A_predicate := resourceRecord_OK)
    end.

  Definition packet_decoder
    : CorrectDecoderFor DNS_Packet_OK encode_packet_Spec.
  Proof.
    synthesize_decoder_ext transformer
                           decode_DNS_rules
                           decompose_parsed_data
                           solve_GoodCache_inv.
  Defined.

  Definition packetDecoderImpl := Eval simpl in (projT1 packet_decoder).

End DnsPacket.

Print packetDecoderImpl.
