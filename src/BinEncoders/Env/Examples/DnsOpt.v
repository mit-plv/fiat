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
        Fiat.BinEncoders.Env.Lib2.DomainNameOpt.

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

  Variable QType_Ws : t (word 16) 17.
  Variable QType_Ws_OK : NoDupVector QType_Ws.
  Variable QClass_Ws : t (word 16) 4.
  Variable QClass_Ws_OK : NoDupVector QClass_Ws.
  Variable RRecordType_Ws : t (word 16) 10.
  Variable RRecordType_Ws_OK : NoDupVector  RRecordType_Ws.
  Variable RRecordClass_Ws : t (word 16) 3.
  Variable RRecordClass_Ws_OK : NoDupVector  RRecordClass_Ws.
  Variable Opcode_Ws : t (word 4) 4.
  Variable Opcode_Ws_OK : NoDupVector  Opcode_Ws.
  Variable RCODE_Ws : t (word 4) 12.
  Variable RCODE_Ws_OK : NoDupVector  RCODE_Ws.

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

    Definition transformer : Transformer ByteString := ByteStringQueueTransformer.

  Lemma firstn_app {A}
    : forall (l1 l2 : list A),
      firstn (|l1 |) (l1 ++ l2) = l1.
  Proof.
    induction l1; intros; simpl; eauto.
    f_equal; eauto.
  Qed.

  Lemma decides_firstn_app {A}
    : forall (l1 l2 : list A),
      decides true (firstn (|l1 |) (l1 ++ l2) = l1).
  Proof.
    apply firstn_app.
  Qed.

  Lemma firstn_self {A}
    : forall (l1 : list A),
      firstn (|l1 |) l1 = l1.
  Proof.
    induction l1; intros; simpl; eauto.
    f_equal; eauto.
  Qed.

  Lemma decides_firstn_self {A}
    : forall (l1 : list A),
      decides true (firstn (|l1 |) l1 = l1).
  Proof.
    intros; apply firstn_self.
  Qed.

  Lemma skipn_app {A}
    : forall (l1 l2 : list A),
      skipn (|l1|) (l1 ++ l2) = l2.
  Proof.
    induction l1; intros; simpl; eauto.
  Qed.

  Lemma decides_skipn_app {A}
    : forall (l1 l2 : list A),
      decides true (skipn (|l1|) (l1 ++ l2) = l2).
  Proof.
    apply skipn_app.
  Qed.

  Lemma firstn_skipn_app {A}
    : forall (l1 l2 l3 : list A),
      firstn (|l3|) (skipn (|l1| + |l2|) (l1 ++ l2 ++ l3)) = l3.
  Proof.
    simpl; intros.
    rewrite <- app_length, List.app_assoc, skipn_app.
    apply firstn_self.
  Qed.

  Lemma decides_firstn_skipn_app {A}
    : forall (l1 l2 l3 : list A),
      decides true (firstn (|l3|) (skipn (|l1| + |l2|) (l1 ++ l2 ++ l3)) = l3).
  Proof.
    intros; apply firstn_skipn_app.
  Qed.

  Lemma firstn_skipn_self' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + m + o
      -> (firstn n l ++ firstn m (skipn n l) ++ firstn o (skipn (n + m) l))%list =
      l.
  Proof.
    induction n; simpl.
    induction m; simpl; eauto.
    induction o; simpl.
    destruct l; simpl; eauto.
    intros; discriminate.
    destruct l; simpl; eauto.
    intros; f_equal; eauto.
    destruct l; simpl.
    intros; discriminate.
    intros; f_equal; eauto.
    destruct l; simpl.
    intros; discriminate.
    intros; f_equal; eauto.
  Qed.

  Lemma firstn_skipn_self'' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + (m + o)
      ->
      decides true ((firstn n l ++ firstn m (skipn n l) ++ firstn o (skipn (n + m) l))%list =
                    l).
  Proof.
    intros; eapply firstn_skipn_self'.
    omega.
  Qed.

  Lemma word_eq_self 
    : forall (w : word 1),
      decides true (WS (whd w) WO = w).
  Proof.
    simpl; intros; shatter_word w; reflexivity.
  Qed.

  Lemma firstn_skipn_self {A}
      : forall (n m o : nat) (l l1 l2 l3 : list A),
      (l1 ++ l2 ++ l3)%list = l ->
      (|l1|) = n ->
      (|l2|) = m ->
      (|l3|) = o ->
      l1 = firstn n l
      /\ l2 = firstn m (skipn n l)
      /\ l3 = firstn o (skipn (n + m) l).
  Proof.
    intros; subst; intuition;
    eauto using firstn_skipn_app, skipn_app, firstn_app.
    rewrite skipn_app; symmetry; apply firstn_app.
  Qed.

  Lemma length_firstn_skipn_app {A}
    : forall (n m o : nat) (l : list A),
      length l = n + m + o
      -> (|firstn m (skipn n l) |) = m.
  Proof.
    induction n; simpl.
    induction m; simpl; eauto.
    induction o; simpl.
    destruct l; simpl; eauto.
    intros; discriminate.
    destruct l; simpl; eauto.
    intros; discriminate.
    intros; f_equal; eauto.
    destruct l; simpl.
    intros; discriminate.
    intros; f_equal; eauto.
  Qed.

  Lemma length_firstn_skipn_app' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + m + o
      -> (|firstn o (skipn (n + m) l) |) = o.
  Proof.
    induction n; simpl.
    induction m; simpl; eauto.
    induction o; simpl.
    destruct l; simpl; eauto.
    destruct l; simpl; eauto.
    destruct l; simpl; eauto.
    intros; discriminate.
    intros; f_equal; eauto.
    destruct l; simpl.
    intros; discriminate.
    intros; f_equal; eauto.
  Qed.

  Lemma length_firstn_skipn_app'' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + m + o
      -> (|firstn n l |) = n.
  Proof.
    induction n; destruct l; simpl; intros;
      try discriminate; eauto.
  Qed.

  Lemma whd_word_1_refl :
    forall (b : word 1),
      WS (whd b) WO = b.
  Proof.
    intros; destruct (shatter_word_S b) as [? [? ?] ]; subst.
    rewrite (shatter_word_0 x0); reflexivity.
  Qed.

  Lemma decides_True' {A}
    : forall a, decides true ((fun _ : A => True) a).
  Proof.
    simpl; intros; exact I.
  Qed.

  Require Import Fiat.Common.IterateBoundedIndex
          Fiat.Common.Tactics.CacheStringConstant.

  Lemma lt_1_pow2_16
    : lt 1 (pow2 16).
  Proof.
    intros.
    rewrite <- (wordToNat_natToWord_idempotent 16 1).
    eapply wordToNat_bound.
    simpl; eapply BinNat.N.ltb_lt; reflexivity.
Qed.

  Hint Resolve lt_1_pow2_16 : data_inv_hints.
  Hint Resolve FixedList_predicate_rest_True : data_inv_hints.

  Opaque pow2. (* Don't want to be evaluating this. *)

Ltac decide_data_invariant :=
  (* Show that the invariant on the data is decideable. Most *)
  (* of the clauses in this predicate are obviously true by *)
  (* construction, but there may be some that need to be checked *)
  (* by a decision procedure*)
  unfold GetAttribute, GetAttributeRaw in *;
  simpl in *; intros; intuition;
    repeat first [ progress subst
             | match goal with
                 |- decides ?A (?B ?C)  =>
                 let T := type of C in
                 unify B (fun _ : T => True);
                 apply (@decides_True' T C)
               end
          | apply decides_eq_refl
          | solve [eauto with decide_data_invariant_db]
          | eapply decides_and
          | eapply decides_assumption; eassumption
          | eapply decides_dec_eq; auto using Peano_dec.eq_nat_dec, weq ].

Ltac decode_step :=
  (* Processes the goal by either: *)
  match goal with
  (* A) decomposing one of the parser combinators, *)
  | |- _ => apply_compose
  (* B) applying one of the rules for a base type  *)
  | H : cache_inv_Property _ _
    |- appcontext [encode_decode_correct_f _ _ _ _ encode_word_Spec _ _] =>
    intros; revert H; eapply Word_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_unused_word_Spec' _ _) _ _] =>
    apply unused_word_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ encode_word_Spec _ _] =>
    eapply Word_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_nat_Spec _) _ _] =>
    eapply Nat_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_list_Spec _) _ _] => intros; apply FixList_decode_correct

  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_enum_Spec _) _ _] =>
    eapply Enum_decode_correct
  | |- appcontext[encode_decode_correct_f _ _ _ _ encode_DomainName_Spec _ _ ] =>
    eapply DomainName_decode_correct
  (* C) Discharging a side condition of one of the base rules *)
  | |- NoDupVector _ => Discharge_NoDupVector
  | _ => solve [solve_data_inv]
  (* D) Solving the goal once all the byte string has been parsed *)
  | _ =>  solve [simpl; intros;
                 eapply encode_decode_correct_finish;
                 [ build_fully_determined_type
                 | decide_data_invariant ] ]
  end.

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

Lemma firstn_lt_decides {A}:
  forall m n (l : list A),
    (lt m n)%nat
    -> decides true (lt (|firstn m l |) n)%nat.
Proof.
  simpl; intros; rewrite firstn_length.
  eapply NPeano.Nat.min_lt_iff; eauto.
Qed.

  Lemma whd_word_1_refl' :
    forall (b : word 1),
      decides true (WS (whd b) WO = b).
  Proof.
    intros; destruct (shatter_word_S b) as [? [? ?] ]; subst.
    rewrite (shatter_word_0 x0); reflexivity.
  Qed.

  Lemma decides_length_firstn_skipn_app {A}
    : forall (n m o : nat) (l : list A),
      length l = n + (m + o)
      -> decides true ((|firstn m (skipn n l) |) = m).
  Proof.
    setoid_rewrite plus_assoc'.
    eapply length_firstn_skipn_app.
  Qed.

  Lemma decides_length_firstn_skipn_app' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + (m + o)
      -> decides true ((|firstn o (skipn (n + m) l) |) = o).
  Proof.
    setoid_rewrite plus_assoc'. 
    apply length_firstn_skipn_app'.
  Qed.

  Lemma decides_length_firstn_skipn_app'' {A}
    : forall (n m o : nat) (l : list A),
      length l = n + (m + o)
      -> decides true ((|firstn n l |) = n).
  Proof.
    setoid_rewrite plus_assoc'. 
    apply length_firstn_skipn_app''.
  Qed.
  
  Hint Resolve whd_word_1_refl' : decide_data_invariant_db.
  Hint Resolve decides_length_firstn_skipn_app'' : decide_data_invariant_db.
  Hint Resolve decides_length_firstn_skipn_app' : decide_data_invariant_db.
  Hint Resolve decides_length_firstn_skipn_app : decide_data_invariant_db.
  Hint Resolve validDomainName_proj1_OK : decide_data_invariant_db.
  Hint Resolve validDomainName_proj2_OK : decide_data_invariant_db.
  Hint Resolve firstn_lt_decides : decide_data_invariant_db.
  Hint Resolve firstn_skipn_self'' : decide_data_invariant_db.
  Hint Resolve decides_firstn_app : decide_data_invariant_db.
  Hint Resolve decides_firstn_self : decide_data_invariant_db.
  Hint Resolve decides_skipn_app : decide_data_invariant_db.
  Hint Resolve decides_firstn_skipn_app : decide_data_invariant_db.
  
  Instance : DecideableEnsembles.Query_eq () :=
  {| A_eq_dec a a' := match a, a' with (), () => left (eq_refl _) end |}.

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

Definition DNS_Packet_OK (data : packet) :=
  lt (|data!"answers" |) (pow2 16)
  /\ lt (|data!"authority" |) (pow2 16)
  /\ lt (|data!"additional" |) (pow2 16)
  /\ ValidDomainName (data!"question")!"qname"
  /\ forall (rr : resourceRecord),
      In rr (data!"answers" ++ data!"additional" ++ data!"authority")
      -> resourceRecord_OK rr.


Definition packet_decoder
    : { decodePlusCacheInv |
        exists P_inv,
        (cache_inv_Property (snd decodePlusCacheInv) P_inv
        -> encode_decode_correct_f _ transformer DNS_Packet_OK (fun _ _ => True) encode_packet_Spec (fst decodePlusCacheInv) (snd decodePlusCacheInv))
        /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
  Proof.
    start_synthesizing_decoder.
    normalize_compose transformer.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    intros; instantiate (1 := fun _ _ => True).
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    eapply SumType_decode_correct with
    (idx := proj12)
    (encoders := (icons _
           (icons _
              (icons _
                 (icons _
                    (icons _
                       (icons _
                          (icons _
                             (icons _
                                    (icons _ (icons _ inil)))))))))))
      (decoders := (icons _
           (icons _
              (icons _
                 (icons _
                    (icons _
                       (icons _
                          (icons _
                             (icons _
                                    (icons _ (icons _ inil)))))))))))
      (invariants := icons _
           (icons _
              (icons _
                 (icons _
                    (icons _
                       (icons _
                          (icons _
                             (icons _
                                    (icons _ (icons _ inil))))))))))
      (invariants_rest := icons _
           (icons _
              (icons _
                 (icons _
                    (icons _
                       (icons _
                          (icons _
                             (icons _
                                    (icons _ (icons _ inil))))))))))
      (cache_invariants := Vector.cons _ _ _
           (Vector.cons _ _ _
              (Vector.cons _ _ _
                 (Vector.cons _ _ _
                    (Vector.cons _ _ _
                       (Vector.cons _ _ _
                          (Vector.cons _ _ _
                             (Vector.cons _ _ _
                                    (Vector.cons _ _ _ (Vector.cons _ _ _ (Vector.nil _))))))))))).
    intro; pattern idx.
    eapply Iterate_Ensemble_equiv' with (idx := idx); simpl.
    apply Build_prim_and.
    unfold encode_A_Spec, encode_unused_word_Spec.
    repeat decode_step.
    apply Build_prim_and.
    unfold encode_NS_Spec, encode_unused_word_Spec.
    repeat decode_step.
    apply Build_prim_and.
    unfold encode_CNAME_Spec, encode_unused_word_Spec.
    repeat decode_step.
    apply Build_prim_and.
    unfold encode_SOA_RDATA_Spec, encode_unused_word_Spec.
    repeat decode_step.
    apply Build_prim_and.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    repeat decode_step.
    repeat decode_step.
    repeat decode_step.
    repeat decode_step.
    apply Build_prim_and.
    unfold encode_PTR_Spec, encode_unused_word_Spec.
    repeat decode_step.
    apply Build_prim_and.
    unfold encode_HINFO_RDATA_Spec, encode_unused_word_Spec.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    eapply String_decode_correct.
    decode_step.
    decode_step.
    intros; eapply encode_decode_correct_finish.
    build_fully_determined_type.
    decide_data_invariant.
    decode_step.
    intros; instantiate (1 := fun _ _ => True).
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    eapply String_decode_correct.
    decode_step.
    decode_step.
    intros; eapply encode_decode_correct_finish.
    build_fully_determined_type.
    decide_data_invariant.
    decode_step.
    intros; instantiate (1 := fun _ _ => True).
    decode_step.
    decode_step.
    apply Build_prim_and.
    unfold encode_MINFO_RDATA_Spec, encode_unused_word_Spec.
    repeat decode_step.
    apply Build_prim_and.
    unfold encode_MX_RDATA_Spec, encode_unused_word_Spec.
    repeat decode_step.
    apply Build_prim_and.
    unfold encode_TXT_Spec, encode_unused_word_Spec.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    eapply String_decode_correct.
    decode_step.
    decode_step.
    decode_step.
    decode_step.
    (* Need an invariant on the resource records in response. *)
    intros; clear.
    simpl.
    repeat instantiate (1 := fun _ _ => True).
    simpl; eauto.
    decode_step.
    decode_step.
    intros.
    destruct H17 as [ [ [ [ [? ?] ? ] ? ] ? ] ?].
    subst proj12.
    pattern data.
    apply H17.

    repeat instantiate (1 := fun _ _ => True).
    intros.
    let a'' := fresh in
    rename a' into a'';
      repeat destruct a'' as [ ? | a''] ; auto.
    decode_step.
    split; intros.
    intuition.
    rewrite !app_length.
    rewrite H16, H17, H18.
    reflexivity.
    intuition; intros.
    apply H31; eauto.
    apply H31; eauto.
    apply H31; eauto.
    decode_step.
    simpl; intros;
      eapply encode_decode_correct_finish.
    let a' := fresh in
  intros a'; repeat destruct a' as [? a'];
  (* Show that it is determined by the constraints (equalities) *)
  (* inferred during parsing. *)
  unfold GetAttribute, GetAttributeRaw in *;
  simpl in *; intros;
  (* Decompose data predicate *) intuition.
    eapply firstn_skipn_self in H19; try eassumption.
    intuition.
    clear H21 H22 H23.
  (* Substitute any inferred equalities *)
    repeat match goal with
             H : WS _ WO = _ |- _ =>
             apply (f_equal (@whd 0)) in H;
               simpl in H; rewrite H in *; clear H
           end.
    let a' := fresh in
    rename prim_fst7 into a'; repeat destruct a' as [? a'];
      simpl in *.
    subst.
    (* And unify with original object *) reflexivity.
    decide_data_invariant.
    instantiate (1 := true).
    simpl; intros.
    rewrite firstn_skipn_self' in H13.
    apply H17 in H13.
    unfold resourceRecord_OK; simpl.
    intuition eauto.
    omega.

    instantiate (17 := GoodCache).
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ].
    instantiate (1 := fun _ => True); exact I.
    intro; pattern idx.
    eapply Iterate_Ensemble_equiv' with (idx := idx); simpl.
    apply Build_prim_and.
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ].
    instantiate (1 := fun _ => True); exact I.
    apply Build_prim_and.
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ];
      try solve [instantiate (1 := fun _ => True); exact I].
    apply Build_prim_and.
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ].
    instantiate (1 := fun _ => True); exact I.
    apply Build_prim_and.
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ];
      try solve [instantiate (1 := fun _ => True); exact I].
    apply Build_prim_and.
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ].
    instantiate (1 := fun _ => True); exact I.
    apply Build_prim_and.
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ];
      try solve [instantiate (1 := fun _ => True); exact I].
    apply Build_prim_and.
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ];
      try solve [instantiate (1 := fun _ => True); exact I].
    apply Build_prim_and.
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ];
      try solve [instantiate (1 := fun _ => True); exact I].
    apply Build_prim_and.
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ];
      try solve [instantiate (1 := fun _ => True); exact I].
    apply Build_prim_and.
    unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10;
      try solve [ eapply cacheIndependent_add_3 in H1; intuition eauto ];
      try solve [ eapply cacheIndependent_add_9 in H2; intuition eauto ];
      try solve [ eapply cacheIndependent_add_5 in H1; intuition eauto ];
      try solve [instantiate (1 := fun _ => True); exact I].
    exact I.
    try solve [instantiate (1 := fun _ => True); exact I].
    try solve [instantiate (1 := fun _ => True); exact I].
  Defined.

  Print Assumptions packet_decoder.
  
  Definition packetDecoderImpl := Eval simpl in (projT1 packet_decoder).

  Print packetDecoderImpl.

End DnsPacket.
