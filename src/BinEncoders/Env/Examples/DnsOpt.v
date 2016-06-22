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

  Definition transformer : Transformer bin := btransformer.
  Variable transformerUnit : TransformerUnitOpt transformer bool.

  Variable QType_Ws : t (word 16) 66.
  Variable QType_Ws_OK : NoDupVector QType_Ws.
  Variable QClass_Ws : t (word 16) 4.
  Variable QClass_Ws_OK : NoDupVector QClass_Ws.
  Variable RRecordType_Ws : t (word 16) 59.
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
    ThenC encode_string_Spec s.

  Definition encode_question_Spec (q : question) :=
       encode_DomainName_Spec q!"qname"
  ThenC encode_enum_Spec QType_Ws q!"qtype"
  ThenC encode_enum_Spec QClass_Ws q!"qclass"
  DoneC.

  Definition encode_SOA_RDATA_Spec (soa : SOA_RDATA) :=
       encode_DomainName_Spec soa!"sourcehost"
  ThenC encode_DomainName_Spec soa!"contact_email"
  ThenC encode_word_Spec soa!"serial"
  ThenC encode_word_Spec soa!"refresh"
  ThenC encode_word_Spec soa!"retry"
  ThenC encode_word_Spec soa!"expire"
  ThenC encode_word_Spec soa!"minTTL"
  DoneC.

  Definition encode_WKS_RDATA_Spec (wks : WKS_RDATA) :=
       encode_word_Spec wks!"Address"
  ThenC encode_word_Spec wks!"Protocol"
  ThenC (encode_list_Spec encode_word_Spec wks!"Bit-Map")
  DoneC.

  Definition encode_HINFO_RDATA_Spec (hinfo : HINFO_RDATA) :=
       encode_characterString_Spec hinfo!"CPU"
  ThenC encode_characterString_Spec hinfo!"OS" (* Should be character string!*)
  DoneC.

  Definition encode_MX_RDATA_Spec (mx : MX_RDATA) :=
       encode_word_Spec mx!"Preference"
  ThenC encode_DomainName_Spec mx!"Exchange"
  DoneC.

  Definition encode_MINFO_RDATA_Spec (minfo : MINFO_RDATA) :=
       encode_DomainName_Spec minfo!"rMailBx"
  ThenC encode_DomainName_Spec minfo!"eMailBx"
  DoneC.

  Definition encode_rdata_Spec :=
  encode_SumType_Spec ResourceRecordTypeTypes
  (icons encode_word_Spec (* A; host address 	[RFC1035] *)
  (icons (encode_DomainName_Spec) (* NS; authoritative name server 	[RFC1035] *)
  (icons (encode_DomainName_Spec)  (* CNAME; canonical name for an alias 	[RFC1035] *)
  (icons encode_SOA_RDATA_Spec  (* SOA rks the start of a zone of authority 	[RFC1035] *)
  (icons encode_WKS_RDATA_Spec (* WKS  well known service description 	[RFC1035] *)
  (icons (encode_DomainName_Spec) (* PTR domain name pointer 	[RFC1035] *)
  (icons encode_HINFO_RDATA_Spec (* HINFO host information 	[RFC1035] *)
  (icons (encode_MINFO_RDATA_Spec) (* MINFO mailbox or mail list information 	[RFC1035] *)
  (icons encode_MX_RDATA_Spec  (* MX  mail exchange 	[RFC1035] *)
  (icons encode_characterString_Spec inil)))))))))). (*TXT text strings 	[RFC1035] *)

  Definition encode_resource_Spec(r : resourceRecord) :=
       encode_DomainName_Spec r!sNAME
  ThenC encode_enum_Spec RRecordType_Ws r!sTYPE
  ThenC encode_enum_Spec RRecordClass_Ws r!sCLASS
  ThenC encode_word_Spec r!sTTL (* Missing length field*)
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

  Ltac normalize_compose :=
    eapply encode_decode_correct_refineEquiv;
    [ intros ? ?; symmetry;
      repeat first [ etransitivity; [apply refineEquiv_compose_compose | ]
                   | etransitivity; [apply refineEquiv_compose_Done | ]
                   | apply refineEquiv_under_compose ];
      intros; higher_order_reflexivity
        | ].

  Lemma firstn_app {A}
    : forall (l1 l2 : list A),
      firstn (|l1 |) (l1 ++ l2) = l1.
  Proof.
    induction l1; intros; simpl; eauto.
    f_equal; eauto.
  Qed.

  Lemma firstn_self {A}
    : forall (l1 : list A),
      firstn (|l1 |) l1 = l1.
  Proof.
    induction l1; intros; simpl; eauto.
    f_equal; eauto.
  Qed.

  Lemma skipn_app {A}
    : forall (l1 l2 : list A),
      skipn (|l1|) (l1 ++ l2) = l2.
  Proof.
    induction l1; intros; simpl; eauto.
  Qed.

  Lemma firstn_skipn_app {A}
    : forall (l1 l2 l3 : list A),
      firstn (|l3|) (skipn (|l1| + |l2|) (l1 ++ l2 ++ l3)) = l3.
  Proof.
    simpl; intros.
    rewrite <- app_length, List.app_assoc, skipn_app.
    apply firstn_self.
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

  Ltac apply_compose :=
    intros;
    match goal with
      H : cache_inv_Property ?P ?P_inv |- _ =>
      first [eapply (compose_encode_correct_no_dep H); clear H
            | eapply (compose_encode_correct H); clear H
            ]
    end.

  (*Theorem characterString_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall (b : nat) cd, P cd -> P (addD cd b)))
    : encode_decode_correct_f cache transformer (fun ls => lt (String.length ls) (pow2 8))
                              encode_characterString_Spec
                              (fun (bin' : _) (env : CacheDecode) =>
                                 `(proj, rest, env') <- decode_nat 8 bin' env;
                                   decode_string proj rest env')
                              P.
  Proof.
    intros; normalize_compose.
    eapply compose_encode_correct.
    2: apply Nat_decode_correct.
    2: eauto.
    Focus 2.
    unfold encode_decode_correct_f; intuition eauto.
    eapply String_decode_correct; eauto.
    eapply String_decode_correct in H3; intuition eauto.
    eapply String_decode_correct in H3; intuition eauto.
    destruct_ex; intuition; eexists _; eexists _; subst;
      intuition eauto.
    unfold cache_inv_Property in *; eauto.
  Qed.
*)
  Ltac makeEvar T k :=
    let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

  Ltac shelve_inv :=
    let H' := fresh in
    let data := fresh in
    intros data H';
    repeat destruct H';
    match goal with
    | H : ?P data |- ?P_inv' =>
      is_evar P;
      let P_inv' := (eval pattern data in P_inv') in
      let P_inv := match P_inv' with ?P_inv data => P_inv end in
      let new_P_T := type of P in
      makeEvar new_P_T
               ltac:(fun new_P =>
                       unify P (fun data => new_P data /\ P_inv data)); apply (Logic.proj2 H)
    end.

  Ltac solve_data_inv :=
    first [ intros; exact I
          | shelve_inv ].

  Ltac build_decoder :=
    first [ solve [eapply Enum_decode_correct; eauto ]
          | solve [eapply Word_decode_correct ]

          | solve [eapply Nat_decode_correct ]
          | solve [eapply String_decode_correct ]
          | solve [intros; eapply DomainName_decode_correct ]
          | intros;
            match goal with
              |- encode_decode_correct_f
                   _ _ _
                   (encode_list_Spec _) _ _ =>
              eapply FixList_decode_correct end
          | apply_compose ].

  Require Import Fiat.Common.IterateBoundedIndex.

  Opaque pow2. (* Don't want to be evaluating this. *)

  Definition packet_decoder
    : { decodePlusCacheInv |
        exists P_inv pred,
        (cache_inv_Property (snd decodePlusCacheInv) P_inv
        -> encode_decode_correct_f cache _ pred encode_packet_Spec (fst decodePlusCacheInv) (snd decodePlusCacheInv))
        /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
  Proof.
    eexists (_, _); eexists _; eexists _; split; simpl.
    intros; normalize_compose.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    cbv beta; transitivity (wordToNat (natToWord 16 2));
      [simpl; omega | eapply wordToNat_bound].
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    build_decoder.
    solve_data_inv.
    build_decoder.
    eapply SumType_decode_correct.
    instantiate (2 := (icons _
           (icons _
              (icons _
                 (icons _
                    (icons _
                       (icons _
                          (icons _
                             (icons _
                                    (icons _ (icons _ inil))))))))))).
    instantiate (13 := @Iterate_Dep_Type_equiv' 10 _
                                               (icons _
           (icons _
              (icons _
                 (icons _
                    (icons _
                       (icons _
                          (icons _
                             (icons _
                                    (icons _ (icons _ inil))))))))))

                ).
    instantiate (12 := @Iterate_Dep_Type_equiv' 10 _
                                               (icons _
           (icons _
              (icons _
                 (icons _
                    (icons _
                       (icons _
                          (icons _
                             (icons _
                                    (icons _ (icons _ inil))))))))))

                ).
    intro; pattern idx.
    eapply Iterate_Ensemble_equiv' with (idx := idx); simpl.
    apply Build_prim_and.
    build_decoder.
    apply Build_prim_and.
    build_decoder.
    apply Build_prim_and.
    build_decoder.
    apply Build_prim_and.
    {
      build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      solve_data_inv.
      unfold encode_decode_correct_f; intuition eauto.
      destruct data as [? [? [? [? [? [? [? [ ] ] ] ] ] ] ] ].
      unfold GetAttribute, GetAttributeRaw in *.
      subst; simpl.
      computes_to_inv; injections.
      eexists; intuition eauto; simpl.
      match goal with
        |- ?f ?a ?b ?c = ?P =>
        let P' := (eval pattern a, b, c in P) in
        let f' := match P' with ?f a b c => f end in
      unify f f'; reflexivity
      end.
      injections; eauto.
      eexists _; eexists _.
    intuition eauto.
    injections; eauto.
    injections.
    solve_predicate.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    injections; eauto.
    }
    apply Build_prim_and.
    {
      build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      revert H21; build_decoder.
      shelve_inv.
      unfold encode_decode_correct_f; intuition eauto.
      destruct data as [? [? [? [ ] ] ] ].
      unfold GetAttribute, GetAttributeRaw in *.
      subst; simpl.
      computes_to_inv; injections.
      eexists; intuition eauto; simpl.
      match goal with
        |- ?f ?a ?b ?c = ?P =>
        let P' := (eval pattern a, b, c in P) in
        let f' := match P' with ?f a b c => f end in
        unify f f'; reflexivity
      end.
      simpl in H25; injections; eauto.
      eexists _; eexists _.
      intuition eauto.
      injections; eauto.
      injections.
      solve_predicate.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
    }
    apply Build_prim_and.
    build_decoder.
    apply Build_prim_and.
    {
      build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      solve_data_inv.
      unfold encode_decode_correct_f; intuition eauto.
      destruct data as [? [? [ ] ] ].
      unfold GetAttribute, GetAttributeRaw in *.
      subst; simpl.
      computes_to_inv; injections.
      eexists; intuition eauto; simpl.
      match goal with
        |- ?f ?a ?b ?c = ?P =>
        let P' := (eval pattern a, b, c in P) in
        let f' := match P' with ?f a b c => f end in
        unify f f'; reflexivity
      end.
      injections; eauto.
      eexists _; eexists _.
      intuition eauto.
      injections; eauto.
      injections; solve_predicate.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; solve_predicate.
    }
    apply Build_prim_and.
    { build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      solve_data_inv.
      unfold encode_decode_correct_f; intuition eauto.
      destruct data as [? [? [ ] ] ].
      unfold GetAttribute, GetAttributeRaw in *.
      subst; simpl.
      computes_to_inv; injections.
      eexists; intuition eauto; simpl.
      match goal with
        |- ?f ?a ?b ?c = ?P =>
        let P' := (eval pattern a, b, c in P) in
        let f' := match P' with ?f a b c => f end in
        unify f f'; reflexivity
      end.
      injections; eauto.
      eexists _; eexists _.
      intuition eauto.
      injections; eauto.
      injections; solve_predicate.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; solve_predicate.
      injections; solve_predicate.
      injections; solve_predicate.
    }
    apply Build_prim_and.
    { build_decoder.
      build_decoder.
      solve_data_inv.
      build_decoder.
      build_decoder.
      solve_data_inv.
      unfold encode_decode_correct_f; intuition eauto.
      destruct data as [? [? [ ] ] ].
      unfold GetAttribute, GetAttributeRaw in *.
      subst; simpl.
      computes_to_inv; injections.
      eexists; intuition eauto; simpl.
      match goal with
        |- ?f ?a ?b ?c = ?P =>
        let P' := (eval pattern a, b, c in P) in
        let f' := match P' with ?f a b c => f end in
        unify f f'; reflexivity
      end.
      injections; eauto.
      eexists _; eexists _.
      intuition eauto.
      injections; eauto.
      injections; solve_predicate.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; solve_predicate.
    }
    apply Build_prim_and.
    build_decoder.
    eauto.
    shelve_inv.
    { unfold encode_decode_correct_f; intuition eauto.
      destruct data as [? [? [? [? [? [ ] ] ] ] ] ].
      unfold GetAttribute, GetAttributeRaw in *.
      simpl in *; subst.
      computes_to_inv; injections.
      eexists; intuition eauto; simpl.
      match goal with
      |- ?f ?a ?b ?c = ?P =>
      let P' := (eval pattern a, b, c in P) in
      let f' := match P' with ?f a b c => f end in
      unify f f'; reflexivity
      end.
      injections; eauto.
      eexists _; eexists _.
      intuition eauto.
      injections; eauto.
      solve_predicate.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
      injections; eauto.
    }
    simpl; intros; intuition eauto.
    rewrite !app_length, H20, H21, H22.
    reflexivity.
    generalize data H15 x H34.
    shelve_inv.
    generalize data H15 x H34.
    shelve_inv.
    generalize data H15 x H34.
    shelve_inv.
    generalize data H15 x H34.
    shelve_inv.
    simpl; intros; intuition eauto.
    unfold encode_decode_correct_f; intuition eauto.
    repeat destruct data.
    repeat destruct prim_snd.
    unfold GetAttribute, GetAttributeRaw in *.
    computes_to_inv.
    repeat match goal with
             H : context [ilist2.ith2]
             |- _ => simpl in H
           end.
    repeat match goal with
             H : ?Z
             |- _ => match Z with context [ilist2.ith2 _ _] => simpl in H
                     end
           end.
    simpl.
    destruct prim_fst7.
    destruct prim_snd.
    simpl in H21; simpl in H22; simpl in H23.
    destruct prim_snd.
    simpl in H21.
    destruct prim_snd.
    simpl.
    eexists; repeat split.
    repeat match goal with
             H : WS _ WO = _ |- _ =>
             let H' := fresh in
             pose proof (f_equal (@whd _) H) as H'; simpl in H';
               rewrite H'; clear H' H
           end.
    simpl in *.
    revert H29 H27 H28; subst.
    injection H21; intros ? ?; subst.
    instantiate (2 := fun al ext env' =>
                         Some
                           ({|
      ilist.prim_fst := _;
      ilist.prim_snd := {|
                         ilist.prim_fst := _;
                        ilist.prim_snd := {|
                                          ilist.prim_fst := _;
                                          ilist.prim_snd := {|
                                                  ilist.prim_fst := _;
                                                  ilist.prim_snd := {|
                                                  ilist.prim_fst := _;
                                                  ilist.prim_snd := {|
                                                  ilist.prim_fst := _;
                                                  ilist.prim_snd := {|
                                                  ilist.prim_fst := _;
                                                  ilist.prim_snd := {|
                                                  ilist.prim_fst := _;
                                                  ilist.prim_snd := {|
                                                  ilist.prim_fst := {|
                                                  ilist.prim_fst := _;
                                                  ilist.prim_snd := {|
                                                  ilist.prim_fst := _;
                                                  ilist.prim_snd := {|
                                                  ilist.prim_fst := _;
                                                  ilist.prim_snd := () |} |} |};
                                                  ilist.prim_snd := {|
                                                  ilist.prim_fst := firstn proj7 al;
                                                  ilist.prim_snd := {|
                                                  ilist.prim_fst := firstn proj8 (skipn (proj7 + proj9) al);
                                                  ilist.prim_snd := {|
                                                  ilist.prim_fst := firstn proj9 (skipn proj7 al); ilist.prim_snd := () |}
                                                   |} |} |} |} |} |} |} |} |} |} |},
     ext, env')).
    simpl; intros; repeat progress f_equal.
    eauto.
    eauto.
    eauto.
    subst; apply firstn_app.
    subst; apply firstn_skipn_app.
    subst; rewrite skipn_app.
    apply firstn_app.
    injections; eauto.
    injections; eauto.
    eexists _; eexists _; split; split; eauto.
    injections; simpl; eauto.
    split.
    simpl in H21.
    injection H21; intros; subst.
    unfold GetAttribute, GetAttributeRaw; simpl.
    intuition eauto.
    solve_predicate.
    injections; eauto.
    eapply H18.
    rewrite firstn_skipn_self' in H34.
    eauto.
    eauto.
    rewrite H17; clear; omega.
    eapply H18.
    rewrite firstn_skipn_self' in H34.
    eauto.
    rewrite H17; clear; omega.
    eapply H18.
    rewrite firstn_skipn_self' in H34.
    eauto.
    rewrite H17; clear; omega.
    eapply H18.
    rewrite firstn_skipn_self' in H34.
    eauto.
    rewrite H17; clear; omega.
    revert H17 H11; clear.
    rewrite Plus.plus_assoc; intros.
    erewrite length_firstn_skipn_app by eauto.
    apply H11.
    revert H17 H10; clear.
    rewrite Plus.plus_assoc; intros.
    erewrite length_firstn_skipn_app' by eauto.
    apply H10.
    revert H17 H9; clear.
    rewrite Plus.plus_assoc; intros.
    erewrite length_firstn_skipn_app'' by eauto.
    apply H9.
    apply whd_word_1_refl.
    apply whd_word_1_refl.
    apply whd_word_1_refl.
    apply whd_word_1_refl.
    apply whd_word_1_refl.
    revert H17; clear.
    rewrite Plus.plus_assoc; intros.
    eapply length_firstn_skipn_app''; eauto.
    revert H17; clear.
    rewrite Plus.plus_assoc; intros.
    eapply length_firstn_skipn_app'; eauto.
    revert H17; clear.
    rewrite Plus.plus_assoc; intros.
    eapply length_firstn_skipn_app; eauto.
    eapply firstn_skipn_self'.
    rewrite H17; omega.
    simpl in H21.
    injection H21; intros; subst.
    eauto.
    repeat instantiate (1 := fun _ => True); admit.
    Grab Existential Variables.
    exact 0. (* Length of the Bit-Map in WKS RDATA. *)
    apply (@Fin.F1 _). (* RDATA Type. *)
    apply Peano_dec.eq_nat_dec.
    intros; destruct (weqb a a') eqn:Heq; [left | right].
    apply weqb_sound; eauto.
    intro; apply weqb_true_iff in H; congruence.
  Defined.

  Definition packetDecoderImpl := Eval simpl in (projT1 packet_decoder).

  Print packetDecoderImpl.

End DnsPacket.
