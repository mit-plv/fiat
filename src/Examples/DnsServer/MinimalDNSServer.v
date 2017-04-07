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
    {| CacheEncode := option {n | lt (NPeano.div n 8) (pow2 14)} * association_list string pointerT;
       CacheDecode := option {n | lt (NPeano.div n 8) (pow2 14)} * association_list pointerT string;
       Equiv ce cd := fst ce = fst cd
                      /\ (snd ce) = (map (fun ps => match ps with (p, s) => (s, p) end) (snd cd))
                      /\ NoDup (map fst (snd cd))
    |}%type.

  Definition list_CacheEncode_empty : CacheEncode := (Some 0, nil).
  Definition list_CacheDecode_empty : CacheDecode := (Some 0, nil).

  Lemma list_cache_empty_Equiv : Equiv list_CacheEncode_empty list_CacheDecode_empty.
  Proof.
    simpl; intuition; simpl; econstructor.
  Qed.

  Local Opaque pow2.

  Instance cacheAddNat : CacheAdd _ nat :=
    {| addE ce n := (Ifopt (fst ce) as m Then
                                         let n' := m + n in
                     if Compare_dec.lt_dec (NPeano.div n' 8) (pow2 14)
                     then Some n'
                     else None
                            Else None, snd ce);
       addD cd n := (Ifopt (fst cd) as m Then
                                         let n' := m + n in
                     if Compare_dec.lt_dec (NPeano.div n' 8) (pow2 14)
                     then Some n'
                     else None
                            Else None, snd cd) |}.
  Proof.
    simpl; intuition eauto; destruct a; destruct a0;
      simpl in *; eauto; try congruence.
    injections.
    find_if_inside; eauto.
  Defined.

  Instance : Query_eq pointerT :=
    {| A_eq_dec := pointerT_eq_dec |}.

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

  Instance cachePeekDNPointer : CachePeek _ (option pointerT) :=
    {| peekE ce := Ifopt (fst ce) as m Then Some (Nat2pointerT (NPeano.div m 8)) Else None;
       peekD cd := Ifopt (fst cd) as m Then Some (Nat2pointerT (NPeano.div m 8)) Else None |}.
  Proof.
    abstract (simpl; intros; intuition; rewrite H0; auto).
  Defined.

  Lemma cacheGetDNPointer_pf
    : forall (ce : CacheEncode) (cd : CacheDecode)
             (p : string) (q : pointerT),
      Equiv ce cd ->
      (association_list_find_first (snd cd) q = Some p <-> List.In q (association_list_find_all (snd ce) p)).
  Proof.
    intros [? ?] [? ?] ? ?; simpl; intuition eauto; subst.
    - subst; induction a0; simpl in *; try congruence.
      destruct a; simpl in *; find_if_inside; subst.
      + inversion H2; subst; intros.
        find_if_inside; subst; simpl; eauto.
      + inversion H2; subst; intros.
        find_if_inside; subst; simpl; eauto; congruence.
    - subst; induction a0; simpl in *; intuition.
      destruct a; simpl in *; find_if_inside.
      + inversion H2; subst; intros.
        find_if_inside; subst; simpl; eauto; try congruence.
        apply IHa0 in H1; eauto.
        elimtype False; apply H3; revert H1; clear.
        induction a0; simpl; intros; try congruence.
        destruct a; find_if_inside; injections; auto.
      + inversion H2; subst; intros.
        find_if_inside; subst; simpl; eauto; try congruence.
        simpl in H1; intuition eauto; subst.
        congruence.
  Qed.

  Instance cacheGetDNPointer : CacheGet _ string pointerT :=
    {| getE ce p := association_list_find_all (snd ce) p;
       getD ce p := association_list_find_first (snd ce) p;
       get_correct := cacheGetDNPointer_pf |}.

  Lemma cacheAddDNPointer_pf
    : forall (ce : CacheEncode) (cd : CacheDecode) (t : string * pointerT),
   Equiv ce cd ->
   add_ptr_OK t ce cd ->
   Equiv (fst ce, association_list_add (snd ce) (fst t) (snd t))
     (fst cd, association_list_add (snd cd) (snd t) (fst t)).
  Proof.
    simpl; intuition eauto; simpl in *; subst; eauto.
    unfold add_ptr_OK in *.
    destruct t; simpl in *; simpl; econstructor; eauto.
    clear H3; induction b0; simpl.
    - intuition.
    - simpl in H0; destruct a; find_if_inside;
        try discriminate.
      intuition.
  Qed.

  Instance cacheAddDNPointer
    : CacheAdd_Guarded _ add_ptr_OK :=
    {| addE_G ce sp := (fst ce, association_list_add (snd ce) (fst sp) (snd sp));
       addD_G cd sp := (fst cd, association_list_add (snd cd) (snd sp) (fst sp));
       add_correct_G := cacheAddDNPointer_pf
    |}.

  Lemma IndependentCaches :
    forall env p (b : nat),
      getD (addD env b) p = getD env p.
  Proof.
    simpl; intros; eauto.
  Qed.

  Lemma IndependentCaches' :
    forall env p (b : nat),
      getE (addE env b) p = getE env p.
  Proof.
    simpl; intros; eauto.
  Qed.

  Lemma getDistinct :
    forall env l p p',
      p <> p'
      -> getD (addD_G env (l, p)) p' = getD env p'.
  Proof.
    simpl; intros; eauto.
    find_if_inside; try congruence.
  Qed.

  Lemma getDistinct' :
    forall env l p p' l',
      List.In p (getE (addE_G env (l', p')) l)
      -> p = p' \/ List.In p (getE env l).
  Proof.
    simpl in *; intros; intuition eauto.
    find_if_inside; simpl in *; intuition eauto.
  Qed.

  Arguments NPeano.div : simpl never.

  Lemma mult_pow2 :
    forall m n,
      pow2 m * pow2 n = pow2 (m + n).
  Proof.
    Local Transparent pow2.
    induction m; simpl; intros.
    - omega.
    - rewrite <- IHm.
      rewrite <- !plus_n_O.
      rewrite mult_plus_distr_r; omega.
  Qed.

  Corollary mult_pow2_8 : forall n,
      8 * (pow2 n) = pow2 (3 + n).
  Proof.
    intros; rewrite <- mult_pow2.
    reflexivity.
  Qed.

  Local Opaque pow2.

  Lemma pow2_div
    : forall m n,
      lt (m + n * 8) (pow2 17)
      -> lt (NPeano.div m 8) (pow2 14).
  Proof.
    intros.
    eapply (NPeano.Nat.mul_lt_mono_pos_l 8); try omega.
    rewrite mult_pow2_8.
    eapply le_lt_trans.
    apply NPeano.Nat.mul_div_le; try omega.
    simpl.
    omega.
  Qed.

  Lemma addPeekNone :
    forall env n,
      peekD env = None
      -> peekD (addD env n) = None.
  Proof.
    simpl; intros.
    destruct (fst env); simpl in *; congruence.
  Qed.

    Lemma addPeekSome :
    forall env n m,
      peekD env = Some m
      -> lt 0 n
      -> lt (n + (pointerT2Nat m)) (pow2 14)
      -> exists p',
          peekD (addD env (n * 8)) = Some p'
          /\ pointerT2Nat p' = n + (pointerT2Nat m).
  Proof.
    simpl; intros; subst.
    destruct (fst env); simpl in *; try discriminate.
    injections.
    find_if_inside.
    - rewrite pointerT2Nat_Nat2pointerT in *;
        try (eapply pow2_div; eassumption).
      eexists; split; try reflexivity.
      rewrite NPeano.Nat.div_add; try omega.
      rewrite pointerT2Nat_Nat2pointerT in *; try omega.
      rewrite NPeano.Nat.div_add in l; omega.
      rewrite NPeano.Nat.div_add in l; omega.
      rewrite NPeano.Nat.div_add in l; omega.
    - elimtype False; apply n1.
      rewrite NPeano.Nat.div_add by omega.
      rewrite pointerT2Nat_Nat2pointerT in *; try omega.
      rewrite pointerT2Nat_Nat2pointerT in *; try omega.


      eapply (mult_lt_compat_l _ _ 8) in H1; try omega.
      rewrite mult_plus_distr_l in H1.
      rewrite (mult_pow2_8 14) in H1.
      destruct n; try omega.
      simpl plus at -1 in H1.
      rewrite pointerT2Nat_Nat2pointerT in *.
      rewrite mult_succ_r in H1.
      rewrite div_eq in H1 by omega.
      assert (lt (NPeano.modulo n0 8) 8).
      apply (NPeano.mod_bound_pos n0 8); try omega.

      assert



      try (eapply pow2_div; eassumption).
        try omega.


  Lemma addZeroPeek :
    forall xenv,
      peekD xenv = peekD (addD xenv 0).
  Proof.
    simpl; intros.
    destruct (fst xenv); simpl; eauto.
    find_if_inside; simpl in *.
  Admitted.

  Variable addPeekNone' :
    forall env n m,
      peekD env = Some m
      -> ~ lt (n + (pointerT2Nat m)) (pow2 14)
      -> peekD (addD env (n * 8)) = None.



    Variable boundPeekSome :
    forall env n m m',
      peekD env = Some m
      -> peekD (addD env (n * 8)) = Some m'
      -> (n + (pointerT2Nat m) < pow2 14)%nat.

    Variable addPeekESome :
    forall env n m,
      peekE env = Some m
      -> (n + (pointerT2Nat m) < pow2 14)%nat
      -> exists p',
          peekE (addE env (n * 8)) = Some p'
          /\ pointerT2Nat p' = n + (pointerT2Nat m).
    Variable boundPeekESome :
    forall env n m m',
      peekE env = Some m
      -> peekE (addE env (n * 8)) = Some m'
      -> (n + (pointerT2Nat m) < pow2 14)%nat.
    Variable addPeekENone :
      forall env n,
        peekE env = None
        -> peekE (addE env n) = None.
    Variable addPeekENone' :
      forall env n m,
        peekE env = Some m
        -> ~ (n + (pointerT2Nat m) < pow2 14)%nat
        -> peekE (addE env (n * 8)) = None.
  Variable addZeroPeekE :
    forall xenv,
      peekE xenv = peekE (addE xenv 0).

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
