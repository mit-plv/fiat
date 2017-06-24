Require Import
        Coq.Strings.String
        Coq.Arith.Mult
        Coq.Vectors.Vector.

Require Import
        Fiat.Examples.DnsServer.SimplePacket
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.DecideableEnsembles
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.BinEncoders.Env.BinLib.AlignedByteString
        Fiat.BinEncoders.Env.BinLib.AlignWord
        Fiat.BinEncoders.Env.BinLib.AlignedDecoders
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

Section DnsPacket.

  Open Scope Tuple_scope.

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
           {K_eq : DecideableEnsembles.Query_eq K}
           (l : association_list K V)
           (k : K) (v : V) : list (K * V)  :=
    (k, v) :: l.

  Instance dns_list_cache : Cache :=
    {| CacheEncode := option (word 17) * association_list string pointerT;
       CacheDecode := option (word 17) * association_list pointerT string;
       Equiv ce cd := fst ce = fst cd
                      /\ (snd ce) = (map (fun ps => match ps with (p, s) => (s, p) end) (snd cd))
                      /\ NoDup (map fst (snd cd))
    |}%type.

  Definition list_CacheEncode_empty : CacheEncode := (Some (wzero _), nil).
  Definition list_CacheDecode_empty : CacheDecode := (Some (wzero _), nil).

  Lemma list_cache_empty_Equiv : Equiv list_CacheEncode_empty list_CacheDecode_empty.
  Proof.
    simpl; intuition; simpl; econstructor.
  Qed.

  Local Opaque pow2.
  Arguments natToWord : simpl never.
  Arguments wordToNat : simpl never.

  (* pointerT2Nat (Nat2pointerT (NPeano.div (wordToNat w) 8)) *)

  Instance cacheAddNat : CacheAdd _ nat :=
    {| addE ce n := (Ifopt (fst ce) as m Then
                                         let n' := (wordToNat m) + n in
                                         if Compare_dec.lt_dec n' (pow2 17)
                                         then Some (natToWord _ n')
                                         else None
                                                Else None, snd ce);
       addD cd n := (Ifopt (fst cd) as m Then
                                         let n' := (wordToNat m) + n in
                                         if Compare_dec.lt_dec n' (pow2 17)
                                         then Some (natToWord _ n')
                                         else None
                                                Else None, snd cd) |}.
  Proof.
    simpl; intuition eauto; destruct a; destruct a0;
      simpl in *; eauto; try congruence.
    injections.
    find_if_inside; eauto.
  Defined.

  Instance Query_eq_string : Query_eq string :=
    {| A_eq_dec := string_dec |}.

  Instance : Query_eq pointerT :=
    {| A_eq_dec := pointerT_eq_dec |}.

  Instance cachePeekDNPointer : CachePeek _ (option pointerT) :=
    {| peekE ce := Ifopt (fst ce) as m Then Some (Nat2pointerT (wordToNat (wtl (wtl (wtl m))))) Else None;
       peekD cd := Ifopt (fst cd) as m Then Some
                                       (Nat2pointerT (wordToNat (wtl (wtl (wtl m)))))
                                       Else None |}.
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

  Instance cacheGetDNPointer : CacheGet dns_list_cache string pointerT :=
    {| getE ce p := @association_list_find_all string _ _ (snd ce) p;
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

  Lemma IndependentCaches''' :
    forall env b,
      peekE (addE_G env b) = peekE env.
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
      rewrite Mult.mult_plus_distr_r; omega.
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

  Lemma wtl_div
    : forall n (w : word (S (S (S n)))),
      wordToNat (wtl (wtl (wtl w))) = NPeano.div (wordToNat w) 8.
  Proof.
    intros.
    pose proof (shatter_word_S w); destruct_ex; subst.
    pose proof (shatter_word_S x0); destruct_ex; subst.
    pose proof (shatter_word_S x2); destruct_ex; subst.
    simpl wtl.
    rewrite <- (NPeano.Nat.div_div _ 2 4) by omega.
    rewrite <- (NPeano.Nat.div_div _ 2 2) by omega.
    rewrite <- !NPeano.Nat.div2_div.
    rewrite !div2_WS.
    reflexivity.
  Qed.

  Lemma mult_lt_compat_l'
    : forall (m n p : nat),
      lt 0 p
      -> lt (p * n)  (p * m)
      -> lt n m.
  Proof.
    induction m; simpl; intros; try omega.
    rewrite (mult_comm p 0) in H0; simpl in *; try omega.
    destruct p; try (elimtype False; auto with arith; omega).
    inversion H0.
    rewrite (mult_comm p (S m)) in H0.
    simpl in H0.
    destruct n; try omega.
    rewrite (mult_comm p (S n)) in H0; simpl in H0.
    apply plus_lt_reg_l in H0.
    rewrite <- NPeano.Nat.succ_lt_mono.
    eapply (IHm n p); try eassumption; try omega.
    rewrite mult_comm.
    rewrite (mult_comm p m); auto.
  Qed.

  Lemma mult_lt_compat_l''
    : forall (p m k n : nat),
      lt 0 p
      -> lt n m
      -> lt k p
      -> lt ((p * n) + k) (p * m).
  Proof.
    induction p; intros; try omega.
    simpl.
    inversion H; subst; simpl.
    inversion H1; subst; omega.
    destruct k; simpl.
    - rewrite <- plus_n_O.
      eapply (mult_lt_compat_l n m (S p)); auto.
    - assert (lt (p * n + k) (p * m)) by
          (apply IHp; try omega).
      omega.
  Qed.

  Lemma addPeekNone' :
    forall env n m,
      peekD env = Some m
      -> ~ lt (n + (pointerT2Nat m)) (pow2 14)
      -> peekD (addD env (n * 8)) = None.
  Proof.
    simpl; intros; subst.
    destruct (fst env); simpl in *; try discriminate.
    injections.
    find_if_inside; try reflexivity.
    unfold If_Opt_Then_Else.
    rewrite !wtl_div in *.
    elimtype False; apply H0.
    rewrite pointerT2Nat_Nat2pointerT in *;
      try (eapply pow2_div; eassumption).
    eapply (mult_lt_compat_l' _ _ 8); try omega.
    destruct n; try omega.
    elimtype False; apply H0.
    simpl.
    eapply (mult_lt_compat_l' _ _ 8); try omega.
    - eapply le_lt_trans.
      apply NPeano.Nat.mul_div_le; omega.
      simpl in l.
      rewrite mult_pow2_8; simpl; omega.
    - rewrite mult_plus_distr_l.
      assert (8 <> 0) by omega.
      pose proof (NPeano.Nat.mul_div_le (wordToNat w) 8 H).
      apply le_lt_trans with (8 * S n + (wordToNat w)).
      omega.
      rewrite mult_pow2_8; simpl; omega.
  Qed.

  Lemma addPeekSome :
    forall env n m,
      peekD env = Some m
      -> lt (n + (pointerT2Nat m)) (pow2 14)
      -> exists p',
          peekD (addD env (n * 8)) = Some p'
          /\ pointerT2Nat p' = n + (pointerT2Nat m).
  Proof.
    simpl; intros; subst.
    destruct (fst env); simpl in *; try discriminate.
    injections.
    find_if_inside.
    - rewrite !wtl_div in *.
      rewrite pointerT2Nat_Nat2pointerT in *;
        try (eapply pow2_div; eassumption).
      unfold If_Opt_Then_Else.
      eexists; split; try reflexivity.
      rewrite wtl_div.
      rewrite wordToNat_natToWord_idempotent.
      rewrite pointerT2Nat_Nat2pointerT in *; try omega.
      rewrite NPeano.Nat.div_add; try omega.
      rewrite NPeano.Nat.div_add; try omega.
      apply Nomega.Nlt_in.
      rewrite Nnat.Nat2N.id, Npow2_nat; auto.
    - elimtype False; apply n0.
      rewrite !wtl_div in *.
      rewrite pointerT2Nat_Nat2pointerT in *.
      rewrite (NPeano.div_mod (wordToNat w) 8); try omega.
      pose proof (mult_pow2_8 14) as H'; simpl plus in H'; rewrite <- H'.
      replace (8 * NPeano.div (wordToNat w) 8 + NPeano.modulo (wordToNat w) 8 + n * 8)
      with (8 * (NPeano.div (wordToNat w) 8 + n) + NPeano.modulo (wordToNat w) 8)
        by omega.
      eapply mult_lt_compat_l''; try omega.
      apply NPeano.Nat.mod_upper_bound; omega.
      eapply (mult_lt_compat_l' _ _ 8); try omega.
      eapply le_lt_trans.
      apply NPeano.Nat.mul_div_le; omega.
      rewrite mult_pow2_8; simpl.
      apply wordToNat_bound.
  Qed.

  Lemma addZeroPeek :
    forall xenv,
      peekD xenv = peekD (addD xenv 0).
  Proof.
    simpl; intros.
    destruct (fst xenv); simpl; eauto.
    find_if_inside; unfold If_Opt_Then_Else.
    rewrite <- plus_n_O, natToWord_wordToNat; auto.
    elimtype False; apply n.
    rewrite <- plus_n_O.
    apply wordToNat_bound.
  Qed.

  Local Opaque wordToNat.
  Local Opaque natToWord.

  Lemma boundPeekSome :
    forall env n m m',
      peekD env = Some m
      -> peekD (addD env (n * 8)) = Some m'
      -> lt (n + (pointerT2Nat m)) (pow2 14).
  Proof.
    simpl; intros; subst.
    destruct (fst env); simpl in *; try discriminate.
    injections.
    find_if_inside; unfold If_Opt_Then_Else in *; try congruence.
    injections.
    rewrite !wtl_div in *.
    rewrite pointerT2Nat_Nat2pointerT in *;
      try (eapply pow2_div; eassumption).
    eapply (mult_lt_compat_l' _ _ 8); try omega.
    - rewrite mult_plus_distr_l.
      assert (8 <> 0) by omega.
      pose proof (NPeano.Nat.mul_div_le (wordToNat w) 8 H).
      apply le_lt_trans with (8 * n + (wordToNat w)).
      omega.
      rewrite mult_pow2_8.
      simpl plus at -1.
      omega.
  Qed.

  Lemma addPeekESome :
    forall env n m,
      peekE env = Some m
      -> lt (n + (pointerT2Nat m)) (pow2 14)%nat
      -> exists p',
          peekE (addE env (n * 8)) = Some p'
          /\ pointerT2Nat p' = n + (pointerT2Nat m).
  Proof.
    simpl; intros; subst.
    destruct (fst env); simpl in *; try discriminate.
    injections.
    find_if_inside.
    - rewrite !wtl_div in *.
      rewrite pointerT2Nat_Nat2pointerT in *;
        try (eapply pow2_div; eassumption).
      unfold If_Opt_Then_Else.
      eexists; split; try reflexivity.
      rewrite wtl_div.
      rewrite wordToNat_natToWord_idempotent.
      rewrite pointerT2Nat_Nat2pointerT in *; try omega.
      rewrite NPeano.Nat.div_add; try omega.
      rewrite NPeano.Nat.div_add; try omega.
      apply Nomega.Nlt_in.
      rewrite Nnat.Nat2N.id, Npow2_nat; auto.
    - elimtype False; apply n0.
      rewrite !wtl_div in *.
      rewrite pointerT2Nat_Nat2pointerT in *.
      rewrite (NPeano.div_mod (wordToNat w) 8); try omega.
      pose proof (mult_pow2_8 14) as H'; simpl plus in H'; rewrite <- H'.
      replace (8 * NPeano.div (wordToNat w) 8 + NPeano.modulo (wordToNat w) 8 + n * 8)
      with (8 * (NPeano.div (wordToNat w) 8 + n) + NPeano.modulo (wordToNat w) 8)
        by omega.
      eapply mult_lt_compat_l''; try omega.
      apply NPeano.Nat.mod_upper_bound; omega.
      eapply (mult_lt_compat_l' _ _ 8); try omega.
      eapply le_lt_trans.
      apply NPeano.Nat.mul_div_le; omega.
      rewrite mult_pow2_8; simpl.
      apply wordToNat_bound.
  Qed.

  Lemma boundPeekESome :
    forall env n m m',
      peekE env = Some m
      -> peekE (addE env (n * 8)) = Some m'
      -> lt (n + (pointerT2Nat m)) (pow2 14).
  Proof.
    simpl; intros; subst.
    destruct (fst env); simpl in *; try discriminate.
    injections.
    find_if_inside; unfold If_Opt_Then_Else in *; try congruence.
    injections.
    rewrite !wtl_div in *.
    rewrite pointerT2Nat_Nat2pointerT in *;
      try (eapply pow2_div; eassumption).
    eapply (mult_lt_compat_l' _ _ 8); try omega.
    - rewrite mult_plus_distr_l.
      assert (8 <> 0) by omega.
      pose proof (NPeano.Nat.mul_div_le (wordToNat w) 8 H).
      apply le_lt_trans with (8 * n + (wordToNat w)).
      omega.
      rewrite mult_pow2_8.
      simpl plus at -1.
      omega.
  Qed.

  Lemma addPeekENone :
    forall env n,
      peekE env = None
      -> peekE (addE env n) = None.
  Proof.
    simpl; intros.
    destruct (fst env); simpl in *; congruence.
  Qed.

  Lemma addPeekENone' :
    forall env n m,
      peekE env = Some m
      -> ~ lt (n + (pointerT2Nat m)) (pow2 14)%nat
      -> peekE (addE env (n * 8)) = None.
  Proof.
    simpl; intros; subst.
    destruct (fst env); simpl in *; try discriminate.
    injections.
    find_if_inside; try reflexivity.
    unfold If_Opt_Then_Else.
    rewrite !wtl_div in *.
    elimtype False; apply H0.
    rewrite pointerT2Nat_Nat2pointerT in *;
      try (eapply pow2_div; eassumption).
    eapply (mult_lt_compat_l' _ _ 8); try omega.
    destruct n; try omega.
    elimtype False; apply H0.
    simpl.
    eapply (mult_lt_compat_l' _ _ 8); try omega.
    - eapply le_lt_trans.
      apply NPeano.Nat.mul_div_le; omega.
      simpl in l.
      rewrite mult_pow2_8; simpl; omega.
    - rewrite mult_plus_distr_l.
      assert (8 <> 0) by omega.
      pose proof (NPeano.Nat.mul_div_le (wordToNat w) 8 H).
      apply le_lt_trans with (8 * S n + (wordToNat w)).
      omega.
      rewrite mult_pow2_8; simpl; omega.
  Qed.

  Lemma addZeroPeekE :
    forall xenv,
      peekE xenv = peekE (addE xenv 0).
  Proof.
    simpl; intros.
    destruct (fst xenv); simpl; eauto.
    find_if_inside; unfold If_Opt_Then_Else.
    rewrite <- plus_n_O, natToWord_wordToNat; auto.
    elimtype False; apply n.
    rewrite <- plus_n_O.
    apply wordToNat_bound.
  Qed.

  Import Vectors.VectorDef.VectorNotations.

  Definition GoodCache (env : CacheDecode) :=
    forall domain p,
      getD env p = Some domain
      -> ValidDomainName domain
         /\ (String.length domain > 0)%nat
         /\ (getD env p = Some domain
             -> forall p' : pointerT, peekD env = Some p' -> lt (pointerT2Nat p) (pointerT2Nat p')).

  Lemma cacheIndependent_add
    : forall (b : nat) (cd : CacheDecode),
      GoodCache cd -> GoodCache (addD cd b).
  Proof.
    unfold GoodCache; intros.
    rewrite IndependentCaches in *;
      eapply H in H0; intuition eauto.
    simpl in *.
    destruct (fst cd); simpl in *; try discriminate.
    find_if_inside; simpl in *; try discriminate.
    injections.
    pose proof (H4 _ (eq_refl _)).
    eapply lt_le_trans; eauto.
    rewrite !pointerT2Nat_Nat2pointerT in *;
      rewrite !wtl_div in *.
    rewrite wordToNat_natToWord_idempotent.
    apply NPeano.Nat.div_le_mono; omega.
    apply Nomega.Nlt_in.
    rewrite Nnat.Nat2N.id, Npow2_nat; auto.
    eapply (mult_lt_compat_l' _ _ 8); try omega.
    + eapply le_lt_trans.
      apply NPeano.Nat.mul_div_le; omega.
      rewrite wordToNat_natToWord_idempotent.
      rewrite mult_pow2_8; simpl; omega.
      apply Nomega.Nlt_in.
      rewrite Nnat.Nat2N.id, Npow2_nat; auto.
    + eapply (mult_lt_compat_l' _ _ 8); try omega.
      eapply le_lt_trans.
      apply NPeano.Nat.mul_div_le; omega.
      rewrite mult_pow2_8; simpl; omega.
    + eapply (mult_lt_compat_l' _ _ 8); try omega.
      eapply le_lt_trans.
      apply NPeano.Nat.mul_div_le; omega.
      rewrite mult_pow2_8; simpl; omega.
    + eapply (mult_lt_compat_l' _ _ 8); try omega.
      eapply le_lt_trans.
      apply NPeano.Nat.mul_div_le; omega.
      rewrite mult_pow2_8; simpl; omega.
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
      -> getD (addD_G cd (domain', p0)) p = Some domain
      -> forall pre label post : string,
          domain = (pre ++ label ++ post)%string ->
          ValidLabel label -> (String.length label <= 63)%nat.
  Proof.
    unfold GoodCache; simpl; intros.
    destruct (pointerT_eq_dec p p0); subst.
    - injections; intuition.
      eapply H1; eauto.
    - eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_9
    : forall cd p p0 domain domain',
      GoodCache cd
      -> ValidDomainName domain' /\ (String.length domain' > 0)%nat
      -> getD (addD_G cd (domain', p0)) p = Some domain
      -> ValidDomainName domain.
  Proof.
    unfold GoodCache; simpl; intros.
    destruct (pointerT_eq_dec p p0); subst.
    - injections; intuition.
    - eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_10
    : forall cd p p0 domain domain',
      GoodCache cd
      -> ValidDomainName domain' /\ (String.length domain' > 0)%nat
      -> getD (addD_G cd (domain', p0)) p = Some domain
      -> gt (String.length domain) 0.
  Proof.
    unfold GoodCache; simpl; intros.
    destruct (pointerT_eq_dec p p0); subst.
    - injections; intuition.
    - eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_11
    : forall (b : nat)
             (cd : CacheDecode)
             (domain : string)
             (p : pointerT),
      GoodCache cd
      -> getD (addD cd b) p = Some domain ->
      forall p' : pointerT, peekD (addD cd b) = Some p' -> lt (pointerT2Nat p) (pointerT2Nat p').
  Proof.
    intros.
    eapply (cacheIndependent_add b) in H.
    eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_12
    : forall (p : pointerT) (cd : CacheDecode) (domain : string),
      GoodCache cd ->
      getD cd p = Some domain
      -> forall p' : pointerT,
          peekD cd = Some p'
          -> lt (pointerT2Nat p) (pointerT2Nat p').
  Proof.
    unfold GoodCache; simpl; intros; intuition eauto.
    eapply H; eauto.
  Qed.

  Lemma cacheIndependent_add_13
    : forall  (env : CacheDecode)
              (p : pointerT)
              (domain : string)
              (H : GoodCache env)
              (H0 : ValidDomainName domain /\ (String.length domain > 0)%nat)
              (H1 : getD env p = None)
              (H2 : forall p' : pointerT, peekD env = Some p' -> lt (pointerT2Nat p) (pointerT2Nat p'))
              (domain0 : string)
              (p0 : pointerT)
              (H3 : getD (addD_G env (domain, p)) p0 = Some domain0)
              (p' : pointerT),
      peekD (addD_G env (domain, p)) = Some p'
      -> lt (pointerT2Nat p0) (pointerT2Nat p').
  Proof.
    simpl; intros.
    destruct (fst env) eqn: ?; simpl in *; try discriminate.
    find_if_inside; subst.
    - injections.
      apply (H2 _ (eq_refl _)).
    - injections.
      pose proof (H2 _ (eq_refl _)).
      unfold GoodCache in *; intuition.
      eapply H; simpl.
      eassumption.
      eassumption.
      rewrite Heqo; simpl; reflexivity.
  Qed.

  Lemma addD_addD_plus :
    forall (cd : CacheDecode) (n m : nat), addD (addD cd n) m = addD cd (n + m).
  Proof.
    simpl; intros.
    destruct (fst cd); simpl; eauto.
    repeat (find_if_inside; simpl); eauto.
    f_equal; f_equal.
    rewrite !natToWord_plus.
    rewrite !natToWord_wordToNat.
    rewrite wplus_assoc; reflexivity.
    rewrite !natToWord_plus in l0.
    rewrite !natToWord_wordToNat in l0.
    elimtype False.
    apply n0.
    rewrite <- (natToWord_wordToNat w) in l0.
    rewrite <- natToWord_plus in l0.
    rewrite wordToNat_natToWord_idempotent in l0.
    omega.
    apply Nomega.Nlt_in; rewrite Nnat.Nat2N.id, Npow2_nat; assumption.
    elimtype False.
    apply n0.
    rewrite <- (natToWord_wordToNat w).
    rewrite !natToWord_plus.
    rewrite !wordToNat_natToWord_idempotent.
    rewrite <- natToWord_plus.
    rewrite !wordToNat_natToWord_idempotent.
    omega.
    apply Nomega.Nlt_in; rewrite Nnat.Nat2N.id, Npow2_nat; assumption.
    apply Nomega.Nlt_in; rewrite Nnat.Nat2N.id, Npow2_nat; omega.
    omega.
  Qed.

  Lemma addE_addE_plus :
    forall (cd : CacheEncode) (n m : nat), addE (addE cd n) m = addE cd (n + m).
  Proof.
    simpl; intros.
    destruct (fst cd); simpl; eauto.
    repeat (find_if_inside; simpl); eauto.
    f_equal; f_equal.
    rewrite !natToWord_plus.
    rewrite !natToWord_wordToNat.
    rewrite wplus_assoc; reflexivity.
    rewrite !natToWord_plus in l0.
    rewrite !natToWord_wordToNat in l0.
    elimtype False.
    apply n0.
    rewrite <- (natToWord_wordToNat w) in l0.
    rewrite <- natToWord_plus in l0.
    rewrite wordToNat_natToWord_idempotent in l0.
    omega.
    apply Nomega.Nlt_in; rewrite Nnat.Nat2N.id, Npow2_nat; assumption.
    elimtype False.
    apply n0.
    rewrite <- (natToWord_wordToNat w).
    rewrite !natToWord_plus.
    rewrite !wordToNat_natToWord_idempotent.
    rewrite <- natToWord_plus.
    rewrite !wordToNat_natToWord_idempotent.
    omega.
    apply Nomega.Nlt_in; rewrite Nnat.Nat2N.id, Npow2_nat; assumption.
    apply Nomega.Nlt_in; rewrite Nnat.Nat2N.id, Npow2_nat; omega.
    omega.
  Qed.

  Ltac solve_GoodCache_inv foo :=
    lazymatch goal with
      |- cache_inv_Property ?Z _ =>
      unify Z GoodCache;
      unfold cache_inv_Property; repeat split;
      eauto using cacheIndependent_add, cacheIndependent_add_2, cacheIndependent_add_4, cacheIndependent_add_6, cacheIndependent_add_7, cacheIndependent_add_8, cacheIndependent_add_10, cacheIndependent_add_11, cacheIndependent_add_12, cacheIndependent_add_13;
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
    ith
      (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
             (icons (B := fun T => T -> Prop) (fun _ : Memory.W => True)
                    (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
                           (icons (B := fun T => T -> Prop) (fun a : SOA_RDATA =>
                                                               (True /\ ValidDomainName a!"contact_email") /\ ValidDomainName a!"sourcehost") inil))))
      (SumType_index
         (DomainName
            :: (Memory.W : Type)
            :: DomainName
            :: [SOA_RDATA])
         rr!sRDATA)
      (SumType_proj
         (DomainName
            :: (Memory.W : Type)
            :: DomainName
            :: [SOA_RDATA])
         rr!sRDATA)
    /\ ValidDomainName rr!sNAME.

  Lemma resourceRecordOK_1
    : forall data : resourceRecord,
      resourceRecord_OK data -> (fun domain : string => ValidDomainName domain) data!sNAME.
  Proof.
    unfold resourceRecord_OK; intuition eauto.
  Qed.
  Hint Resolve resourceRecordOK_1 : data_inv_hints.

  Lemma resourceRecordOK_3
    : forall rr : resourceRecord,
      resourceRecord_OK rr ->
      ith
        (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
               (icons (B := fun T => T -> Prop) (fun _ : Memory.W => True)
                      (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
                             (icons (B := fun T => T -> Prop) (fun a : SOA_RDATA =>
                                                                 (True /\ ValidDomainName a!"contact_email") /\ ValidDomainName a!"sourcehost") inil))))        (SumType_index ResourceRecordTypeTypes rr!sRDATA)
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

  Definition encode_rdata_Spec :=
    encode_SumType_Spec ResourceRecordTypeTypes
                        (icons (encode_CNAME_Spec)  (* CNAME; canonical name for an alias 	[RFC1035] *)
                               (icons encode_A_Spec (* A; host address 	[RFC1035] *)
                                      (icons (encode_NS_Spec) (* NS; authoritative name server 	[RFC1035] *)
                                             (icons encode_SOA_RDATA_Spec  (* SOA rks the start of a zone of authority 	[RFC1035] *) inil)))).

  Definition encode_resource_Spec(r : resourceRecord) :=
    encode_DomainName_Spec r!sNAME
                           ThenC encode_enum_Spec RRecordType_Ws (RDataTypeToRRecordType r!sRDATA)
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
      eapply (DomainName_decode_correct
                IndependentCaches IndependentCaches' IndependentCaches'''
                getDistinct getDistinct' addPeekSome
                boundPeekSome addPeekNone addPeekNone'
                addZeroPeek addPeekESome boundPeekESome
                addPeekENone addPeekENone')
    | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_list_Spec encode_resource_Spec) _ _] =>
      intros; apply FixList_decode_correct with (A_predicate := resourceRecord_OK)
    end.

  Ltac synthesize_decoder_ext
       transformer
       decode_step'
       determineHooks
       synthesize_cache_invariant' :=
    (* Combines tactics into one-liner. *)
    start_synthesizing_decoder;
    [ normalize_compose transformer;
      repeat first [decode_step' idtac | decode_step determineHooks]
    | cbv beta; synthesize_cache_invariant' idtac
    |  ].

  Print encode_DomainName_Spec.

  Lemma byte_align_Fix_encoder {A}
        (lt_A : A -> A -> Prop)
        (wf_lt_A : well_founded lt_A)
    : forall
      (body : FixComp.funType [A; CacheEncode] (ByteString * CacheEncode)
              -> FixComp.funType [A; CacheEncode] (ByteString * CacheEncode))
      (body' : forall r : A,
          (forall r' : A, lt_A r' r -> FixComp.LeastFixedPointFun.cfunType [CacheEncode] ({n : _ & Vector.t (word 8) n} * CacheEncode)) ->
          FixComp.LeastFixedPointFun.cfunType [CacheEncode] ({n : _ & Vector.t (word 8) n} * CacheEncode))

      (refine_body_OK : forall (r : A)
                               (x : A -> CacheEncode  ->
                                    Comp (ByteString * CacheEncode))
                               (y : forall r' : A,
                                   lt_A r' r ->
                                   CacheEncode ->
                                   {n : _ & Vector.t (word 8) n} * CacheEncode),
          (forall (a' : A) (wf_r : lt_A a' r) (ce : CacheEncode),
              refine (x a' ce)
                     (ret (let (v, ce') := y a' wf_r ce in
                           (build_aligned_ByteString (projT2 v), ce'))))
          -> forall ce, refine (body x r ce) (ret (let (v, ce') := body' r y ce in
                                                   (build_aligned_ByteString (projT2 v), ce'))))

      (body_monotone : forall rec rec' : FixComp.funType [A; CacheEncode] (ByteString * CacheEncode),
          FixComp.refineFun rec rec' -> FixComp.refineFun (body rec) (body rec'))
      (body'_monotone : forall (x0 : A)
                               (f
                                  g : {y : A | lt_A y x0} ->
                                      option (word 17) * association_list string pointerT ->
                                      {n : nat & t (word 8) n} * (option (word 17) * association_list string pointerT)),
          (forall y : {y : A | lt_A y x0}, f y = g y) ->
          body' x0 (fun (a' : A) (lt_a' : lt_A a' x0) => f (exist (fun a'0 : A => lt_A a'0 x0) a' lt_a')) =
          body' x0 (fun (a' : A) (lt_a' : lt_A a' x0) => g (exist (fun a'0 : A => lt_A a'0 x0) a' lt_a')))
      (a : A) (ce : CacheEncode),
      refine (FixComp.LeastFixedPointFun.LeastFixedPoint body a ce)
                (ret (let (v, ce') := Fix wf_lt_A _ body' a ce in
                      (build_aligned_ByteString (projT2 v), ce'))).
  Proof.
    intros.
    unfold FixComp.LeastFixedPointFun.LeastFixedPoint, respectful_hetero; intros.
    simpl.
    revert ce; pattern a; eapply (well_founded_ind wf_lt_A).
    simpl; intros.
    pose proof (proj1 (Frame.Is_GreatestFixedPoint (O := @FixComp.LeastFixedPointFun.funDefOps [A; CacheEncode] (ByteString * CacheEncode)) _ (body_monotone))); etransitivity.
    eapply H0; eauto.
    destruct (Fix wf_lt_A
             (fun _ : A =>
              option (word 17) * association_list string pointerT ->
              {n : nat & t (word 8) n} * (option (word 17) * association_list string pointerT)) body' x ce) eqn: ?.
    pose proof (Fix_eq _ _ wf_lt_A _ (fun a rec => body' a (fun a' lt_a' => rec (existT (fun a' => lt_A a' a) a' lt_a')))).
    simpl in H1; unfold Fix_sub, Fix_F_sub in H1; unfold Fix, Fix_F in Heqp.
    rewrite H1 in Heqp; simpl in Heqp; clear H1; eauto.
    etransitivity.
    eapply refine_body_OK.
    instantiate (1 := (fun (a' : A) (_ : lt_A a' x) =>
            (fix Fix_F_sub (x0 : A) (r : Acc lt_A x0) {struct r} :
               option (word 17) * association_list string pointerT ->
               {n : nat & t (word 8) n} * (option (word 17) * association_list string pointerT) :=
               body' x0 (fun (a'0 : A) (lt_a'0 : lt_A a'0 x0) => Fix_F_sub a'0 (Acc_inv r lt_a'0))) a'
              (wf_lt_A a'))).
    eapply H; eauto.
    rewrite Heqp; reflexivity.
  Qed.

  Lemma byte_align_Fix_encoder_inv {A}
        (A_OK : A -> Prop)
        (lt_A : _ -> _ -> Prop)
        (wf_lt_A : well_founded lt_A)
    : forall
      (body : FixComp.funType [A; CacheEncode] (ByteString * CacheEncode)
              -> FixComp.funType [A; CacheEncode] (ByteString * CacheEncode))
      (body' : forall r : { a : _ & A_OK a},
          (forall r' : { a : _ & A_OK a},
              lt_A r' r
              -> FixComp.LeastFixedPointFun.cfunType [CacheEncode] ({n : _ & Vector.t (word 8) n} * CacheEncode)) ->
          FixComp.LeastFixedPointFun.cfunType [CacheEncode] ({n : _ & Vector.t (word 8) n} * CacheEncode))
      (refine_body_OK : forall (r : { a : _ & A_OK a})
                               (x : A -> CacheEncode ->
                                    Comp (ByteString * CacheEncode))
                               (y : forall r' : { a : _ & A_OK a},
                                   lt_A r' r ->
                                   CacheEncode ->
                                   {n : _ & Vector.t (word 8) n} * CacheEncode),
          (forall (a' : { a : _ & A_OK a}) (wf_r : lt_A a' r) (ce : CacheEncode),
              refine (x (projT1 a') ce)
                     (ret (let (v, ce') := y a' wf_r ce in
                           (build_aligned_ByteString (projT2 v), ce'))))
          -> forall ce, refine (body x (projT1 r) ce) (ret (let (v, ce') := body' r y ce in
                                                            (build_aligned_ByteString (projT2 v), ce'))))

      (body_monotone : forall rec rec' : FixComp.funType [A; CacheEncode] (ByteString * CacheEncode),
          FixComp.refineFun rec rec' -> FixComp.refineFun (body rec) (body rec'))
      (body'_monotone : forall (x0 : { a : _ & A_OK a})
                               (f
                                  g : {y : { a : _ & A_OK a} | lt_A y x0} ->
                                      option (word 17) * association_list string pointerT ->
                                      {n : nat & t (word 8) n} * (option (word 17) * association_list string pointerT)),
          (forall y : {y : { a : _ & A_OK a} | lt_A y x0}, f y = g y) ->
          body' x0 (fun (a' : { a : _ & A_OK a}) (lt_a' : lt_A a' x0) => f (exist (fun a'0 : { a : _ & A_OK a} => lt_A a'0 x0) a' lt_a')) =
          body' x0 (fun (a' : { a : _ & A_OK a}) (lt_a' : lt_A a' x0) => g (exist (fun a'0 : { a : _ & A_OK a} => lt_A a'0 x0) a' lt_a')))
      (a : A) (ce : CacheEncode) (a_OK : A_OK a),
      refine (FixComp.LeastFixedPointFun.LeastFixedPoint body a ce)
                (ret (let (v, ce') := Fix wf_lt_A _ body' (existT _ _ a_OK) ce in
                      (build_aligned_ByteString (projT2 v), ce'))).
  Proof.
    intros.
    unfold FixComp.LeastFixedPointFun.LeastFixedPoint, respectful_hetero; intros.
    simpl.
    replace a with (projT1 (existT _ a a_OK)) at 1.
    revert ce; pattern (existT _ a a_OK); eapply (well_founded_ind wf_lt_A).
    simpl; intros.
    pose proof (proj1 (Frame.Is_GreatestFixedPoint (O := @FixComp.LeastFixedPointFun.funDefOps [A; CacheEncode] (ByteString * CacheEncode)) _ (body_monotone))); etransitivity.
    eapply H0; eauto.
    destruct ( Fix wf_lt_A
               (fun _ : {a0 : A & A_OK a0} =>
                option (word 17) * association_list string pointerT ->
                {n : nat & t (word 8) n} * (option (word 17) * association_list string pointerT)) body' x ce) eqn: ?.
    pose proof (Fix_eq _ _ wf_lt_A _ (fun a rec => body' a (fun a' lt_a' => rec (existT (fun a' => lt_A a' a) a' lt_a')))).
    simpl in H1; unfold Fix_sub, Fix_F_sub in H1; unfold Fix, Fix_F in Heqp.
    rewrite H1 in Heqp; simpl in Heqp; clear H1; eauto.
    etransitivity.
    eapply refine_body_OK.
    instantiate (1 := fun (a' : {a0 : A & A_OK a0}) (_ : lt_A a' x) =>
            (fix Fix_F_sub (x0 : {a0 : A & A_OK a0}) (r : Acc lt_A x0) {struct r} :
               option (word 17) * association_list string pointerT ->
               {n : nat & t (word 8) n} * (option (word 17) * association_list string pointerT) :=
               body' x0 (fun (a'0 : {a0 : A & A_OK a0}) (lt_a'0 : lt_A a'0 x0) => Fix_F_sub a'0 (Acc_inv r lt_a'0))) a'
              (wf_lt_A a')).
    eapply H; eauto.
    rewrite Heqp; reflexivity.
    reflexivity.
  Qed.

  Fixpoint split_string (s : string) : (string * string) :=
    match s with
    | EmptyString => ("", "")
    | String a s' => If Ascii.ascii_dec a "." Then ("", s')
                        Else let (s1, s2) := split_string s' in
                             (String a s1, s2)
    end%string.

  Lemma split_string_ValidDomainName :
    forall d,
      ValidDomainName d ->
      ValidDomainName (snd (split_string d)).
  Proof.
  Admitted.

  Lemma split_string_ValidDomainName_length :
    forall d,
      d <> ""%string
      -> lt (String.length (snd (split_string d))) (String.length d).
  Proof.
    induction d; simpl; intros; try congruence.
    find_if_inside; simpl; eauto.
    destruct d; simpl in *; eauto.
    destruct (If Ascii.ascii_dec a0 "." Then (""%string, d)
               Else (let (s1, s2) := split_string d in (String a0 s1, s2))).
    simpl in *.
    etransitivity.
    apply IHd.
    congruence.
    eauto with arith.
  Qed.

  Lemma split_string_OK
    : forall d,
      ValidDomainName d ->
      (d = (fst (split_string (d)) ++ String "." (snd (split_string (d))))%string \/
       split_string (d) = (d, ""%string)) /\
      RRecordTypes.ValidLabel (fst (split_string (d))) /\
      (forall label' post' : string,
          d = (label' ++ post')%string ->
          RRecordTypes.ValidLabel label' -> (String.length label' <= String.length (fst (split_string (d))))%nat).
  Proof.
  Admitted.

  Lemma well_founded_string_length
    : well_founded (fun y r : string => lt (String.length y) (String.length r)%nat).
  Proof.
  Admitted.

  Lemma well_founded_string_length'
    : well_founded (fun y r : {a : string & ValidDomainName a} => lt (String.length (projT1 y)) (String.length (projT1 r))%nat).
  Proof.
  Admitted.

  Definition aligned_encode_DomainName :=
             Fix well_founded_string_length
                  (fun _ : string  =>
                   FixComp.LeastFixedPointFun.cfunType [CacheEncode] ({n : nat & t (word 8) n} * CacheEncode))
                  (fun (r : string)
                     (y : forall r' : string,
                          lt (String.length r') (String.length r)%nat ->
                          CacheEncode -> {n : nat & t (word 8) n} * CacheEncode)
                     (ce : CacheEncode) =>
                     match string_dec r "" with
                     | left e =>
                       (existT (fun n : nat => t (word 8) n) 1 [NToWord 8 (Ascii.N_of_ascii terminal_char)], addE ce 8)
                     | right e => (existT (fun n : nat => t (word 8) n)
                           (1 + String.length (fst (split_string r)) +
                            projT1
                              (fst
                                 (y
                                    ((snd (split_string r)))
                                    (split_string_ValidDomainName_length r e)
                                    (Ifopt Ifopt fst ce as m
                                           Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                then Some (natToWord 17 (wordToNat m + 8))
                                                else None Else None as m
                                     Then if Compare_dec.lt_dec
                                               (wordToNat m + 8 * String.length (fst (split_string r)))
                                               (pow2 17)
                                          then
                                           Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string r))))
                                          else None Else None,
                                    snd ce))))
                           (([natToWord 8 (String.length (let (x0, _) := split_string r in x0))] ++
                             StringToBytes (fst (split_string r))) ++
                            projT2
                              (fst
                                 (y
                                    (snd (split_string r))
                                    (split_string_ValidDomainName_length r e)
                                    (Ifopt Ifopt fst ce as m
                                           Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                then Some (natToWord 17 (wordToNat m + 8))
                                                else None Else None as m
                                     Then if Compare_dec.lt_dec
                                               (wordToNat m + 8 * String.length (fst (split_string r)))
                                               (pow2 17)
                                          then
                                           Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string r))))
                                          else None Else None,
                                    snd ce)))),
                        Ifopt Ifopt fst ce as m Then Some (Nat2pointerT (wordToNat (wtl (wtl (wtl m))))) Else None as curPtr
                        Then (fst
                                (snd
                                   (y
                                      (snd (split_string r))
                                      (split_string_ValidDomainName_length r e)
                                      (Ifopt Ifopt
                                             fst ce as m
                                             Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                  then Some (natToWord 17 (wordToNat m + 8))
                                                  else None Else None as m
                                       Then if Compare_dec.lt_dec
                                                 (wordToNat m + 8 * String.length (fst (split_string r)))
                                                 (pow2 17)
                                            then
                                             Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string r))))
                                            else None Else None,
                                      snd ce))),
                             ((r, curPtr)
                              :: snd
                                   (snd
                                      (y (snd (split_string r))
                                         (split_string_ValidDomainName_length r e)
                                         (Ifopt Ifopt
                                                fst ce as m
                                                Then
                                                if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                then Some (natToWord 17 (wordToNat m + 8))
                                                else None Else None as m
                                          Then if Compare_dec.lt_dec
                                                  (wordToNat m + 8 * String.length (fst (split_string r)))
                                                  (pow2 17)
                                               then
                                                Some
                                                  (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string r))))
                                               else None Else None,
                                         snd ce))))%list)
                        Else snd
                               (y
                                  (snd (split_string r))
                                  (split_string_ValidDomainName_length r e)
                                  (Ifopt Ifopt fst ce as m
                                         Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                              then Some (natToWord 17 (wordToNat m + 8))
                                              else None Else None as m
                                   Then if Compare_dec.lt_dec
                                             (wordToNat m + 8 * String.length (fst (split_string r)))
                                             (pow2 17)
                                        then Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string r))))
                                        else None Else None,
                                                                     snd ce)))
                     end).

  Lemma refine_If_string_dec {A}
    : forall s s' (t e : Comp A)
             (t' : s = s' -> Comp A)
             (e' : s <> s' -> Comp A),
      (forall e'', refine t (t' e''))
      -> (forall n, refine e (e' n))
      -> refine (If string_dec s s' Then t Else e)
             (match string_dec s s' with
              | left e'' => t' e''
              | right n => e' n
              end).
  Proof.
    intros; destruct (string_dec s s'); auto.
  Qed.

  Lemma align_encode_DomainName
    : forall d ce
      (d_OK : ValidDomainName d),
      refine (encode_DomainName_Spec d ce)
             (ret (build_aligned_ByteString (projT2 (fst (aligned_encode_DomainName d ce))),
                   (snd (aligned_encode_DomainName d ce)))).
  Proof.
    intros.
    etransitivity.
    eapply (byte_align_Fix_encoder_inv ValidDomainName) with
    (lt_A := fun a a' => lt (String.length (projT1 a)) (String.length (projT1 a')));
      eauto using encode_body_monotone.
    intros.
    etransitivity.
    match goal with
      |- refine (If_Then_Else (bool_of_sumbool (string_dec ?s ?s')) _ _) _ =>
      subst_refine_evar; eapply (refine_If_string_dec s s');
        let H := fresh in
        intro H; set_refine_evar; try rewrite H; simpl
    end.
    unfold AsciiOpt.encode_ascii_Spec; rewrite aligned_encode_char_eq.
    subst_refine_evar; higher_order_reflexivity.
    refine pick val None; try congruence.
    simplify with monad laws; simpl.
    unfold Bind2.
    refine pick val (split_string (projT1 r)).
    simplify with monad laws.
    unfold encode_nat_Spec.
    rewrite aligned_encode_char_eq.
    simplify with monad laws.
    rewrite encode_string_ByteString.
    simplify with monad laws.
    unfold snd at 2; unfold snd at 2.
    unfold fst at 2; unfold fst at 2.
    unfold fst at 2.
    rewrite (H (exist _ _ (split_string_ValidDomainName _ (projT2 r)))
                   (split_string_ValidDomainName_length _ H0)).
    simplify with monad laws.
    Arguments mult : simpl never.
    simpl.
    subst_refine_evar; higher_order_reflexivity.
    auto using addE_addE_plus.
    destruct r; apply split_string_OK.
    simpl; eauto.
    instantiate (1 := (fun (r : {a : string & ValidDomainName a})
                     (y : forall r' : {a : string & ValidDomainName a},
                          lt (String.length (projT1 r')) (String.length (projT1 r))%nat ->
                          CacheEncode -> {n : nat & t (word 8) n} * CacheEncode)
                     (ce : CacheEncode) =>
                   match string_dec (projT1 r) "" with
                   | left _ =>  (existT (fun n : nat => t (word 8) n) 1 [NToWord 8 (Ascii.N_of_ascii terminal_char)], addE ce 8)
                   | right n' =>  (existT (fun n : nat => t (word 8) n)
                           (1 + String.length (fst (split_string (projT1 r))) +
                            projT1
                              (fst
                                 (y
                                    (existT ValidDomainName
                                       (snd (split_string (projT1 r)))
                                       (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                    (split_string_ValidDomainName_length (projT1 r) n')
                                    (Ifopt Ifopt fst ce as m
                                           Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                then Some (natToWord 17 (wordToNat m + 8))
                                                else None Else None as m
                                     Then if Compare_dec.lt_dec
                                               (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                               (pow2 17)
                                          then
                                           Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                          else None Else None,
                                    snd ce))))
                           (([natToWord 8 (String.length (let (x0, _) := split_string (projT1 r) in x0))] ++
                             StringToBytes (fst (split_string (projT1 r)))) ++
                            projT2
                              (fst
                                 (y
                                    (existT ValidDomainName
                                       (snd (split_string (projT1 r)))
                                       (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                    (split_string_ValidDomainName_length (projT1 r) n')
                                    (Ifopt Ifopt fst ce as m
                                           Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                then Some (natToWord 17 (wordToNat m + 8))
                                                else None Else None as m
                                     Then if Compare_dec.lt_dec
                                               (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                               (pow2 17)
                                          then
                                           Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                          else None Else None,
                                    snd ce)))),
                        Ifopt Ifopt fst ce as m Then Some (Nat2pointerT (wordToNat (wtl (wtl (wtl m))))) Else None as curPtr
                        Then (fst
                                (snd
                                   (y
                                      (existT ValidDomainName
                                         (snd (split_string (projT1 r)))
                                         (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                      (split_string_ValidDomainName_length (projT1 r) n')
                                      (Ifopt Ifopt
                                             fst ce as m
                                             Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                  then Some (natToWord 17 (wordToNat m + 8))
                                                  else None Else None as m
                                       Then if Compare_dec.lt_dec
                                                 (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                                 (pow2 17)
                                            then
                                             Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                            else None Else None,
                                      snd ce))),
                             ((projT1 r, curPtr)
                              :: snd
                                   (snd
                                      (y
                                         (existT ValidDomainName
                                            (snd (split_string (projT1 r)))
                                            (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                         (split_string_ValidDomainName_length (projT1 r) n')
                                         (Ifopt Ifopt
                                                fst ce as m
                                                Then
                                                if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                                then Some (natToWord 17 (wordToNat m + 8))
                                                else None Else None as m
                                          Then if Compare_dec.lt_dec
                                                  (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                                  (pow2 17)
                                               then
                                                Some
                                                  (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                               else None Else None,
                                         snd ce))))%list)
                        Else snd
                               (y
                                  (existT ValidDomainName
                                     (snd (split_string (projT1 r)))
                                     (split_string_ValidDomainName (projT1 r) (projT2 r)))
                                  (split_string_ValidDomainName_length (projT1 r) n')
                                  (Ifopt Ifopt fst ce as m
                                         Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17)
                                              then Some (natToWord 17 (wordToNat m + 8))
                                              else None Else None as m
                                   Then if Compare_dec.lt_dec
                                             (wordToNat m + 8 * String.length (fst (split_string (projT1 r))))
                                             (pow2 17)
                                        then Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                                        else None Else None,
                                  snd ce))) end)).
    simpl.
    destruct (string_dec (projT1 r) ""); simpl.
    reflexivity.
    rewrite <- !build_aligned_ByteString_append.
    destruct (y (existT ValidDomainName (snd (split_string (projT1 r))) (split_string_ValidDomainName (projT1 r) (projT2 r)))
                (split_string_ValidDomainName_length (projT1 r) n)
                (Ifopt Ifopt fst ce0 as m
                       Then if Compare_dec.lt_dec (wordToNat m + 8) (pow2 17) then Some (natToWord 17 (wordToNat m + 8)) else None
                       Else None as m
                 Then if Compare_dec.lt_dec (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))) (pow2 17)
                      then Some (natToWord 17 (wordToNat m + 8 * String.length (fst (split_string (projT1 r)))))
                      else None Else None, snd ce0)); simpl.
    rewrite <- !build_aligned_ByteString_append.
    reflexivity.
    intros; apply functional_extensionality; intros.
    destruct (string_dec (projT1 x0) ""); simpl; try rewrite H; reflexivity.
    instantiate (2 := well_founded_string_length').
    instantiate (1 := d_OK).
    match goal with
      |- context [let (_,_) := ?z in _] =>
      replace z with
      (aligned_encode_DomainName d ce)
    end.
    destruct (aligned_encode_DomainName d ce); reflexivity.
    simpl. admit.
  Qed.

    Lemma optimize_align_encode_list
          {A}
          (A_OK : A -> Prop)
          (A_encode_Spec : A -> CacheEncode -> Comp (ByteString * CacheEncode))
          (A_encode_align :
             A
             ->  CacheEncode
             -> {n : _ & Vector.t (word 8) n} * CacheEncode)
          (A_encode_OK :
             forall a ce,
               A_OK a
               -> refine (A_encode_Spec a ce)
                      (ret (let (v', ce') := A_encode_align a ce in
                            (build_aligned_ByteString (projT2 v'), ce'))))
      : forall (As : list A)
               (ce : CacheEncode),
      (forall a, In a As -> A_OK a)
      -> refine (encode_list_Spec A_encode_Spec As ce)
               (let (v', ce') := (align_encode_list A_encode_align As ce) in
                ret (build_aligned_ByteString (projT2 v'), ce')).
  Proof.
    induction As; simpl; intros; simpl.
    - simpl.
      repeat f_equiv.
      eapply ByteString_f_equal.
      instantiate (1 := eq_refl _); reflexivity.
      instantiate (1 := eq_refl _); reflexivity.
    - unfold Bind2.
      rewrite A_encode_OK.
      simplify with monad laws.
      rewrite IHAs.
      destruct (A_encode_align a ce); simpl.
      destruct (align_encode_list A_encode_align As c);
        simplify with monad laws.
      simpl.
      rewrite <- build_aligned_ByteString_append.
      reflexivity.
      eauto.
      eauto.
  Qed.

  Lemma align_encode_sumtype_OK_inv'
        {m : nat}
        {types : t Type m}
        (A_OKs : SumType types -> Prop)
        (align_encoders :
                ilist (B := (fun T : Type => T -> @CacheEncode dns_list_cache -> ({n : _ & Vector.t (word 8) n} * (CacheEncode)))) types)
        (encoders :
           ilist (B := (fun T : Type => T -> @CacheEncode dns_list_cache -> Comp (ByteString * (CacheEncode)))) types)
        (encoders_OK : forall idx t (ce : CacheEncode),
            A_OKs (inj_SumType _ idx t)
            -> refine (ith encoders idx t ce)
                   (ret (build_aligned_ByteString (projT2 (fst (ith align_encoders idx t ce))),
                         snd (ith align_encoders idx t ce))))
    : forall (st : SumType types)
             (ce : CacheEncode),
      A_OKs st
      -> refine (encode_SumType_Spec types encoders st ce)
             (ret (build_aligned_ByteString (projT2 (fst (align_encode_sumtype align_encoders st ce))),
                   (snd (align_encode_sumtype align_encoders st ce)))).
  Proof.
    intros; unfold encode_SumType_Spec, align_encode_sumtype.
    rewrite encoders_OK; eauto.
    reflexivity.
    rewrite inj_SumType_proj_inverse; eauto.
  Qed.

  Corollary align_encode_sumtype_OK
        {m : nat}
        {types : t Type m}
        (A_OKs : SumType types -> Prop)
        (align_encoders :
                ilist (B := (fun T : Type => T -> @CacheEncode dns_list_cache -> ({n : _ & Vector.t (word 8) n} * (CacheEncode)))) types)
        (encoders :
           ilist (B := (fun T : Type => T -> @CacheEncode dns_list_cache -> Comp (ByteString * (CacheEncode)))) types)
        (encoders_OK : Iterate_Ensemble_BoundedIndex
                         (fun idx => forall t (ce : CacheEncode),
                              A_OKs (inj_SumType _ idx t)
                              -> refine (ith encoders idx t ce)
                                        (ret (build_aligned_ByteString (projT2 (fst (ith align_encoders idx t ce))),
                                              snd (ith align_encoders idx t ce)))))
    : forall (st : SumType types)
             (ce : CacheEncode),
      A_OKs st
      -> refine (encode_SumType_Spec types encoders st ce)
                (ret (build_aligned_ByteString (projT2 (fst (align_encode_sumtype align_encoders st ce))),
                      (snd (align_encode_sumtype align_encoders st ce)))).
  Proof.
    intros; eapply align_encode_sumtype_OK_inv'; intros.
    eapply Iterate_Ensemble_BoundedIndex_equiv in encoders_OK.
    apply encoders_OK; eauto.
    eauto.
  Qed.

  Arguments split1' : simpl never.
  Arguments split2' : simpl never.
  Arguments fin_eq_dec m !n !n' /.

  Lemma zeta_to_fst {A B C}
    : forall (ab : A * B) (k : A -> B -> C),
      (let (a, b) := ab in (k a b)) =
      k (fst ab) (snd ab).
  Proof.
    destruct ab; reflexivity.
  Qed.

  Lemma zeta_inside_ret {A B C}
    : forall (ab : A * B) (k : A -> B -> C),
      refine (let (a, b) := ab in ret (k a b))
             (ret (let (a, b) := ab in k a b)).
  Proof.
    destruct ab; reflexivity.
  Qed.

  Arguments addE : simpl never.

  Ltac pose_string_hyps :=
  fold_string_hyps;
   repeat
    match goal with
    | |- context [String ?R ?R'] =>
      let str := fresh "StringId" in
      assert True as H' by
          (clear;
           (cache_term (String R R') as str run (fun id => fold id in *; add id to stringCache));
           exact I); clear H'; fold_string_hyps
    | |- context [{| bindex := ?bindex'; indexb := ?indexb' |}] =>
      let str := fresh "BStringId" in
      cache_term ``(bindex') as str run fun id => fold id in *; add id to stringCache
    end.

  Create HintDb encoderCache.

  Ltac fold_encoders :=
    (repeat foreach [ encodeCache ] run (fun id => progress fold id in *)).
     
  Ltac cache_encoders :=
    repeat match goal with
           | |- context [icons (fun (a : ?z) => @?f a) _] =>
             let p' := fresh "encoder" in
             let H'' := fresh in
             assert True as H'' by
                   (clear;
                    (cache_term (fun a : z => f a) as p' run (fun id => fold id in *; add id to encodeCache)) ; exact I);
             fold_encoders; clear H''
           | |- context [align_encode_list (fun (a : ?z) => @?f a) _ _] =>
             let p' := fresh "encoder" in
             let H'' := fresh in
             assert True as H'' by
                   (clear;
                    (cache_term (fun a : z => f a) as p' run (fun id => fold id in *; add id to encodeCache)) ; exact I);
             fold_encoders; clear H''
           end.

  Arguments Vector.nth A !m !v' !p /.

  Definition refine_encode_packet
    : { b : _ & forall (p : packet)
                       (p_OK : DNS_Packet_OK p),
            refine (encode_packet_Spec p list_CacheEncode_empty)
                   (ret (b p)) }.
  Proof.
    unfold encode_packet_Spec.
    pose_string_hyps.
    eexists; intros.
    eapply refine_refineEquiv_Proper;
      [ unfold flip;
        repeat first
               [ etransitivity; [ apply refineEquiv_compose_compose with (transformer := transformer) | idtac ]
               | etransitivity; [ apply refineEquiv_compose_Done with (transformer := transformer) | idtac ]
               | apply refineEquiv_under_compose with (transformer := transformer) ];
        intros; higher_order_reflexivity
      | reflexivity | ].
    pose_string_hyps.
    etransitivity.
    eapply AlignedEncode2Char; eauto using addE_addE_plus.
    unfold encode_enum_Spec.
    rewrite CollapseEncodeWord; eauto using addE_addE_plus.
    rewrite CollapseEncodeWord; eauto using addE_addE_plus.
    rewrite CollapseEncodeWord; eauto using addE_addE_plus.
    rewrite CollapseEncodeWord; eauto using addE_addE_plus.
    eapply AlignedEncodeChar; eauto using addE_addE_plus.
    rewrite CollapseEncodeWord; eauto using addE_addE_plus.
    rewrite CollapseEncodeWord; eauto using addE_addE_plus.
    eapply AlignedEncodeChar; eauto using addE_addE_plus.
    eapply AlignedEncode2Nat; eauto using addE_addE_plus.
    eapply AlignedEncode2Nat; eauto using addE_addE_plus.
    eapply AlignedEncode2Nat; eauto using addE_addE_plus.
    eapply AlignedEncode2Nat; eauto using addE_addE_plus.
    unfold compose at 1, Bind2.
    rewrite align_encode_DomainName.
    simplify with monad laws.
    etransitivity.
    apply refine_under_bind_both.
    eapply AlignedEncode2Char; eauto using addE_addE_plus.
    eapply AlignedEncode2Char; eauto using addE_addE_plus.
    unfold compose, Bind2.
    etransitivity.
    apply refine_under_bind_both.
    pose proof (proj2 (proj2 (proj2 (proj2 p_OK)))).
    apply optimize_align_encode_list with (A_OK := resourceRecord_OK).
    unfold encode_resource_Spec; intros.
    unfold compose at 1, Bind2.
    rewrite align_encode_DomainName.
    simplify with monad laws.
    etransitivity.
    apply refine_under_bind_both.
    unfold encode_enum_Spec.
    eapply AlignedEncode2Char; eauto using addE_addE_plus.
    eapply AlignedEncode2Char; eauto using addE_addE_plus.
    eapply AlignedEncode32Char; eauto using addE_addE_plus.
    unfold encode_rdata_Spec.
    etransitivity.
    apply refine_under_bind_both.
    unfold resourceRecord_OK in H0.
    let types' := (eval unfold ResourceRecordTypeTypes in ResourceRecordTypeTypes)
      in ilist_of_evar
           (fun T : Type => T -> @CacheEncode dns_list_cache -> ({n : _ & Vector.t (word 8) n} * (CacheEncode)))
           types'
           ltac:(fun encoders' => eapply (@align_encode_sumtype_OK _ ResourceRecordTypeTypes _ encoders'));
           [simpl; intros; repeat (apply Build_prim_and; intros); try exact I |
           ].
    5 : instantiate (1 := fun a => ith
      (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
             (icons (B := fun T => T -> Prop) (fun _ : Memory.W => True)
                    (icons (B := fun T => T -> Prop) (fun a : DomainName => ValidDomainName a)
                           (icons (B := fun T => T -> Prop) (fun a : SOA_RDATA =>
                                                               (True /\ ValidDomainName a!"contact_email") /\ ValidDomainName a!"sourcehost") inil))))
      (SumType_index
         (DomainName
            :: (Memory.W : Type)
            :: DomainName
            :: [SOA_RDATA])
         a)
      (SumType_proj
         (DomainName
            :: (Memory.W : Type)
            :: DomainName
            :: [SOA_RDATA])
         a)); apply H0.
    { unfold encode_CNAME_Spec.
      etransitivity.
      apply (@AlignedEncode2UnusedChar dns_list_cache).
      etransitivity.
      apply refine_under_bind_both.
      apply align_encode_DomainName.
      apply H1.
      intros; unfold Bind2; simplify with monad laws.
      simpl; higher_order_reflexivity.
      simplify with monad laws.
      simpl.
      replace ByteString_id
      with (build_aligned_ByteString (Vector.nil _)).
      erewrite <- build_aligned_ByteString_append.
      reflexivity.
      eapply ByteString_f_equal;
        instantiate (1 := eq_refl _); reflexivity.
      simpl in H1.
      instantiate (1 := fun t ce0 => (existT _ _ _, _)).
      simpl; reflexivity.
    }
    { unfold encode_A_Spec.
      etransitivity.
      apply (@AlignedEncode2UnusedChar dns_list_cache).
      apply (@AlignedEncode32Char dns_list_cache); auto using addE_addE_plus.
      replace transform_id
      with (build_aligned_ByteString (Vector.nil _)).
      reflexivity.
      eapply ByteString_f_equal;
        instantiate (1 := eq_refl _); reflexivity.
      instantiate (1 := fun t ce0 => (existT _ _ _, _)).
      simpl; reflexivity.
    }
    { unfold encode_NS_Spec.
      etransitivity.
      apply (@AlignedEncode2UnusedChar dns_list_cache).
      etransitivity.
      apply refine_under_bind_both.
      apply align_encode_DomainName.
      apply H1.
      intros; unfold Bind2; simplify with monad laws.
      simpl; higher_order_reflexivity.
      simplify with monad laws.
      simpl.
      replace ByteString_id
      with (build_aligned_ByteString (Vector.nil _)).
      erewrite <- build_aligned_ByteString_append.
      reflexivity.
      eapply ByteString_f_equal;
        instantiate (1 := eq_refl _); reflexivity.
      instantiate (1 := fun t ce0 => (existT _ _ _, _)).
      simpl; reflexivity.
    }
    { unfold encode_SOA_RDATA_Spec.
      pose_string_hyps.
      etransitivity.
      apply (@AlignedEncode2UnusedChar dns_list_cache).
      etransitivity.
      apply refine_under_bind_both.
      apply align_encode_DomainName.
      apply H1.
      intros; unfold Bind2.
      etransitivity.
      apply refine_under_bind_both.
      etransitivity.
      apply refine_under_bind_both.
      apply align_encode_DomainName.
      apply H1.
      intros; unfold Bind2.
      apply refine_under_bind_both.
      apply (@AlignedEncode32Char dns_list_cache); auto using addE_addE_plus.
      apply (@AlignedEncode32Char dns_list_cache); auto using addE_addE_plus.
      apply (@AlignedEncode32Char dns_list_cache); auto using addE_addE_plus.
      apply (@AlignedEncode32Char dns_list_cache); auto using addE_addE_plus.
      apply (@AlignedEncode32Char dns_list_cache); auto using addE_addE_plus.
      replace transform_id
      with (build_aligned_ByteString (Vector.nil _)).
      reflexivity.
      eapply ByteString_f_equal;
        instantiate (1 := eq_refl _); reflexivity.
      intros; higher_order_reflexivity.
      simpl.
      simplify with monad laws.
      reflexivity.
      intros; higher_order_reflexivity.
      simplify with monad laws.
      higher_order_reflexivity.
      simplify with monad laws.
      simpl.
      rewrite <- !build_aligned_ByteString_append.
      reflexivity.
      instantiate (1 := fun t ce0 => (existT _ _ _, _)).
      simpl; reflexivity.
    }
    intros.
    intros; unfold Bind2; simplify with monad laws.
    simpl; higher_order_reflexivity.

       cache_encoders.
       simplify with monad laws.
       simpl.
       replace ByteString_id
       with (build_aligned_ByteString (Vector.nil _)).
       rewrite <- build_aligned_ByteString_append.
       reflexivity.
       eapply ByteString_f_equal;
         instantiate (1 := eq_refl _); reflexivity.
       intros; higher_order_reflexivity.
       match goal with
         |- context [ @align_encode_sumtype ?cache ?m ?types ?encoders ?p ?ce] =>
         pose (@align_encode_sumtype cache m types encoders) as H'; fold H'
       end.

       simpl.
       simplify with monad laws.
       simpl.
       rewrite <- build_aligned_ByteString_append.
       instantiate (1 := fun t ce0 =>
                           (existT _ _ _, _)).
       simpl.
       reflexivity.
       apply H0.
       apply H.
       intros; unfold Bind2; simplify with monad laws.
       simpl; higher_order_reflexivity.
       cache_encoders.
       simpl.
       Time match goal with
              |- context [let (v, c) := ?z in ret (@?b v c)] =>
              rewrite (zeta_inside_ret z b)
            end.
       simplify with monad laws.
       replace ByteString_id
       with (build_aligned_ByteString (Vector.nil _)).
       Time match goal with
              |- context [let (v, c) := ?z in (@?b v c)] =>
              pose proof (zeta_to_fst z b)
            end.
       simpl in H.
       simpl; rewrite H; clear H.
       simpl; rewrite <- build_aligned_ByteString_append.
       reflexivity.
       eapply ByteString_f_equal;
         instantiate (1 := eq_refl _); reflexivity.
       intros; higher_order_reflexivity.
       simplify with monad laws.
       simpl; rewrite <- build_aligned_ByteString_append.
       rewrite !addE_addE_plus.
       simpl.
       reflexivity.
       apply p_OK.
       simpl.
       higher_order_reflexivity.
       Time Defined.

Definition refine_encode_packet_Impl
             (p : packet)
  := Eval simpl in (projT1 refine_encode_packet p).

Lemma refine_encode_packet_Impl_OK
  : forall p (p_OK : DNS_Packet_OK p),
    refine (encode_packet_Spec p list_CacheEncode_empty)
           (ret (refine_encode_packet_Impl p)).
Proof.
  intros; apply (projT2 refine_encode_packet); eauto.
Qed.
  
  Definition ByteAlignedCorrectDecoderFor {A} {cache : Cache}
             Invariant FormatSpec :=
    { decodePlusCacheInv |
      exists P_inv,
      (cache_inv_Property (snd decodePlusCacheInv) P_inv
       -> encode_decode_correct_f (A := A) cache transformer Invariant (fun _ _ => True)
                                  FormatSpec
                                  (fst decodePlusCacheInv)
                                  (snd decodePlusCacheInv))
      /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.

  Arguments split1' : simpl never.
  Arguments split2' : simpl never.
  Arguments weq : simpl never.
  Arguments word_indexed : simpl never.

  Definition packet_decoder
    : CorrectDecoderFor DNS_Packet_OK encode_packet_Spec.
  Proof.
    synthesize_decoder_ext transformer
                           decode_DNS_rules
                           decompose_parsed_data
                           solve_GoodCache_inv.
    unfold resourceRecord_OK.
    clear; intros.
    apply (proj2 H).
    simpl; intros;
      repeat (try rewrite !DecodeBindOpt2_assoc;
              try rewrite !Bool.andb_true_r;
              try rewrite !Bool.andb_true_l;
              try rewrite !optimize_if_bind2;
              try rewrite !optimize_if_bind2_bool).
    first [ apply DecodeBindOpt2_under_bind; simpl; intros
          | eapply optimize_under_if_bool; simpl; intros
          | eapply optimize_under_if; simpl; intros].
    unfold decode_enum at 1.
    repeat (try rewrite !DecodeBindOpt2_assoc;
            try rewrite !Bool.andb_true_r;
            try rewrite !Bool.andb_true_l;
            try rewrite !optimize_if_bind2;
            try rewrite !optimize_if_bind2_bool).
    etransitivity.
    first [ apply DecodeBindOpt2_under_bind; simpl; intros
          | eapply optimize_under_if_bool; simpl; intros
          | eapply optimize_under_if; simpl; intros].
    rewrite !DecodeBindOpt2_assoc.
    first [ apply DecodeBindOpt2_under_bind; simpl; intros
          | eapply optimize_under_if_bool; simpl; intros
          | eapply optimize_under_if; simpl; intros].
    rewrite (If_Opt_Then_Else_DecodeBindOpt_swap (cache := dns_list_cache)).
    first [ apply DecodeBindOpt2_under_bind; simpl; intros
          | eapply optimize_under_if_bool; simpl; intros
          | eapply optimize_under_if; simpl; intros].
    rewrite (If_Opt_Then_Else_DecodeBindOpt_swap (cache := dns_list_cache)).
    first [ apply DecodeBindOpt2_under_bind; simpl; intros
          | eapply optimize_under_if_bool; simpl; intros
          | eapply optimize_under_if; simpl; intros].
    rewrite (If_Opt_Then_Else_DecodeBindOpt_swap (cache := dns_list_cache)).
    first [ apply DecodeBindOpt2_under_bind; simpl; intros
          | eapply optimize_under_if_bool; simpl; intros
          | eapply optimize_under_if; simpl; intros].
    rewrite (If_Opt_Then_Else_DecodeBindOpt_swap (cache := dns_list_cache)).
    first [ apply DecodeBindOpt2_under_bind; simpl; intros
          | eapply optimize_under_if_bool; simpl; intros
          | eapply optimize_under_if; simpl; intros].
    rewrite (If_Opt_Then_Else_DecodeBindOpt_swap (cache := dns_list_cache)).
    first [ apply DecodeBindOpt2_under_bind; simpl; intros
          | eapply optimize_under_if_bool; simpl; intros
          | eapply optimize_under_if; simpl; intros].
    etransitivity.
    first [ apply DecodeBindOpt2_under_bind; simpl; intros
          | eapply optimize_under_if_bool; simpl; intros
          | eapply optimize_under_if; simpl; intros].
    rewrite (If_Then_Else_Bind (cache := dns_list_cache)).
    unfold decode_enum at 1.
    repeat (try rewrite !DecodeBindOpt2_assoc;
            try rewrite !Bool.andb_true_r;
            try rewrite !Bool.andb_true_l;
            try rewrite !optimize_if_bind2;
            try rewrite !optimize_if_bind2_bool).
    higher_order_reflexivity.
    set_refine_evar.
    rewrite (If_Opt_Then_Else_DecodeBindOpt_swap (cache := dns_list_cache)).
    unfold H; higher_order_reflexivity.
    collapse_word addD_addD_plus.
    collapse_word addD_addD_plus.
    collapse_word addD_addD_plus.
    collapse_word addD_addD_plus.
    first [ apply DecodeBindOpt2_under_bind; simpl; intros
          | eapply optimize_under_if_bool; simpl; intros
          | eapply optimize_under_if; simpl; intros].
    collapse_word addD_addD_plus.
    collapse_word addD_addD_plus.
    simpl.
    higher_order_reflexivity.
  Defined.

  Definition packetDecoderImpl
    := Eval simpl in (projT1 packet_decoder).

  Arguments Guarded_Vector_split : simpl never.

  Arguments addD : simpl never.

  Lemma rec_aligned_decode_DomainName_OK
    : forall (x : nat) (x0 : t (word 8) x),
      (le 1 x) ->
      ~ (lt (x - 1) (wordToNat (Vector.hd (Guarded_Vector_split 1 x x0))))%nat ->
      (lt (x - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 x x0))) x)%nat.
  Proof.
    clear; intros; omega.
  Qed.

  Definition byte_aligned_decode_DomainName {sz}
             (b : Vector.t (word 8) sz)
             (cd : CacheDecode) :=
    let body :=
        fun n0
            (rec' : forall x : nat,
                (lt x n0)%nat ->
                t Core.char x -> CacheDecode -> option (RRecordTypes.DomainName * {n1 : nat & t Core.char n1} * CacheDecode))
            b cd =>
          match Compare_dec.le_dec 1 n0 with
          | left e1 =>
            match wlt_dec (natToWord 8 191) (Vector.hd (Guarded_Vector_split 1 n0 b)) with
            | left e =>
              if match n0 - 1 with
                 | 0 => false
                 | S _ => true
                 end
              then
                match
                  association_list_find_first (snd cd)
                                              (exist (wlt (natToWord 8 191)) (Vector.hd (Guarded_Vector_split 1 n0 b)) e,
                                               Vector.hd (Guarded_Vector_split 1 (n0 - 1) (Vector.tl (Guarded_Vector_split 1 n0 b))))
                with
                | Some ""%string => None
                | Some (String _ _ as domain) =>
                  Some
                    (domain,
                     existT (fun n => Vector.t (word 8) n) _ (Vector.tl (Guarded_Vector_split 1 (n0 - 1) (Vector.tl (Guarded_Vector_split 1 n0 b)))),
                     addD (addD cd 8) 8)
                | None => None
                end
              else None
            | right n1 =>
              if bool_of_sumbool (wlt_dec (Vector.hd (Guarded_Vector_split 1 n0 b)) (natToWord 8 64))
              then
                match weq (Vector.hd (Guarded_Vector_split 1 n0 b)) (wzero 8) with
                | in_left => Some (""%string, existT (fun n => Vector.t (word 8) n) _ (Vector.tl (Guarded_Vector_split 1 n0 b)), addD cd 8)
                | right n2 =>
                  (fun a_neq0 : Vector.hd (Guarded_Vector_split 1 n0 b) <> wzero 8 =>
                     match Compare_dec.lt_dec (n0 - 1) (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b))) with
                     | left e => (fun _ : lt (n0 - 1) (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))%nat => None) e
                     | right n3 =>
                       (fun a_neq1 : ~ lt (n0 - 1) (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))%nat =>
                          Ifopt index 0 "."
                                (BytesToString
                                   (fst
                                      (Vector_split (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                    (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                    (Guarded_Vector_split
                                                       (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                       (n0 - 1) (Vector.tl (Guarded_Vector_split 1 n0 b)))))) as a8 Then
                                                                                                                    (fun _ : nat => None) a8
                                                                                                                    Else (`(d, s, c) <- rec' (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                           (rec_aligned_decode_DomainName_OK n0 b e1 n3)
                                                                                                                           (snd
                                                                                                                              (Vector_split
                                                                                                                                 (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                 (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                 (Guarded_Vector_split
                                                                                                                                    (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                    (n0 - 1)
                                                                                                                                    (Vector.tl (Guarded_Vector_split 1 n0 b)))))
                                                                                                                           (addD (addD cd 8) (8 * wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b))));
                                                                                                                            If string_dec d ""
                                                                                                                               Then Some
                                                                                                                               (BytesToString
                                                                                                                                  (fst
                                                                                                                                     (Vector_split
                                                                                                                                        (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                        (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                        (Guarded_Vector_split
                                                                                                                                           (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                           (n0 - 1)
                                                                                                                                           (Vector.tl (Guarded_Vector_split 1 n0 b))))),
                                                                                                                                s,
                                                                                                                                Ifopt Ifopt fst cd as m Then Some (Nat2pointerT (wordToNat (wtl (wtl (wtl m))))) Else None
                                                                                                                                   as curPtr
                                                                                                                                        Then (fst c,
                                                                                                                                              ((curPtr,
                                                                                                                                                BytesToString
                                                                                                                                                  (fst
                                                                                                                                                     (Vector_split
                                                                                                                                                        (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                        (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                        (Guarded_Vector_split
                                                                                                                                                           (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                           (n0 - 1)
                                                                                                                                                           (Vector.tl (Guarded_Vector_split 1 n0 b)))))) ::
                                                                                                                                                                                                         snd c)%list) Else c)
                                                                                                                               Else Some
                                                                                                                               ((BytesToString
                                                                                                                                   (fst
                                                                                                                                      (Vector_split
                                                                                                                                         (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                         (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                         (Guarded_Vector_split
                                                                                                                                            (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                            (n0 - 1)
                                                                                                                                            (Vector.tl (Guarded_Vector_split 1 n0 b))))) ++
                                                                                                                                   String "." d)%string,
                                                                                                                                s,
                                                                                                                                Ifopt Ifopt fst cd as m Then Some (Nat2pointerT (wordToNat (wtl (wtl (wtl m))))) Else None
                                                                                                                                   as curPtr
                                                                                                                                        Then (fst c,
                                                                                                                                              ((curPtr,
                                                                                                                                                (BytesToString
                                                                                                                                                   (fst
                                                                                                                                                      (Vector_split
                                                                                                                                                         (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                         (n0 - 1 - wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                         (Guarded_Vector_split
                                                                                                                                                            (wordToNat (Vector.hd (Guarded_Vector_split 1 n0 b)))
                                                                                                                                                            (n0 - 1)
                                                                                                                                                            (Vector.tl (Guarded_Vector_split 1 n0 b))))) ++
                                                                                                                                                   String "." d)%string) ::
                                                                                                                                                                         snd c)%list) Else c))) n3
                     end) n2
                end
              else None
            end
          | right e => None
          end in
    Fix Wf_nat.lt_wf (fun m : nat => Vector.t (word 8) m -> CacheDecode -> option (_ * { n : _ & Vector.t _ n} * CacheDecode)) body sz b cd.

  Lemma byte_align_decode_DomainName {sz}
    : forall (b : Vector.t (word 8) sz) cd,
      decode_DomainName(build_aligned_ByteString b) cd =
      Ifopt byte_aligned_decode_DomainName b cd as p Then
                                                     (match p with
                                                      | (a, b', cd') => Some (a, build_aligned_ByteString (projT2 b'), cd')
                                                      end)
                                                     Else None.
  Proof.
    unfold If_Opt_Then_Else,decode_DomainName,
    byte_aligned_decode_DomainName; simpl; intros.
    eapply (@optimize_Fix dns_list_cache).
    Focus 3.
    etransitivity.
    simpl; intros.
    erewrite ByteAlign_Decode_w_Measure_le with (m := 1)
                                                  (dec_a' := Vector.hd)
                                                  (f := fun cd => addD cd 8);
      try (intros; unfold decode_word; rewrite aligned_decode_char_eq;
           reflexivity).
    Focus 2.
    intros; assert (n = 0) by omega; subst.
    revert b1; clear.
    apply case0; reflexivity.
    set_refine_evar.
    etransitivity;
      [eapply (@If_sumbool_Then_Else_DecodeBindOpt _ _ _ _ _ dns_list_cache) | ]; simpl.
    apply optimize_under_match; intros.
    simpl.

    apply optimize_under_match; intros.
    simpl.
    erewrite ByteAlign_Decode_w_Measure_le with (m := 1)
                                                  (dec_a' := Vector.hd)
                                                  (f := fun cd => addD cd 8);
      try (intros; unfold decode_word; rewrite aligned_decode_char_eq;
           reflexivity).
    Focus 2.
    intros; assert (n - 1 = 0) by omega.
    revert b1; rewrite H3; clear.
    apply case0; reflexivity.
    set_refine_evar.
    simpl.
    etransitivity;
      [eapply (@If_sumbool_Then_Else_DecodeBindOpt _ _ _ _ _ dns_list_cache) | ]; simpl.
    apply optimize_under_match; intros.
    simpl.
    reflexivity.
    simpl.
    reflexivity.
    eapply optimize_under_if_bool.
    apply optimize_under_match.
    simpl.
    intros; higher_order_reflexivity.
    intros.
    simpl.
    2: reflexivity.
    2: reflexivity.
    2: simpl.
    erewrite ByteAlign_Decode_w_Measure_lt with (m := (wordToNat (Vector.hd (Guarded_Vector_split 1 n b0)))) (m_OK := n_eq_0_lt _ a_neq0).
    Focus 3.

    intros.
    rewrite decode_string_aligned_ByteString.
    repeat f_equal.
    higher_order_reflexivity.
    higher_order_reflexivity.
    apply addD_addD_plus.
    etransitivity;
      [eapply (@If_sumbool_Then_Else_DecodeBindOpt _ _ _ _ _ dns_list_cache) | ]; simpl.
    etransitivity.
    apply optimize_under_match; intros.
    subst_refine_evar; simpl; higher_order_reflexivity.
    subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
    subst_refine_evar; simpl; higher_order_reflexivity.
    apply optimize_under_match; intros.
    simpl; higher_order_reflexivity.
    unfold LetIn.
    apply optimize_under_if_opt.
    intros; higher_order_reflexivity.
    eapply optimize_under_DecodeBindOpt2_both.
    unfold lt_B_Guarded_Vector_split; simpl.
    intros; apply H with (b_lt' := rec_aligned_decode_DomainName_OK _ _ a_eq a_neq1).
    apply H2.
    intros; eapply H0; eauto.
    intros; simpl.
    higher_order_reflexivity.
    intros; eauto using decode_string_aligned_ByteString_overflow.
    destruct n; eauto.
    destruct (wlt_dec (natToWord 8 191) (Vector.hd (Guarded_Vector_split 1 (S n) b0)));
      eauto.
    find_if_inside; eauto.
    simpl.
    find_if_inside; eauto.
    destruct n; try omega; simpl; eauto.
    match goal with
      |- match ?z with _ => _ end = match match ?z' with _ => _ end with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    clear; induction s; simpl; eauto.
    destruct n; simpl; auto; try omega.
    match goal with
      |- match ?z with _ => _ end = match match ?z' with _ => _ end with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    match goal with
      |- match ?z with _ => _ end = match match ?z' with _ => _ end with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    find_if_inside; simpl; eauto.
    match goal with
      |- match ?z with _ => _ end = match match ?z' with _ => _ end with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    match goal with
      |- (Ifopt ?c as a Then _ Else _) = _ => destruct c as [ ? | ]; simpl; eauto
    end.
    match goal with
      |- DecodeBindOpt2 ?z _ = _ => destruct z as [ [ [? ?] ?] | ]; simpl; eauto
    end.
    find_if_inside; simpl; eauto.
    simpl; intros; apply functional_extensionality; intros.
    f_equal.
    simpl; intros; repeat (apply functional_extensionality; intros).
    destruct (wlt_dec (natToWord 8 191) x1).
    reflexivity.
    destruct (wlt_dec x1 (natToWord 8 64)); simpl.
    destruct (weq x1 (wzero 8)); eauto.
    match goal with
      |- DecodeBindOpt2 ?z _ = _ => destruct z as [ [ [? ?] ?] | ]; simpl; eauto
    end.
    match goal with
      |- (Ifopt ?c as a Then _ Else _) = _ => destruct c as [ ? | ]; simpl; eauto
    end.
    rewrite H.
    reflexivity.
    eauto.
    simpl; intros; apply functional_extensionality; intros.
    f_equal.
    simpl; intros; repeat (apply functional_extensionality; intros).
    match goal with
      |- match ?z with _ => _ end = match ?z' with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    match goal with
      |- match ?z with _ => _ end = match ?z' with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    find_if_inside; simpl.
    find_if_inside; simpl; eauto.
    match goal with
      |- match ?z with _ => _ end = match ?z' with _ => _ end =>
      replace z' with z by reflexivity; destruct z; eauto
    end.
    match goal with
      |- (Ifopt ?c as a Then _ Else _) = _ => destruct c as [ ? | ]; simpl; eauto
    end.
    rewrite H; reflexivity.
    eauto.
  Qed.

  Arguments Core.append_word : simpl never.
  Arguments Vector_split : simpl never.
  Arguments NPeano.leb : simpl never.

  Definition If_Opt_Then_Else_map
             {A B B'} :
    forall (f : option B -> B')
           (a_opt : option A)
           (t : A -> option B)
           c,
      f (Ifopt a_opt as a Then t a Else c) =
      Ifopt a_opt as a Then f (t a) Else (f c).
  Proof.
    destruct a_opt as [ a' | ]; reflexivity.
  Qed.

  Ltac rewrite_DecodeOpt2_fmap :=
    set_refine_evar;
    progress rewrite ?BindOpt_map, ?DecodeOpt2_fmap_if,
    ?DecodeOpt2_fmap_if_bool;
    subst_refine_evar.

  Lemma Ifopt_Ifopt {A A' B}
    : forall (a_opt : option A)
             (t : A -> option A')
             (e : option A')
             (t' : A' -> B)
             (e' :  B),
      Ifopt (Ifopt a_opt as a Then t a Else e) as a' Then t' a' Else e' =
      Ifopt a_opt as a Then (Ifopt (t a) as a' Then t' a' Else e') Else (Ifopt e as a' Then t' a' Else e').
  Proof.
    destruct a_opt; simpl; reflexivity.
  Qed.

  Definition ByteAligned_packetDecoderImpl {A}
             (f : _ -> A)
             n
    : {impl : _ & forall (v : Vector.t _ (12 + n)),
           f (fst packetDecoderImpl (build_aligned_ByteString v) (Some (wzero 17), @nil (pointerT * string))) =
           impl v (Some (wzero 17) , @nil (pointerT * string))%list}.
  Proof.
    eexists _; intros.
    etransitivity.
    set_refine_evar; simpl.
    unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
    rewrite (@AlignedDecode2Char dns_list_cache).
    subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
    unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
    rewrite (@AlignedDecodeChar dns_list_cache ).
    rewrite !nth_Vector_split.
    subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
    unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
    rewrite (@AlignedDecodeChar dns_list_cache ).
    rewrite !nth_Vector_split.
    subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
    unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
    rewrite Ifopt_Ifopt; simpl.
    subst_refine_evar; eapply optimize_under_if_opt; simpl; intros.
    unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
    rewrite Ifopt_Ifopt; simpl.
    eapply optimize_under_if_opt; simpl; intros.
    rewrite BindOpt_map_if.
    subst_refine_evar; eapply optimize_under_if; simpl; intros.
    unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
    rewrite (@AlignedDecode2Nat dns_list_cache).
    repeat first  [rewrite <- !Vector_nth_tl
                  | rewrite !nth_Vector_split].
    subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
    rewrite BindOpt_map_if; unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
    subst_refine_evar; eapply optimize_under_if; simpl; intros.
    rewrite (@AlignedDecode2Nat dns_list_cache).
    subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
    unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
    repeat first  [rewrite <- !Vector_nth_tl
                  | rewrite !nth_Vector_split
                  | rewrite Vector_split_merge,
                    <- Eqdep_dec.eq_rect_eq_dec;
                    eauto using Peano_dec.eq_nat_dec].
    rewrite (@AlignedDecode2Nat dns_list_cache).
    repeat first  [rewrite <- !Vector_nth_tl
                  | rewrite !nth_Vector_split
                  | rewrite Vector_split_merge,
                    <- Eqdep_dec.eq_rect_eq_dec;
                    eauto using Peano_dec.eq_nat_dec].
    subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
    unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
    rewrite (@AlignedDecode2Nat dns_list_cache).
    repeat first  [rewrite <- !Vector_nth_tl
                  | rewrite !nth_Vector_split
                  | rewrite Vector_split_merge,
                    <- Eqdep_dec.eq_rect_eq_dec;
                    eauto using Peano_dec.eq_nat_dec].
    subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
    rewrite !DecodeBindOpt2_assoc.
    repeat first  [rewrite <- !Vector_nth_tl
                  | rewrite !nth_Vector_split
                  | rewrite Vector_split_merge,
                    <- Eqdep_dec.eq_rect_eq_dec;
                    eauto using Peano_dec.eq_nat_dec].
    simpl.
    unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
    rewrite byte_align_decode_DomainName.
    rewrite Ifopt_Ifopt; simpl.
    subst_refine_evar; eapply optimize_under_if_opt; simpl; intros.
    destruct a8 as [ [? [ ? ?] ] ? ]; simpl.
    rewrite DecodeBindOpt2_assoc.
    etransitivity.
    unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.

  Lemma optimize_Guarded_Decode {sz} {C} n
    : forall (a_opt : ByteString -> C)
             (a_opt' : ByteString -> C) v c,
      (~ (n <= sz)%nat
       -> a_opt (build_aligned_ByteString v) = c)
      -> (le n sz -> a_opt  (build_aligned_ByteString (Guarded_Vector_split n sz v))
                     = a_opt'
                         (build_aligned_ByteString (Guarded_Vector_split n sz v)))
      -> a_opt (build_aligned_ByteString v) =
         If NPeano.leb n sz Then
            a_opt' (build_aligned_ByteString (Guarded_Vector_split n sz v))
            Else c.
  Proof.
    intros; destruct (NPeano.leb n sz) eqn: ?.
    - apply NPeano.leb_le in Heqb.
      rewrite <- H0.
      simpl; rewrite <- build_aligned_ByteString_eq_split'; eauto.
      eauto.
    - rewrite H; simpl; eauto.
      intro.
      rewrite <- NPeano.leb_le in H1; congruence.
  Qed.

    match goal with
      |- ?b = _ =>
      let b' := (eval pattern (build_aligned_ByteString t) in b) in
      let b' := match b' with ?f _ => f end in
      eapply (@optimize_Guarded_Decode x _ 4 b')
    end.
    { intros.
      unfold decode_enum.
      unfold DecodeBindOpt2 at 1, BindOpt.
      rewrite Ifopt_Ifopt.
      destruct (Compare_dec.lt_dec x 2).
      pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
        simpl in H'; rewrite H'; try reflexivity; auto.
      destruct x as [ | [ | [ | ?] ] ]; try omega.
      rewrite AlignedDecode2Char; unfold LetIn; simpl.
      rewrite Ifopt_Ifopt.
      match goal with
        |- If_Opt_Then_Else ?b _ _ = _ => destruct b; reflexivity
      end.
      rewrite AlignedDecode2Char; unfold LetIn; simpl.
      rewrite Ifopt_Ifopt.
      simpl.
      match goal with
        |- If_Opt_Then_Else ?b _ _ = _ => destruct b; simpl; try eauto
      end.
      repeat rewrite DecodeBindOpt2_assoc.
      pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
        simpl in H'; rewrite H'; try reflexivity; auto.
      omega.
    }
    { intros; unfold decode_enum.
      etransitivity.
      set_refine_evar; repeat rewrite BindOpt_assoc.
      unfold DecodeBindOpt2 at 1, BindOpt.
      rewrite Ifopt_Ifopt.
      rewrite (AlignedDecode2Char (Guarded_Vector_split 4 x t)).
      subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
      rewrite Ifopt_Ifopt.
      simpl.
      subst_refine_evar;
        eapply optimize_under_if_opt; simpl; intros;
          set_refine_evar.
      repeat rewrite DecodeBindOpt2_assoc.
      unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
      rewrite (@AlignedDecode2Char dns_list_cache ).
      subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
      rewrite (@If_Opt_Then_Else_DecodeBindOpt _ dns_list_cache); simpl.
      rewrite If_Opt_Then_Else_map.
      subst_refine_evar;
        eapply optimize_under_if_opt; simpl; intros;
          set_refine_evar.
      unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
      erewrite optimize_align_decode_list.
      rewrite Ifopt_Ifopt.
      simpl.
      etransitivity.
      eapply optimize_under_if_opt; simpl; intros.
      rewrite BindOpt_map_if_bool.
      higher_order_reflexivity.
      higher_order_reflexivity.
      higher_order_reflexivity.
      etransitivity.
      set_refine_evar.
      clear H0.
      rewrite byte_align_decode_DomainName.
      etransitivity;
        [match goal with
           |- DecodeBindOpt2 (If_Opt_Then_Else ?a_opt ?t ?e) ?k = _ =>
           pose proof (If_Opt_Then_Else_DecodeBindOpt (cache := dns_list_cache) a_opt t e k) as H'; apply H'; clear H'
         end | ].
      subst_evars.
      eapply optimize_under_if_opt; simpl; intros.
      destruct a12 as [ [? [ ? ?] ] ? ]; simpl.
      rewrite DecodeBindOpt2_assoc.
      simpl.
      etransitivity.
      match goal with
        |- ?b = _ =>
        let b' := (eval pattern (build_aligned_ByteString t0) in b) in
        let b' := match b' with ?f _ => f end in
        eapply (@AlignedDecoders.optimize_Guarded_Decode x0 _ 8 b')
      end.
      { intros.
        destruct x0 as [ | [ | x0] ].
        pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
          simpl in H'; rewrite H'; try reflexivity; auto.
        pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
          simpl in H'; rewrite H'; try reflexivity; auto.
        etransitivity; set_refine_evar.
        unfold DecodeBindOpt2, BindOpt at 1; rewrite (@AlignedDecode2Char dns_list_cache ).
        subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
        rewrite (If_Opt_Then_Else_BindOpt).
        subst_refine_evar; eapply optimize_under_if_opt; simpl; intros; set_refine_evar.
        subst_refine_evar.
        instantiate (1 := fun _ => None).
        rewrite BindOpt_assoc.
        destruct x0 as [ | [ | x0] ].
        pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
          simpl in H'; rewrite H'; try higher_order_reflexivity; auto.
        pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
          simpl in H'; rewrite H'; try higher_order_reflexivity; auto.
        unfold BindOpt at 1; rewrite (@AlignedDecode2Char dns_list_cache ).
        etransitivity.
        subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
        rewrite (If_Opt_Then_Else_BindOpt).
        subst_evars.
        eapply optimize_under_if_opt; simpl; intros; set_refine_evar.
        subst_refine_evar.
        instantiate (1 := fun _ => None).
        destruct x0 as [ | [| [ | [ | x0] ] ] ]; try omega.
        pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
          simpl in H'; rewrite H'; try reflexivity; auto.
        pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
          simpl in H'; rewrite H'; try reflexivity; auto.
        pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
          simpl in H'; rewrite H'; try reflexivity; auto.
        pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
          simpl in H'; rewrite H'; try reflexivity; auto.
        subst_evars; reflexivity.
        unfold LetIn; simpl; match goal with
                               |- Ifopt ?b as _ Then _ Else _ = _ =>
                               destruct b; reflexivity
                             end.
        subst_evars; reflexivity.
        unfold LetIn; simpl; match goal with
                               |- Ifopt ?b as _ Then _ Else _ = _ =>
                               destruct b; reflexivity
                             end.
      }
      intros; etransitivity.
      simpl; unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode2Char dns_list_cache ).
      subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
      etransitivity;
        [match goal with
           |- DecodeBindOpt2 (If_Opt_Then_Else ?a_opt ?t ?e) ?k = _ =>
           pose proof (If_Opt_Then_Else_DecodeBindOpt (cache := dns_list_cache) a_opt t e k) as H'; apply H'; clear H'
         end | ].
      simpl.
      subst_refine_evar;
        eapply optimize_under_if_opt; simpl; intros;
          set_refine_evar.
      repeat rewrite DecodeBindOpt2_assoc.
      unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode2Char dns_list_cache ).
      subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
      etransitivity;
        [match goal with
           |- DecodeBindOpt2 (If_Opt_Then_Else ?a_opt ?t ?e) ?k = _ =>
           pose proof (If_Opt_Then_Else_DecodeBindOpt (cache := dns_list_cache) a_opt t e k) as H'; apply H'; clear H'
         end | ].
      simpl.
      subst_refine_evar;
        eapply optimize_under_if_opt; simpl; intros;
          set_refine_evar.
      repeat rewrite DecodeBindOpt2_assoc.
      unfold DecodeBindOpt2 at 1, BindOpt;rewrite (@AlignedDecode4Char dns_list_cache).
      repeat (rewrite Vector_split_merge,
              <- Eqdep_dec.eq_rect_eq_dec;
              eauto using Peano_dec.eq_nat_dec ).
      subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
      let types' := (eval unfold ResourceRecordTypeTypes in ResourceRecordTypeTypes)
      in ilist_of_evar
           (fun T : Type => forall n,
                Vector.t (word 8) n
                -> CacheDecode
                -> option (T * {n : _ & Vector.t (word 8) n} * CacheDecode))
           types'
           ltac:(fun decoders' => rewrite (@align_decode_sumtype_OK dns_list_cache _ ResourceRecordTypeTypes decoders'));
           [ | simpl; intros; repeat (apply Build_prim_and; intros); try exact I].
      set_refine_evar.
      rewrite (If_Opt_Then_Else_DecodeBindOpt (cache := dns_list_cache)).
      simpl.
      subst_refine_evar.
      etransitivity.
      subst_evars; higher_order_reflexivity.
      subst_evars; higher_order_reflexivity.
      { etransitivity.
        match goal with
          |- ?b = _ =>
          let b' := (eval pattern (build_aligned_ByteString v1) in b) in
          let b' := match b' with ?f _ => f end in
          eapply (@AlignedDecoders.optimize_Guarded_Decode n1 _ 2 b')
        end.
        { intros.
          destruct n1 as [ | [ | n1] ]; try omega.
          pose proof (@decode_unused_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
            simpl in H'; rewrite H'; try reflexivity; auto.
          pose proof (@decode_unused_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
            simpl in H'; rewrite H'; try reflexivity; auto.
        }
        { intros; etransitivity.

          idtac.
          unfold DecodeBindOpt2 at 1;rewrite (@AlignedDecodeUnusedChars dns_list_cache _ _ _ 2).
          rewrite byte_align_decode_DomainName.
          reflexivity.
          higher_order_reflexivity.
        }
        simpl.
        instantiate (1 := fun n1 v1 cd0 =>  If  NPeano.leb 2 n1
                                                Then `(proj, rest, env') <- Ifopt byte_aligned_decode_DomainName
                                                (snd (Vector_split 2 (n1 - 2) (Guarded_Vector_split 2 n1 v1)))
                                                (addD cd0 16) as p1
                                                                   Then let (p2, cd') := p1 in
                                                                        let (a17, b') := p2 in Some (a17, b', cd')
                                                                                                    Else None;
                                                                                               Some (proj, rest, env') Else None); simpl.
        find_if_inside; simpl; eauto.
        repeat rewrite (If_Opt_Then_Else_DecodeBindOpt (cache := dns_list_cache)).
        simpl.
        unfold mult; simpl.
        match goal with
          |- Ifopt ?b as _ Then _ Else _ = _ =>
          destruct b as [ [ [? [? ?] ] ?] | ]; reflexivity
        end.
      }
      { etransitivity.
        match goal with
          |- ?b = _ =>
          let b' := (eval pattern (build_aligned_ByteString v1) in b) in
          let b' := match b' with ?f _ => f end in
          eapply (@AlignedDecoders.optimize_Guarded_Decode n1 _ 6 b')
        end.
        { intros.
          destruct n1 as [ | [ | n1] ]; try omega.
          pose proof (@decode_unused_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
            simpl in H'; rewrite H'; try reflexivity; auto.
          pose proof (@decode_unused_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
            simpl in H'; rewrite H'; try reflexivity; auto.
          simpl.
          unfold DecodeBindOpt2 at 1;
          pose proof (fun C B => @AlignedDecodeUnusedChars dns_list_cache _ C B 2) as H';
            simpl in H'; rewrite H'; clear H'.
          destruct n1 as [ | [ | [ | [ | n1] ] ] ] ; try omega;
            try reflexivity.
        }
        { intros; etransitivity.
          simpl.
          unfold DecodeBindOpt2 at 1; pose proof (fun C B => @AlignedDecodeUnusedChars dns_list_cache _ C B 2) as H';
            simpl in H'; rewrite H'; clear H'.
          unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode4Char dns_list_cache); simpl.
          reflexivity.
          higher_order_reflexivity.
        }
        simpl.
        repeat (rewrite Vector_split_merge,
                <- Eqdep_dec.eq_rect_eq_dec;
                eauto using Peano_dec.eq_nat_dec ).
        unfold mult; simpl.
        instantiate (1 :=
                       fun n1 v1 cd0
                       => If NPeano.leb 6 n1
                             Then Let n2 := Core.append_word
                                              (snd (Vector_split 2 (S (S (S (S (n1 - 6))))) (Guarded_Vector_split 6 n1 v1)))[@
                                                                                                                               Fin.FS (Fin.FS (Fin.FS Fin.F1))]
                                              (Core.append_word
                                                 (snd (Vector_split 2 (S (S (S (S (n1 - 6))))) (Guarded_Vector_split 6 n1 v1)))[@
                                                                                                                                  Fin.FS (Fin.FS Fin.F1)]
                                                 (Core.append_word
                                                    (snd (Vector_split 2 (S (S (S (S (n1 - 6))))) (Guarded_Vector_split 6 n1 v1)))[@
                                                                                                                                     Fin.FS Fin.F1]
                                                    (snd (Vector_split 2 (S (S (S (S (n1 - 6))))) (Guarded_Vector_split 6 n1 v1)))[@Fin.F1])) in
                           Some
                             (n2, existT _ _ (snd (Vector_split (2 + 4) (n1 - 6) (Guarded_Vector_split 6 n1 v1))),
                              addD (addD cd0 16) 32) Else None).
        simpl; find_if_inside; simpl; eauto.
      }
      { etransitivity.
        match goal with
          |- ?b = _ =>
          let b' := (eval pattern (build_aligned_ByteString v1) in b) in
          let b' := match b' with ?f _ => f end in
          eapply (@AlignedDecoders.optimize_Guarded_Decode n1 _ 2 b')
        end.
        { intros.
          destruct n1 as [ | [ | n1] ]; try omega.
          pose proof (@decode_unused_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
            simpl in H'; rewrite H'; try reflexivity; auto.
          pose proof (@decode_unused_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
            simpl in H'; rewrite H'; try reflexivity; auto.
        }
        { intros; etransitivity.
          simpl.
          unfold DecodeBindOpt2 at 1; pose proof (fun C B => @AlignedDecodeUnusedChars dns_list_cache _ C B 2) as H';
            simpl in H'; rewrite H'; clear H'.
          rewrite byte_align_decode_DomainName.
          reflexivity.
          higher_order_reflexivity.
        }
        simpl.
        instantiate (1 :=
                       fun n1 v1 cd0 =>
                         If  NPeano.leb 2 n1
                             Then `(proj, rest, env') <- Ifopt byte_aligned_decode_DomainName
                             (snd (Vector_split 2 (n1 - 2) (Guarded_Vector_split 2 n1 v1)))
                             (addD cd0 16) as p1
                                                Then let (p2, cd') := p1 in
                                                     let (a17, b') := p2 in Some (a17, b', cd')
                                                                                 Else None;
                                                                            Some (proj, rest, env') Else None).
        simpl.
        find_if_inside; simpl; eauto.
        repeat rewrite (If_Opt_Then_Else_DecodeBindOpt (cache := dns_list_cache)).
        unfold mult; simpl.
        match goal with
          |- Ifopt ?b as _ Then _ Else _ = _ =>
          destruct b as [ [ [? [? ?] ] ?] | ]; reflexivity
        end.
      }
      Arguments plus : simpl never.
      { etransitivity.
        match goal with
          |- ?b = _ =>
          let b' := (eval pattern (build_aligned_ByteString v1) in b) in
          let b' := match b' with ?f _ => f end in
          eapply (@AlignedDecoders.optimize_Guarded_Decode n1 _ 2 b')
        end.
        { intros.
          destruct n1 as [ | [ | n1] ]; try omega.
          pose proof (@decode_unused_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
            simpl in H'; rewrite H'; try reflexivity; auto.
          pose proof (@decode_unused_word_aligned_ByteString_overflow dns_list_cache _ 2) as H';
            simpl in H'; rewrite H'; try reflexivity; auto.
        }
        { intros; etransitivity.
          simpl.
          unfold DecodeBindOpt2 at 1;pose proof (fun C B => @AlignedDecodeUnusedChars dns_list_cache _ C B 2) as H';
            simpl in H'; rewrite H'; clear H'.
          rewrite byte_align_decode_DomainName.
          rewrite (If_Opt_Then_Else_DecodeBindOpt (cache := dns_list_cache));
            simpl.
          eapply optimize_under_if_opt; simpl; intros; set_refine_evar.
          destruct a17 as [ [? [ ? ?] ] ? ]; simpl.
          rewrite byte_align_decode_DomainName.
          rewrite (If_Opt_Then_Else_DecodeBindOpt (cache := dns_list_cache));
            simpl.
          etransitivity.
          eapply optimize_under_if_opt; simpl; intros; set_refine_evar.
          destruct a17 as [ [? [ ? ?] ] ? ]; simpl.
          etransitivity.
          match goal with
            |- ?b = _ =>
            let b' := (eval pattern (build_aligned_ByteString t2) in b) in
            let b' := match b' with ?f _ => f end in
            eapply (@AlignedDecoders.optimize_Guarded_Decode x2 _ 20 b')
          end.
          { subst_evars.
            intros; destruct x2 as [ | [ | [ | [ | x2] ] ] ].
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            etransitivity; set_refine_evar.
            unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode4Char dns_list_cache ).
            subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
            subst_evars.
            intros; destruct x2 as [ | [ | [ | [ | x2] ] ] ].
            instantiate (1 := fun _ => None).
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            etransitivity; set_refine_evar.
            unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode4Char dns_list_cache ).
            subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
            subst_evars.
            intros; destruct x2 as [ | [ | [ | [ | x2] ] ] ].
            instantiate (1 := fun _ => None).
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            etransitivity; set_refine_evar.
            unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode4Char dns_list_cache ).
            subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
            subst_evars.
            intros; destruct x2 as [ | [ | [ | [ | x2] ] ] ].
            instantiate (1 := fun _ => None).
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            etransitivity; set_refine_evar.
            unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode4Char dns_list_cache ).
            subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
            subst_evars.
            intros; destruct x2 as [ | [ | [ | [ | x2] ] ] ]; try omega.
            instantiate (1 := fun _ => None).
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            pose proof (@decode_word_aligned_ByteString_overflow dns_list_cache _ 4) as H';
              simpl in H'; rewrite H'; try reflexivity; auto.
            unfold LetIn; reflexivity.
            unfold LetIn; reflexivity.
            unfold LetIn; reflexivity.
            unfold LetIn; reflexivity.
          }
          { intros.
            etransitivity.
            unfold plus.
            simpl; unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode4Char dns_list_cache ).
            unfold plus.
            subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
            simpl; unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode4Char dns_list_cache ).
            subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
            simpl; unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode4Char dns_list_cache ).
            subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
            simpl; unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode4Char dns_list_cache ).
            subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
            simpl; unfold DecodeBindOpt2 at 1, BindOpt; rewrite (@AlignedDecode4Char dns_list_cache ).
            repeat (rewrite Vector_split_merge,
                    <- Eqdep_dec.eq_rect_eq_dec;
                    eauto using Peano_dec.eq_nat_dec ).
            higher_order_reflexivity.
            higher_order_reflexivity.
          }
          Opaque If_Opt_Then_Else.
          Opaque If_Then_Else.
          match goal with
            |- ?z = ?f (?d, existT _ ?x ?t, ?p) =>
            let z' := (eval pattern d, x, t, p in z) in
            let z' := match z' with ?f' _ _ _ _ => f' end in
            unify f (fun a => z' (fst (fst a)) (projT1 (snd (fst a)))
                                 (projT2 (snd (fst a)))
                                 (snd a));
              cbv beta; reflexivity
          end.
          subst_evars; reflexivity.
          Opaque Core.append_word.
          Opaque Guarded_Vector_split.
          Opaque Vector.tl.
          simpl.

          match goal with
            |- ?z = ?f (?d, existT _ ?x ?t, ?p) =>
            let z' := (eval pattern d, x, t, p in z) in
            let z' := match z' with ?f' _ _ _ _ => f' end in
            unify f (fun a => z' (fst (fst a)) (projT1 (snd (fst a)))
                                 (projT2 (snd (fst a)))
                                 (snd a));
              cbv beta; reflexivity
          end.
          Transparent If_Opt_Then_Else.
          Transparent If_Then_Else.
          simpl.
          subst_refine_evar; reflexivity.
          higher_order_reflexivity.
        }
        simpl.
        fold (plus 20 (n1 - 20)).
        fold (plus 16 (n1 - 16)).
        fold (plus 12 (n1 - 12)).
        fold (plus 8 (n1 - 8)).
        fold (plus 4 (n1 - 4)).
        match goal with
          |- context [S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S ?n)))))))))))))))] => fold (plus 16 n)
        end.
        match goal with
          |- If ?b Then ?t Else ?e =
             Ifopt ?z ?n ?v ?cd as a Then _ Else _ =>
          let b' := (eval pattern n, v, cd in b) in
          let b' := match b' with ?f _ _ _ => f end in
          let ZT := match type of z with _ -> _ -> _ -> option ?T => T end in
          makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> option ZT)
                   ltac:(fun zt =>
                           makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> option ZT)
                                    ltac:(fun et =>
                                            unify z (fun n v cd => If (b' n v cd) Then (et n v cd) Else (zt n v cd)); cbv beta; simpl; find_if_inside; simpl)) end.
        match goal with
          |- If_Opt_Then_Else ?a ?t ?e =
             Ifopt ?z ?n ?v ?cd as a Then _ Else _ =>
          let a' := (eval pattern n, v, cd in a) in
          let a' := match a' with ?f _ _ _ => f end in
          let AT := match type of a with option ?T => T end in
          let ZT := match type of z with _ -> _ -> _ -> option ?T => T end in
          makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> AT -> option ZT)
                   ltac:(fun zt =>
                           makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> option ZT)
                                    ltac:(fun et =>
                                            unify z (fun n v cd => If_Opt_Then_Else (a' n v cd)
                                                                                    (zt n v cd)
                                                                                    (et n v cd));
                                            cbv beta; simpl; destruct a; simpl)) end.
        match goal with
          |- If_Opt_Then_Else ?a ?t ?e =
             Ifopt ?z ?n ?v ?cd ?a'' as a Then _ Else _ =>
          let a' := (eval pattern n, v, cd, a'' in a) in
          let a' := match a' with ?f _ _ _ _ => f end in
          let AT := match type of a with option ?T => T end in
          let AT'' := match type of a'' with ?T => T end in
          let ZT := match type of z with _ -> _ -> _ -> _ -> option ?T => T end in
          makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> AT'' -> AT -> option ZT)
                   ltac:(fun zt =>
                           makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> AT'' -> option ZT)
                                    ltac:(fun et =>
                                            unify z (fun n v cd a'' => If_Opt_Then_Else (a' n v cd a'')
                                                                                        (zt n v cd a'')
                                                                                        (et n v cd a''));
                                            cbv beta; simpl; destruct a; simpl)) end.
        match goal with
          |- If ?b Then ?t Else ?e =
             Ifopt ?z ?n ?v ?cd ?q ?q' as a Then _ Else _ =>
          let b' := (eval pattern n, v, cd, q, q' in b) in
          let b' := match b' with ?f _ _ _ _ _ => f end in
          let QT := match type of q with ?T => T end in
          let QT' := match type of q' with ?T => T end in
          let ZT := match type of z with _ -> _ -> _ -> _ -> _ -> option ?T => T end in
          makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> QT -> QT' -> option ZT)
                   ltac:(fun zt =>
                           makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> QT -> QT' -> option ZT)
                                    ltac:(fun et =>
                                            unify z (fun n v cd q q' => If (b' n v cd q q') Then (et n v cd q q') Else (zt n v cd q q')); cbv beta; simpl; find_if_inside; simpl)) end.
        clear H H1.
        Opaque LetIn.
        match goal with
          |- _ =
             Ifopt ?z ?n ?v ?cd ?q ?q' as a Then _ Else _ =>
          let QT := match type of q with ?T => T end in
          let QT' := match type of q' with ?T => T end in
          let ZT1 := match type of z with _ -> _ -> _ -> _ -> _ -> option (?T1 * ?T2 * ?T3) => T1 end in
          let ZT2 := match type of z with _ -> _ -> _ -> _ -> _ -> option (?T1 * ?T2 * ?T3) => T2 end in
          let ZT3 := match type of z with _ -> _ -> _ -> _ -> _ -> option (?T1 * ?T2 * ?T3) => T3 end in
          makeEvar (forall n, Vector.t (word 8) n ->
                              CacheDecode -> QT -> QT' ->
                              word 32 -> word 32 ->
                              word 32 -> word 32 -> ZT1)
                   ltac:(fun zt1 =>
                           makeEvar (forall n, Vector.t (word 8) n ->
                                               CacheDecode -> QT -> QT' ->
                                               word 32 -> word 32 ->
                                               word 32 -> word 32 -> ZT2)
                                    ltac:(fun zt2 =>
                                            makeEvar (forall n, Vector.t (word 8) n ->
                                                                CacheDecode -> QT -> QT' ->
                                                                word 32 -> word 32 ->
                                                                word 32 -> word 32 -> ZT3)
                                                     ltac:(fun zt3 =>
                                                             makeEvar (forall n, Vector.t (word 8) n ->
                                                                                 CacheDecode -> QT -> QT' -> word 32)
                                                                      ltac:(fun w1 =>
                                                                              makeEvar (forall n, Vector.t (word 8) n ->
                                                                                                  CacheDecode -> QT -> QT' -> word 32)
                                                                                       ltac:(fun w2 =>
                                                                                               makeEvar (forall n, Vector.t (word 8) n ->
                                                                                                                   CacheDecode -> QT -> QT' -> word 32)
                                                                                                        ltac:(fun w3 => makeEvar (forall n, Vector.t (word 8) n ->
                                                                                                                                            CacheDecode -> QT -> QT' -> word 32)
                                                                                                                                 ltac:(fun w4 =>
                                                                                                                                         unify z (fun n v cd q q' => LetIn (w1 n v cd q q') (fun w => LetIn (w2 n v cd q q')  (fun w' => LetIn (w3  n v cd q q') (fun w'' => LetIn (w4 n v cd q q') (fun w''' => Some (zt1 n v cd q q' w w' w'' w''',
                                                                                                                                                                                                                                                                                                                       zt2 n v cd q q' w w' w'' w''',
                                                                                                                                                                                                                                                                                                                       zt3 n v cd q q' w w' w'' w'''
                                                                                                                                                 )))))); simpl)))))))
        end.
        simpl.
        rewrite LetIn_If_Opt_Then_Else.
        f_equal.
        higher_order_reflexivity.
        apply functional_extensionality; intros.
        simpl.
        rewrite LetIn_If_Opt_Then_Else.
        f_equal.
        higher_order_reflexivity.
        apply functional_extensionality; intros.
        simpl.
        rewrite LetIn_If_Opt_Then_Else.
        f_equal.
        higher_order_reflexivity.
        apply functional_extensionality; intros.
        simpl.
        rewrite LetIn_If_Opt_Then_Else.
        f_equal.
        higher_order_reflexivity.
        apply functional_extensionality; intros.
        simpl.
        repeat f_equal.
        higher_order_reflexivity.
        instantiate (1 := fun n1 v1 cd0 p1 p2 x1 x2 x3 x4 => existT _ _ _).
        simpl; reflexivity.
        higher_order_reflexivity.
        instantiate (1 := fun _ _ _ _ _ => None); reflexivity.
        instantiate (1 := fun _ _ _ _ => None); reflexivity.
        instantiate (1 := fun _ _ _ => None); reflexivity.
        instantiate (1 := fun _ _ _ => None); reflexivity.
      }
      subst_refine_evar; reflexivity.
      subst_refine_evar; reflexivity.
      higher_order_reflexivity.
      match goal with
        |- ?z = ?f (?d, existT _ ?x ?t, ?p) =>
        let z' := (eval pattern d, x, t, p in z) in
        let z' := match z' with ?f' _ _ _ _ => f' end in
        unify f (fun a => z' (fst (fst a)) (projT1 (snd (fst a)))
                             (projT2 (snd (fst a)))
                             (snd a));
          cbv beta; reflexivity
      end.
      higher_order_reflexivity.
      simpl.
      match goal with
        |- If_Opt_Then_Else ?a ?t ?e =
           Ifopt ?z ?n ?v ?cd as a Then _ Else _ =>
        let a' := (eval pattern n, v, cd in a) in
        let a' := match a' with ?f _ _ _ => f end in
        let AT := match type of a with option ?T => T end in
        let ZT := match type of z with _ -> _ -> _ -> option ?T => T end in
        makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> AT -> option ZT)
                 ltac:(fun zt =>
                         unify z (fun n v cd => If_Opt_Then_Else (a' n v cd)
                                                                 (zt n v cd)
                                                                 (@None ZT));
                         cbv beta; simpl; destruct a; simpl) end.
      match goal with
        |- If ?b Then ?t Else ?e =
           Ifopt ?z ?n ?v ?cd ?q as a Then _ Else _ =>
        let b' := (eval pattern n, v, cd, q in b) in
        let b' := match b' with ?f _ _ _ _ => f end in
        let QT := match type of q with ?T => T end in
        let ZT := match type of z with _ -> _ -> _ -> _ -> option ?T => T end in
        makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> QT -> option ZT)
                 ltac:(fun zt =>
                         unify z (fun n v cd q => If (b' n v cd q) Then (zt n v cd q) Else (@None ZT)); cbv beta; simpl; find_if_inside; simpl)
      end.

      match goal with
        |- LetIn ?b ?k =
           Ifopt ?z ?n ?v ?cd ?q as a Then _ Else _ =>
        let b' := (eval pattern n, v, cd, q in b) in
        let b' := match b' with ?f _ _ _ _ => f end in
        let BT := match type of b with ?T => T end in
        let QT := match type of q with ?T => T end in
        let ZT := match type of z with _ -> _ -> _ -> _ -> option ?T => T end in
        makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> QT -> BT -> option ZT)
                 ltac:(fun zt =>
                         unify z (fun n v cd q => LetIn (b' n v cd q) (zt n v cd q)))
      end.
      simpl.
      rewrite LetIn_If_Opt_Then_Else.
      f_equal.
      apply functional_extensionality; intros.
      match goal with
        |- If_Opt_Then_Else ?a ?t ?e =
           Ifopt ?z ?n ?v ?cd ?q ?q' as a Then _ Else _ =>
        let a' := (eval pattern n, v, cd, q, q' in a) in
        let a' := match a' with ?f _ _ _ _ _ => f end in
        let AT := match type of a with option ?T => T end in
        let QT := match type of q with ?T => T end in
        let QT' := match type of q' with ?T => T end in
        let ZT := match type of z with _ -> _ -> _ -> _ -> _ -> option ?T => T end in
        makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> QT -> QT' -> AT -> option ZT)
                 ltac:(fun zt =>
                         unify z (fun n v cd q q' => If_Opt_Then_Else (a' n v cd q q')
                                                                      (zt n v cd q q')
                                                                      (@None ZT));
                         cbv beta; simpl; destruct a; simpl) end.

      match goal with
        |- LetIn ?b ?k =
           Ifopt ?z ?n ?v ?cd ?q ?q' ?q'' as a Then _ Else _ =>
        let b' := (eval pattern n, v, cd, q, q', q'' in b) in
        let b' := match b' with ?f _ _ _ _ _ _ => f end in
        let BT := match type of b with ?T => T end in
        let QT := match type of q with ?T => T end in
        let QT' := match type of q' with ?T => T end in
        let QT'' := match type of q'' with ?T => T end in
        let ZT := match type of z with _ -> _ -> _ -> _ -> _ -> _ -> option ?T => T end in
        makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> QT -> QT' -> QT'' -> BT -> option ZT)
                 ltac:(fun zt =>
                         unify z (fun n v cd q q' q'' => LetIn (b' n v cd q q' q'') (zt n v cd q q' q'')))
      end.
      simpl.
      rewrite LetIn_If_Opt_Then_Else.
      f_equal.
      apply functional_extensionality; intros.
      match goal with
        |- If_Opt_Then_Else ?a ?t ?e =
           Ifopt ?z ?n ?v ?cd ?q ?q' ?q'' ?q''' as a Then _ Else _ =>
        let a' := (eval pattern n, v, cd, q, q', q'', q''' in a) in
        let a' := match a' with ?f _ _ _ _ _ _ _ => f end in
        let AT := match type of a with option ?T => T end in
        let QT := match type of q with ?T => T end in
        let QT' := match type of q' with ?T => T end in
        let QT'' := match type of q'' with ?T => T end in
        let QT''' := match type of q''' with ?T => T end in
        let ZT := match type of z with _ -> _ -> _ -> _ -> _ -> _ -> _ -> option ?T => T end in
        makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> QT -> QT' -> QT'' -> QT''' -> AT -> option ZT)
                 ltac:(fun zt =>
                         unify z (fun n v cd q q' q'' q''' => If_Opt_Then_Else (a' n v cd q q' q'' q''')
                                                                               (zt n v cd q q' q'' q''')
                                                                               (@None ZT));
                         cbv beta; simpl; destruct a; simpl) end.

      match goal with
        |- LetIn ?b ?k =
           Ifopt ?z ?n ?v ?cd ?q ?q' ?q'' ?q''' ?r as a Then _ Else _ =>
        let b' := (eval pattern n, v, cd, q, q', q'', q''', r in b) in
        let b' := match b' with ?f _ _ _ _ _ _ _ _ => f end in
        let BT := match type of b with ?T => T end in
        let QT := match type of q with ?T => T end in
        let QT' := match type of q' with ?T => T end in
        let QT'' := match type of q'' with ?T => T end in
        let QT''' := match type of q''' with ?T => T end in
        let RT := match type of r with ?T => T end in
        let ZT := match type of z with _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> option ?T => T end in
        makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> QT -> QT' -> QT'' -> QT''' -> RT -> BT -> option ZT)
                 ltac:(fun zt =>
                         unify z (fun n v cd q q' q'' q''' r => LetIn (b' n v cd q q' q'' q''' r) (zt n v cd q q' q'' q''' r)))
      end.
      simpl.
      rewrite LetIn_If_Opt_Then_Else.
      f_equal.
      apply functional_extensionality; intros.
      Time match goal with
             |- If_Opt_Then_Else ?a ?t ?e =
                Ifopt ?z ?n ?v ?cd ?q ?q' ?q'' ?q''' ?r ?r' as a Then _ Else _ =>
             let a' := (eval pattern n, v, cd, q, q', q'', q''', r, r' in a) in
             let a' := match a' with ?f _ _ _ _ _ _ _ _ _ => f end in
             let AT := match type of a with option ?T => T end in
             let QT := match type of q with ?T => T end in
             let QT' := match type of q' with ?T => T end in
             let QT'' := match type of q'' with ?T => T end in
             let QT''' := match type of q''' with ?T => T end in
             let RT := match type of r with ?T => T end in
             let RT' := match type of r' with ?T => T end in
             let ZT := match type of z with _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> _ -> option ?T => T end in
             makeEvar (forall n, Vector.t (word 8) n -> CacheDecode -> QT -> QT' -> QT'' -> QT''' -> RT -> RT' -> AT -> option ZT)
                      ltac:(fun zt =>
                              unify z (fun n v cd q q' q'' q''' r r'=> If_Opt_Then_Else (a' n v cd q q' q'' q''' r r')
                                                                                        (zt n v cd q q' q'' q''' r r')
                                                                                        (@None ZT));
                                cbv beta; simpl; destruct a; simpl) end.
      (* This unification takes four minutes :p*)

      match goal with
        |- _ =
           Ifopt ?z ?n ?v ?cd ?q ?q' ?q'' ?q''' ?r ?r' ?r'' as a Then _ Else _ =>
        let QT := match type of q with ?T => T end in
        let QT' := match type of q' with ?T => T end in
        let QT'' := match type of q'' with ?T => T end in
        let QT''' := match type of q''' with ?T => T end in
        let RT := match type of r with ?T => T end in
        let RT' := match type of r' with ?T => T end in
        let RT'' := match type of r'' with ?T => T end in
        let ZT1 := match type of z with _ -> _ -> _ -> _ -> _ ->
                                        _ -> _ -> _ -> _ -> _ -> option (?T1 * ?T2 * ?T3) => T1 end in
        let ZT2 := match type of z with _ -> _ -> _ -> _ -> _ ->
                                        _ -> _ -> _ -> _ -> _ -> option (?T1 * ?T2 * ?T3) => T2 end in
        let ZT3 := match type of z with _ -> _ -> _ -> _ -> _ ->
                                        _ -> _ -> _ -> _ -> _ -> option (?T1 * ?T2 * ?T3) => T3 end in
        makeEvar (forall n, Vector.t (word 8) n ->
                            CacheDecode -> QT -> QT' ->
                            QT'' -> QT''' -> RT -> RT' -> RT''
                            -> ZT1)
                 ltac:(fun zt1 =>
                         makeEvar (forall n, Vector.t (word 8) n ->
                                             CacheDecode -> QT -> QT' ->
                                             QT'' -> QT''' -> RT -> RT' -> RT''
                                             -> ZT2)
                                  ltac:(fun zt2 =>
                                          makeEvar (forall n, Vector.t (word 8) n ->
                                                              CacheDecode -> QT -> QT' ->
                                                              QT'' -> QT''' -> RT -> RT' -> RT''
                                                              -> ZT3)
                                                   ltac:(fun zt3 => unify z (fun n v cd q q' q'' q''' r r' r'' =>
                                                                               Some (zt1 n v cd q q' q'' q''' r r' r'',
                                                                                     zt2 n v cd q q' q'' q''' r r' r'',
                                                                                     zt3 n v cd q q' q'' q''' r r' r''));
                                                                    simpl))) end.
      repeat f_equal; try higher_order_reflexivity.
      subst_evars; reflexivity.
      subst_evars; reflexivity.
      subst_evars; reflexivity.
      subst_evars; reflexivity.
      subst_evars; reflexivity.
      subst_evars; reflexivity.
      subst_evars; reflexivity.
      subst_evars; higher_order_reflexivity.
    }
    { match goal with
        |- ?z = ?f (?d, existT _ ?x ?t, ?p) =>
        let z' := (eval pattern d, x, t, p in z) in
        let z' := match z' with ?f' _ _ _ _ => f' end in
        unify f (fun a => z' (fst (fst a)) (projT1 (snd (fst a)))
                             (projT2 (snd (fst a)))
                             (snd a));
          cbv beta; reflexivity
      end.
    }
    subst_evars; reflexivity.
    subst_evars; reflexivity.
    subst_evars; reflexivity.
    subst_evars; reflexivity.
    subst_evars; reflexivity.
    simpl.
    higher_order_reflexivity.
    Time Defined.

  Check ByteAligned_packetDecoderImpl.
  Definition ByteAligned_packetDecoderImpl' {A} (k : _ -> A) n :=
    Eval simpl in (projT1 (ByteAligned_packetDecoderImpl k n)).

  Lemma ByteAligned_packetDecoderImpl'_OK {A}
    : forall (f : _ -> A) n (v : Vector.t _ (12 + n)),
        f (fst packetDecoderImpl (build_aligned_ByteString v) (Some (wzero 17), @nil (pointerT * string))) =
        ByteAligned_packetDecoderImpl' f n v (Some (wzero 17) , @nil (pointerT * string))%list.
  Proof.
    intros.
    pose proof (projT2 (ByteAligned_packetDecoderImpl f n));
      cbv beta in H.
    rewrite H.
    set (H' := (Some (wzero 17), @nil (pointerT * string))).
    simpl.
    unfold ByteAligned_packetDecoderImpl'.
    reflexivity.
  Qed.

End DnsPacket.
