Require Export Coq.Lists.List
               Fiat.BinEncoders.NoEnv.Libraries.FixInt.
Require Import Fiat.BinEncoders.NoEnv.Specs
               Fiat.BinEncoders.NoEnv.Libraries.Sig
               Coq.omega.Omega.

Set Implicit Arguments.

Section FixListEncoder.
  Variable (A : Type)
           (B : Type)
           (size : nat)
           (encode_A : A * B -> B)
           (predicate_A : A -> Prop)
           (decoder_A : decoder (fun bundle => predicate_A (fst bundle)) encode_A).

  Definition data_t := { xs : list A | length xs < exp2_nat size }.

  Definition FixList_getlength
             (ls : data_t) : {n : N | (n < exp2 size)%N}.
    refine (exist _ (N_of_nat (length (proj1_sig ls))) _).
    destruct ls as [ xs xs_pf ]. unfold exp2_nat in xs_pf. simpl.
    rewrite <- Nnat.N2Nat.id. rewrite <- N.compare_lt_iff.
    rewrite <- Nnat.Nat2N.inj_compare.
    rewrite <- Compare_dec.nat_compare_lt.
    eauto.
  Defined.

  Definition FixList_predicate (len : {n : N | (n < exp2 size)%N}) (bundle : data_t * B) :=
    FixList_getlength (fst bundle) = len /\
    forall x, In x (proj1_sig (fst bundle)) -> predicate_A x.

  Fixpoint encode' (xs : list A) (ext : B) :=
    match xs with
      | nil => ext
      | x :: xs => encode_A (x, encode' xs ext)
    end.

  Definition FixList_encode (bundle : data_t * B) := encode' (proj1_sig (fst bundle)) (snd bundle).

  Fixpoint decode' (len : nat) (b : B) :=
    match len with
    | O => (nil, b)
    | S size' => let (_data, _bin) := @decode _ _ _ _ decoder_A b in
                 let (_rest, _bin') := decode' size' _bin in
                     (_data :: _rest, _bin')
    end.

  Lemma decode'_length :
    forall len bin, length (fst (decode' len bin)) = len.
  Proof.
    induction len; intuition eauto.
    simpl. destruct (decode bin).
    specialize (IHlen b). destruct (decode' len b). simpl. f_equal. eauto.
  Qed.

  Lemma exp2_nat_nonzero :
    forall size, exp2_nat size <> O.
  Proof.
    assert (forall size, exp2_nat size > O) as lt_pf.
    intro s. unfold exp2_nat. unfold exp2. rewrite positive_N_nat.
    destruct (Pos2Nat.is_succ (exp2' s)). rewrite H. eapply gt_Sn_O.
    intro s. specialize (lt_pf s). omega.
  Qed.

  Definition FixList_decode (len : nat) (b : B) : data_t * B.
    refine (exist _ (fst (decode' (min (pred (exp2_nat size)) len) b)) _, snd (decode' len b)).
    rewrite decode'_length.
    rewrite NPeano.Nat.min_lt_iff.
    left. unfold lt.
    rewrite NPeano.Nat.succ_pred; [ | eapply exp2_nat_nonzero ]; eauto.
  Defined.

  Theorem FixList_encode_decode_correct :
    forall len, encode_decode_correct (FixList_predicate len)
                                      FixList_encode
                                      (FixList_decode (nat_of_N (proj1_sig len))).
  Proof.
    unfold encode_decode_correct, FixList_predicate, FixList_encode, FixList_decode.
    intros [len len_pf] [[data data_pf] ext] pred_pf. simpl.
    assert (min (pred (exp2_nat size)) (N.to_nat len) = N.to_nat len) as pmin.
    rewrite Min.min_r; eauto. eapply NPeano.Nat.lt_le_pred. unfold exp2_nat.
    eapply nat_compare_lt. rewrite <- Nnat.N2Nat.inj_compare. eauto.
    f_equal. eapply sig_equivalence; try rewrite pmin; clear pmin.
    - generalize dependent len. generalize dependent data.
      induction data; intros data_pf len len_pf [psize pin]; simpl in *.
      + inversion psize. eauto.
      + inversion psize.
        assert (length data < exp2_nat size) as data_pf' by omega.
        assert (N.lt (N.pred len) (exp2 size)) as len_pf' by (eapply N.lt_lt_pred; eauto).
        assert ( FixList_getlength
             (exist (fun xs : list A => length xs < exp2_nat size) data
                data_pf') =
           exist (fun n : N => (n < exp2 size)%N) (N.pred len) len_pf' /\
           (forall x : A, In x data -> predicate_A x)) as IHdata_pf.
        split; eauto. eapply sig_equivalence. simpl.
        rewrite <- H0. simpl.
        clear. destruct (length data). eauto. simpl. rewrite Pos.pred_N_succ. eauto.
        specialize (IHdata data_pf' (N.pred len) len_pf' IHdata_pf).
        rewrite <- H0 in IHdata. rewrite Nnat.N2Nat.inj_pred in IHdata.
        destruct (N.to_nat (N.pos (Pos.of_succ_nat (length data)))) eqn: eq.
        inversion eq. rewrite SuccNat2Pos.id_succ in H1. inversion H1.
        simpl in *. rewrite (@decode_correct _ _ _ _ decoder_A); eauto.
        simpl in *. destruct (decode' n (encode' data ext)).
        simpl in *. subst. reflexivity.
    - clear pmin. generalize dependent len. generalize dependent data.
      induction data; intros data_pf len len_pf [psize pin]; simpl in *.
      + inversion psize. eauto.
      + inversion psize.
        assert (length data < exp2_nat size) as data_pf' by omega.
        assert (N.lt (N.pred len) (exp2 size)) as len_pf' by (eapply N.lt_lt_pred; eauto).
        assert ( FixList_getlength
             (exist (fun xs : list A => length xs < exp2_nat size) data
                data_pf') =
           exist (fun n : N => (n < exp2 size)%N) (N.pred len) len_pf' /\
           (forall x : A, In x data -> predicate_A x)) as IHdata_pf.
        split; eauto. eapply sig_equivalence. simpl.
        rewrite <- H0. simpl.
        clear. destruct (length data). eauto. simpl. rewrite Pos.pred_N_succ. eauto.
        specialize (IHdata data_pf' (N.pred len) len_pf' IHdata_pf).
        rewrite <- H0 in IHdata. rewrite Nnat.N2Nat.inj_pred in IHdata.
        destruct (N.to_nat (N.pos (Pos.of_succ_nat (length data)))) eqn: eq.
        inversion eq. rewrite SuccNat2Pos.id_succ in H1. inversion H1.
        simpl in *. rewrite (@decode_correct _ _ _ _ decoder_A); eauto.
        simpl in *. destruct (decode' n (encode' data ext)).
        simpl in *. subst. reflexivity.
  Qed.
End FixListEncoder.

Global Instance FixList_decoder
       (A : Type)
       (B : Type)
       (size : nat)
       (len : {n : N | (n < exp2 size)%N})
       (predicate_A : A -> Prop)
       (encode_A : A * B -> B)
       (decoder_A : decoder (fun bundle => predicate_A (fst bundle)) encode_A)
  : decoder (FixList_predicate predicate_A len)
            (FixList_encode (size:=size) encode_A) :=
  { decode := FixList_decode size predicate_A decoder_A (nat_of_N (proj1_sig len));
    decode_correct := @FixList_encode_decode_correct _ _ _ _ _ _ _ }.

Arguments FixList_predicate / _ _ _ _ _ _.
Arguments FixList.data_t / _ _.