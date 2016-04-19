Require Export
        Coq.Numbers.BinNums
        Coq.NArith.BinNat.
Require Import
        Coq.omega.Omega
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Sig
        Fiat.BinEncoders.Env.BinLib.Core.

Set Implicit Arguments.


Fixpoint exp2' (l : nat) :=
  match l with
  | O    => xH
  | S l' => xO (exp2' l')
  end.

Definition exp2 (l : nat) := Npos (exp2' l).
Definition exp2_nat (l : nat) := nat_of_N (exp2 l).

Notation "'uint' size" := {n : N | (n < exp2 size)%N} (at level 30).

Section FixIntBinEncoder.
  Variable size : nat.

  Variable cache : Cache.
  Variable cacheAdd : CacheAdd cache N.

  Fixpoint encode''(pos : positive) (acc : list bool) :=
    match pos with
      | xI pos' => encode'' pos' (true :: acc)
      | xO pos' => encode'' pos' (false :: acc)
      | xH      => true :: acc
    end.

  Definition encode' (n : N) :=
    match n with
      | N0       => nil
      | Npos pos => encode'' pos nil
    end.

  Fixpoint pad (b : list bool) (l : nat) :=
    match l with
      | O    => b
      | S l' => false :: pad b l'
    end.


  Definition FixInt_encode (n : uint size) (ce : CacheEncode) :=
    let b := encode' (proj1_sig n)
    in  (pad b (size - (length b)), addE ce (N.of_nat size)).

  Fixpoint decode'' (b : list bool) (l : nat) (acc : positive) :=
    match l with
      | O    => (acc, b)
      | S l' =>
        match b with
          | nil         => (acc, nil)
          | false :: b' => decode'' b' l' (xO acc)
          | true  :: b' => decode'' b' l' (xI acc)
        end
    end.

  Fixpoint decode' (b : list bool) (l : nat) {struct l} :=
    match l with
      | O    => (N0, b)
      | S l' =>
        match b with
          | nil         => (N0, nil)
          | false :: b' => decode' b' l'
          | true  :: b' =>
            match decode'' b' l' xH with
              | (pos, b'') => (Npos pos, b'')
            end
        end
    end.

  Fixpoint bitlength (n : positive) : nat :=
    match n with
    | xH    => 1
    | xI n' => 1 + bitlength n'
    | xO n' => 1 + bitlength n'
    end.

  Lemma bitlength_exp2 : forall l, bitlength (exp2' l) = S l.
  Proof.
    induction l; simpl; eauto.
  Qed.

  Lemma bitlength_lt : forall n m, bitlength n < bitlength m -> (n < m)%positive.
  Proof.
    intros n m.
    rewrite <- Pos.compare_lt_iff. unfold Pos.compare. generalize dependent m.
    induction n; destruct m; intros; simpl in *; auto; try (solve [ inversion H; inversion H1 ]).
    - apply IHn. apply lt_S_n. auto.
    - rewrite Pos.compare_cont_Gt_Lt. rewrite <- Pos.compare_lt_iff. apply IHn. apply lt_S_n. auto.
    - rewrite Pos.compare_cont_Lt_Lt. apply Pos.lt_le_incl. rewrite <- Pos.compare_lt_iff. apply IHn. apply lt_S_n. auto.
    - apply IHn. apply lt_S_n. auto.
  Qed.

  Lemma bitlength_decode'' :
    forall l b acc, bitlength (fst (decode'' b l acc)) <= l + bitlength acc.
  Proof.
    induction l; intros; simpl in *.
    - destruct b; eauto.
    - destruct b; simpl in *.
      + omega.
      + destruct b; simpl in *.
        etransitivity. eauto. simpl. omega.
        etransitivity. eauto. simpl. omega.
  Qed.

  Lemma decode'_size : forall s b, N.lt (fst (decode'  b s)) (exp2 s).
  Proof.
    induction s; intuition eauto; simpl.
    rewrite <- N.compare_lt_iff; eauto.
    destruct b; simpl.
    - rewrite <- N.compare_lt_iff; eauto.
    - destruct b; simpl.
      + unfold exp2; simpl. clear IHs.
        destruct (decode'' b0 s 1) eqn: eq.
        simpl. rewrite <- N.compare_lt_iff. simpl.
        rewrite Pos.compare_lt_iff. apply bitlength_lt. simpl.
        rewrite bitlength_exp2.
        pose proof (bitlength_decode'' s b0 xH). rewrite eq in H. simpl in *. omega.
      + etransitivity; eauto; unfold exp2; simpl.
        apply bitlength_lt. simpl. omega.
  Qed.

  Definition FixInt_decode (b : list bool) (cd : CacheDecode)
    : {n : N | (n < exp2 size)%N} * list bool * CacheDecode.
    refine (let x := decode' b size in
            (exist _ (fst x) _, snd x, addD cd (N.of_nat size))).
    eapply decode'_size.
  Defined.

  Lemma encode''_pull : forall pos acc, encode'' pos acc =  encode'' pos nil ++ acc.
  Proof.
    (induction pos; simpl; intuition eauto);
    [ rewrite IHpos; rewrite IHpos with (acc:=(true :: nil));
      rewrite <- app_assoc; reflexivity |
      rewrite IHpos; rewrite IHpos with (acc:=(false :: nil));
      rewrite <- app_assoc; reflexivity ].
  Qed.

  Lemma encode''_size :
    forall p s, BinPos.Pos.lt p (exp2' s) -> length (encode'' p nil) <= s.
  Proof.
    intros p s; generalize dependent p; induction s; intuition.
    - inversion H; destruct p; compute in H1; discriminate.
    - destruct p.
      + simpl; rewrite encode''_pull; rewrite app_length; simpl.
        rewrite Plus.plus_comm; simpl; apply Le.le_n_S.
        apply IHs; unfold BinPos.Pos.lt, BinPos.Pos.compare in H; simpl in *.
        apply BinPos.Pos.compare_cont_Gt_Lt; assumption.
      + simpl; rewrite encode''_pull; rewrite app_length; simpl.
        rewrite Plus.plus_comm; simpl; apply Le.le_n_S.
        apply IHs; unfold BinPos.Pos.lt, BinPos.Pos.compare in *; simpl in *.
        assumption.
      + simpl; auto with arith.
  Qed.

  Lemma encode'_size : forall n s, N.lt n (exp2 s) -> length (encode' n) <= s.
  Proof.
    intros; unfold encode'; destruct n.
    + auto with arith.
    + apply encode''_size. unfold BinPos.Pos.lt, exp2 in H. apply H.
  Qed.

  Lemma decode'_pad :
    forall ls s ext, length ls <= s ->
                     decode' (pad ls (s - length ls) ++ ext) s =
                     decode' (ls ++ ext) (length ls).
  Proof.
    intros ls s; remember (s - length ls) as m;
    generalize dependent s; generalize dependent ls;
    induction m; intuition; simpl.
    destruct s; [ omega | simpl ].
    apply IHm; omega.
  Qed.

  Lemma decode''_length :
    forall ls ext p,
      decode'' (ls ++ ext) (length ls) p =
      (fst (decode'' ls (length ls) p), (snd (decode'' ls (length ls) p) ++ ext)).
  Proof.
    induction ls; intuition eauto; simpl.
    { destruct ext; eauto. }
    { destruct a; eauto. }
  Qed.

  Lemma decode'_length :
    forall ls ext,
      decode' (ls ++ ext) (length ls) =
      (fst (decode' ls (length ls)), (snd (decode' ls (length ls)) ++ ext)).
  Proof.
    induction ls; intuition eauto; simpl.
    destruct a; eauto.
    repeat rewrite decode''_length.
    destruct (decode'' ls (length ls) 1); eauto.
  Qed.

  Lemma decode''_pulltrue :
    forall ls p,
      decode'' (ls ++ true :: nil) (length (ls ++ true :: nil)) p =
      (xI (fst (decode'' ls (length ls) p)), snd (decode'' ls (length ls) p)).
  Proof.
    induction ls; simpl; intuition eauto.
    destruct a; eauto.
  Qed.

  Lemma decode''_pullfalse :
    forall ls p,
      decode'' (ls ++ false :: nil) (length (ls ++ false :: nil)) p =
      (xO (fst (decode'' ls (length ls) p)), snd (decode'' ls (length ls) p)).
  Proof.
    induction ls; simpl; intuition eauto.
    destruct a; eauto.
  Qed.

  Lemma encode_correct' :
    forall p, decode' (encode'' p nil) (length (encode'' p nil)) = (N.pos p, nil).
  Proof.
    induction p; intuition eauto; simpl; rewrite encode''_pull.
    { remember (encode'' p Datatypes.nil) as ls; clear Heqls.
      generalize dependent p; induction ls; intuition eauto; inversion IHp.
      destruct a; simpl in *; eauto.
      clear -IHp; rewrite decode''_pulltrue.
      destruct (decode'' ls (length ls) 1).
      inversion IHp; eauto.
    }
    { remember (encode'' p Datatypes.nil) as ls; clear Heqls.
      generalize dependent p; induction ls; intuition eauto; inversion IHp.
      destruct a; simpl in *; eauto.
      clear -IHp; rewrite decode''_pullfalse.
      destruct (decode'' ls (length ls) 1).
      inversion IHp; eauto.
    }
  Qed.

  Theorem FixInt_encode_correct :
    forall predicate, encode_decode_correct cache btransformer predicate FixInt_encode FixInt_decode.
  Proof.
    unfold encode_decode_correct, FixInt_encode, FixInt_decode.
    intros predicate env env' xenv xenv' [n P] [n' P'] bin ext ext' Eeq _ Penc Pdec. simpl in *.
    inversion Penc; clear Penc; inversion Pdec; clear Pdec; subst; intuition;
    [ apply add_correct; auto | apply sig_equivalence | change ext with (snd (n, ext)); f_equal ];
    apply encode'_size in P;
    rewrite decode'_pad; auto; clear P;
    destruct n; simpl; auto; rewrite decode'_length;
    rewrite encode_correct'; reflexivity.
  Qed.
End FixIntBinEncoder.

Arguments FixInt_encode {_ _ _} _ _.