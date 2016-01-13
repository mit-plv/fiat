Require Export Coq.Numbers.BinNums
               Coq.NArith.BinNat.
Require Import Coq.omega.Omega
               Coq.Logic.ProofIrrelevance.
Require Import Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Core.

Section FixInt_encode_decode.

  Variable size : nat.
  (* Hypothesis size_nonzero : 0 < size. *)

  Fixpoint exp2' (l : nat) :=
    match l with
      | O    => xH
      | S l' => xO (exp2' l')
    end.

  Definition exp2 (l : nat) := Npos (exp2' l).

  Definition predicate (n : N) := (n < exp2 size)%N.

  Fixpoint encode''(pos : positive) (acc : bin) :=
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

  Fixpoint pad (b : bin) (l : nat) :=
    match l with
      | O    => b
      | S l' => false :: pad b l'
    end.

  Definition encode (n : N) :=
    let b := encode' n
    in pad b (size - (length b)).

  Fixpoint decode'' (b : bin) (l : nat) (acc : positive) :=
    match l with
      | O => (acc, b)
      | S l' =>
        match b with
          | nil         => (acc, nil)
          | false :: b' => decode'' b' l' (xO acc)
          | true  :: b' => decode'' b' l' (xI acc)
        end
    end.

  Fixpoint decode' (b : bin) (l : nat) {struct l} :=
    match l with
      | O    => (N0, b)
      | S l' =>
        match b with
          | nil         => (N0, nil)
          | false :: b' => decode' b' l'
          | true :: b'  =>
            match decode'' b' l' xH with
              | (pos, b'') => (Npos pos, b'')
            end
        end
    end.

  Definition decode (b : bin) := decode' b size.

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

  Theorem encode_correct :
    forall val ext, predicate val -> decode ((encode val) ++ ext) = (val, ext).
  Proof.
    unfold predicate, encode, decode.
    intros n ext P; apply encode'_size in P.
    unfold encode, decode in *.
    rewrite decode'_pad; eauto; clear P.
    destruct n; simpl; eauto; rewrite decode'_length.
    rewrite encode_correct'. reflexivity.
  Qed.

  Definition FixInt_encode (n : ({n | n < exp2 size})%N) :=
    match n with
      | exist n' _ => encode n'
    end.

  Lemma FixInt_decode'_size :
    forall s b, (fst (decode' b s) < exp2 s)%N.
  Proof.
    intro s; induction s as [ | s' ]; intuition.
    { admit. }
    { admit. }
  Qed.

  Definition FixInt_decode : bin -> ({n | n < exp2 size}%N).
  Proof.
    refine (fun b => exist _ (fst (decode b)) _).
    eapply FixInt_decode'_size.
  Defined.

  Global Instance FixInt_decoder
    : decoder (fun _ => True) FixInt_encode :=
    { decode := FixInt_decode;
      decode_correct := _ }.
  Proof.
    unfold encode_decode_correct, FixInt_decode, FixInt_encode.
    intros [data data_pf] _.
    Set Printing Implicit. idtac.
    assert (fst (decode (encode data)) = data).
    rewrite <- app_nil_r with (l:=encode data).
    rewrite encode_correct; eauto. (* rewrite <- H. *)
    (* apply proof_irrelevance *)
    admit.
  Defined.

(*
  Lemma decode''_shorten' :
    forall b l acc, length (snd (decode'' b l acc)) <= length b.
  Proof.
    induction b; destruct l; intuition eauto; simpl.
    econstructor; destruct a; eauto.
  Qed.

  Lemma decode'_shorten' :
    forall b l, length (snd (decode' b l)) <= length b.
  Proof.
    induction b; destruct l; intuition eauto; simpl.
    destruct a; eauto.
    pose proof (decode''_shorten' b l 1).
    destruct (decode'' b l 1); eauto.
  Qed.

  Theorem decode_shorten : decode_shorten decode.
  Proof.
    unfold decode_shorten, decode.
    destruct size; [ inversion size_nonzero | clear size_nonzero ].
    destruct ls; intuition eauto; destruct b; simpl.
    { pose proof (decode''_shorten' ls n 1).
      destruct (decode'' ls n 1); eauto. }
    { eapply decode'_shorten'. }
  Qed.

  Definition FixInt_encode_decode :=
    {| predicate_R := predicate;
       encode_R    := encode;
       decode_R    := decode;
       proof_R     := encode_correct;
       shorten_R   := decode_shorten |}. *)

End FixInt_encode_decode.

(*
  Variable FixNat_encode : forall size, {n | n < exp2 size} -> bin.
  Variable List1_encode : forall (A : Type) (encode_A : A -> bin) (size : nat), {ls : list A | length ls < exp2 size} -> bin.
  Variable List_encode : forall (A : Type) (encode_A : A -> bin), list A -> bin.
  Variable Nat_encode : nat -> bin.
  Variable Bin_encode : forall (A : Type) (encode_A : A -> bin), A * bin -> bin.

  Global Instance FixNat_decoder
         (size : nat)
    : decoder (fun _ => True) (FixNat_encode size).
  Admitted.
*)