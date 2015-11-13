Require Import Fiat.BinEncoders.take3.BigNat Compare_dec Fiat.BinEncoders.take3.Base.
Require Import Arith Omega.

Section List2.

  Context {A : Type}.
  Variable A_record : encode_decode_R A.

  (* terminator *)
  Variable halt : A.
  Variable halt_dec : forall a, {a = halt} + {a <> halt}.
  Hypothesis halt_pred : predicate_R A_record halt.

  Definition predicate (xs : list A) :=
    forall x, In x xs -> predicate_R A_record x /\ x <> halt.

  Fixpoint encode (data : list A) :=
    match data with
      | nil => encode_R A_record halt
      | cons s data' => encode_R A_record s ++ encode data'
    end.

  Fixpoint decode' (b : bin) (l : nat) :=
    match l with
      | O    => (nil, nil)
      | S l' =>
        let (x, b') := decode_R A_record b in
        if halt_dec x then
          (nil, b')
        else
          let (xs, b'') := decode' b' l' in
          (x :: xs, b'')
    end.

  Definition decode (b : bin) := decode' b (length b).

  Lemma encode_nonnil :
    forall val, predicate_R A_record val -> encode_R A_record val <> nil.
  Proof.
    intros val pred H.
    pose proof (proof_R A_record val (true :: nil) pred).
    pose proof (shorten_R A_record (true :: nil)).
    rewrite H in H0. simpl in H0.
    rewrite H0 in H1. inversion H1.
  Qed.

  Lemma encode_correct' :
    forall val l ext,  predicate val ->
                       length (encode val) <= l ->
                       decode' (encode val ++ ext) l = (val, ext).
  Proof.
    induction val; intuition; simpl in *.
    { destruct l.
      - pose proof (encode_nonnil _ halt_pred). destruct (encode_R A_record halt).
        congruence. inversion H0.
      - simpl; rewrite (proof_R A_record); eauto.
        destruct (halt_dec halt); eauto; congruence. }
    { unfold predicate in H. destruct l; simpl.
      - exfalso; eapply (encode_nonnil a).
        eapply H; constructor; eauto.
        destruct (encode_R A_record a); eauto; inversion H0.
      - assert (In a (a :: val)) by (constructor; eauto).
        pose proof (H a H1) as [? ?].
        rewrite <- app_assoc; rewrite (proof_R A_record); eauto.
        destruct (halt_dec a); try congruence.
        rewrite IHval; eauto.
        unfold predicate; intros; eapply H; econstructor 2; eauto.
        pose proof (encode_nonnil _ H2).
        destruct (encode_R A_record a); try congruence.
        simpl in *; apply le_S_n in H0.
        rewrite app_length in H0. omega. }
  Qed.

  Theorem encode_correct : encode_correct predicate encode decode.
  Proof.
    unfold encode_correct; intros.
    apply encode_correct'; eauto.
    rewrite app_length. apply le_plus_l.
  Qed.

   Definition binorder (b1 b2 : bin) := length b1 < length b2.
  Lemma binorder_wf' : forall n b, List.length b <= n -> Acc binorder b.
    unfold binorder; induction n; intuition eauto.
    constructor; intuition; inversion H; rewrite H2 in H0; inversion H0.
    inversion H; [ constructor; rewrite H1; intuition; apply IHn | apply IHn]; eauto.
  Defined.
  Lemma binorder_wf : well_founded binorder.
    unfold well_founded; intro; eapply binorder_wf'; eauto.
  Defined.
  Definition decode2 : bin -> (list A * bin) :=
    (Fix binorder_wf _
         (fun b rec =>
            let (x, b') := decode_R A_record b in
            if halt_dec x then
              (nil, b)
            else
              match lt_dec (length b') (length b) with
                | left pf =>
                  let (xs, b'') := rec b' pf in
                  (x :: xs, b'')
                | right _ =>
                  (nil, b')
              end)).

  Theorem encode_correct2 : Base.encode_correct predicate encode decode2.
   (* intro ls; induction ls; intuition eauto; simpl in *.
    { unfold decode, decode'. admit. }
    { *)
(*
      pose proof (proof_R A_record halt ext H0).
      unfold Fix, Fix_F.
_ _ _ (encode_R A_record halt ++ ext)).
    admit. *)
    hnf. intros val ext. generalize val. pattern ext.
    eapply well_founded_induction. eapply binorder_wf.
    intros.
    unfold decode2.
    rewrite Fix_eq.
  Qed.

  Lemma decode'_shorten' :
    forall l ls, length ls <= l -> length (snd (decode' ls l)) <= pred (length ls).
  Proof.
    induction l; intuition; simpl in *.
    { pose proof (shorten_R A_record ls); destruct (decode_R A_record ls).
      destruct (halt_dec a); eauto. specialize (IHl b).
      destruct (decode' b l). simpl.
      eapply Le.le_trans. eapply IHl. eapply Le.le_trans. eapply H0.
      destruct (length ls). eapply le_0_n. eapply le_S_n. eauto.
      eapply Le.le_trans. eapply le_pred_n. eauto. }
  Qed.

  Theorem decode_shorten : decode_shorten decode.
  Proof.
    unfold decode_shorten; intros.
    apply decode'_shorten'; eauto.
  Qed.

  Definition List2_encode_decode :=
    {| predicate_R := predicate;
       encode_R    := encode;
       decode_R    := decode;
       proof_R     := encode_correct;
       shorten_R   := decode_shorten |}.
End List2.

(*

  Program Fixpoint decode (b : bin) {measure (length b)} :=
    let (x, b') := decode_R A_record b in
    if halt_dec x then
      (nil, b)
    else
      match lt_dec (length b') (length b) with
        | left pf =>
          let (xs, b'') := decode b' in
          (x :: xs, b'')
        | right _ =>
          (nil, b')
      end.

  Definition binorder (b1 b2 : bin) := length b1 < length b2.
  Lemma binorder_wf' : forall n b, List.length b <= n -> Acc binorder b.
    unfold binorder; induction n; intuition eauto.
    constructor; intuition; inversion H; rewrite H2 in H0; inversion H0.
    inversion H; [ constructor; rewrite H1; intuition; apply IHn | apply IHn]; eauto.
  Defined.
  Lemma binorder_wf : well_founded binorder.
    unfold well_founded; intro; eapply binorder_wf'; eauto.
  Defined.
  Definition decode : bin -> (list A * bin) :=
    (Fix binorder_wf _
         (fun b rec =>
            let (x, b') := decode_R A_record b in
            if halt_dec x then
              (nil, b)
            else
              match lt_dec (length b') (length b) with
                | left pf =>
                  let (xs, b'') := rec b' pf in
                  (x :: xs, b'')
                | right _ =>
                  (nil, b')
              end)).


    intro ls; induction ls; intuition eauto; simpl in *.
    { unfold decode, decode'. admit. }
    {
(*
      pose proof (proof_R A_record halt ext H0).
      unfold Fix, Fix_F.
_ _ _ (encode_R A_record halt ++ ext)).
    admit.
    eapply well_founded_induction. eauto. ; intros; [ eapply binorder_wf | | eapply nil ]. *)
  Qed.
*)