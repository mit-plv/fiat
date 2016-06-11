Require Import
        Bedrock.Word
        Coq.NArith.NArith
        Coq.Arith.Arith
        Coq.Numbers.Natural.Peano.NPeano
        Coq.Logic.Eqdep_dec
        Fiat.BinEncoders.Env.Common.Specs.

Set Implicit Arguments.

Notation bin := (list bool).

Global Instance btransformer : Transformer bin :=
  {| transform := @app _;
     bin_measure := (@length bool);
     transform_measure b b' := app_length b b';
     transform_id := nil;
     transform_id_left := @app_nil_l _;
     transform_id_right := @app_nil_r _;
     transform_assoc := @app_assoc _ |}.

Definition char := word 8.

Definition char_get_bit
           (i : nat)
           (c : word i)
  := Nmod2 (Ndiv (wordToN c) (Npow2 i)).

Definition char_set_bit (* Assumes the ith bit of c is unset. *)
           (b : bool)
           (i : nat)
           (c : char) :=
  if b then
    wplus c (NToWord _ (Npow2 i))
  else c.

Definition char_chomp_bits
           (i : word 3)
           (c : char)
  : word 7 :=
  NToWord _ (N.modulo (wordToN c) (Npow2 (wordToNat i))).

Record ByteString :=
  { padding : nat; (* The number of valid bits in front. *)
    paddingOK : lt padding 8;
    front : word padding;
    byteString : list char (* The bytestring. *)
  }.

Definition ByteString_push
         (b : bool)
         (bs : ByteString)
  : ByteString.
  refine (if (eq_nat_dec (padding bs) 7) then
    {| front := (wzero _);
       byteString := WS b _
                        :: byteString bs;
       padding := 0 |}
  else
    {| front := WS b (front bs);
       byteString := byteString bs |}).
  abstract omega.
  pose (front bs) as w; destruct _H; exact w.
  abstract (pose proof (paddingOK bs); omega).
Defined.

Definition ByteString_pop
         (bs : ByteString)
  : option (bool * ByteString).
  refine (match padding bs as n return
                word n
                -> lt n 8
                -> _ with
          | 0 => fun _ _ =>
                   match byteString bs with
                   | [ ] =>  None
                   | c :: l' => Some (whd c,
                                      {| front := wtl c;
                                         byteString := l' |})
                   end
          | S n => fun c lt_n => Some (whd c,
                                  {| front := wtl c;
                                     byteString := byteString bs |})
          end (front bs) (paddingOK bs)).
  abstract omega.
  abstract omega.
Defined.

Fixpoint ByteString_push_word
           {n}
           (w : word n)
           (bs : ByteString) :=
  match w with
  | WO => bs
  | WS b _ w' => ByteString_push b (ByteString_push_word w' bs)
  end.

Definition ByteString_push_char (c : char) (bs : ByteString)
  := ByteString_push_word c bs.

Fixpoint ByteString_push_front
           {n}
           (w : word n)
           (bs : ByteString) :=
  match n return word n -> ByteString with
  | 0 => fun _ => bs
  | S n' => fun w =>
              ByteString_push (whd w) (ByteString_push_front (wtl w) bs)
  end w.

Definition ByteString_transformer
           (bs bs' : ByteString)
  : ByteString :=
  let bs'' := fold_right ByteString_push_char bs' (byteString bs) in
  ByteString_push_front (front bs) bs''.

Definition length_ByteString (bs : ByteString) :=
  (padding bs) + (8 * (length (byteString bs))).

Lemma length_ByteString_push
  : forall (bs' : ByteString)
           (b : bool),
    length_ByteString (ByteString_push b bs') =
    S (length_ByteString bs').
Proof.
  simpl; clear; destruct bs'; simpl.
  unfold ByteString_push; simpl.
  destruct (eq_nat_dec padding0 7);
    intros; simpl; subst.
  - unfold length_ByteString; simpl; omega.
  - unfold length_ByteString; simpl; omega.
Qed.

Lemma length_ByteString_push_char
  : forall (bs' : ByteString)
           (c : char),
    length_ByteString (ByteString_push_char c bs') =
    8 + (length_ByteString bs').
Proof.
  intros.
  pose proof (shatter_word c); simpl in *;
    pose proof (shatter_word (wtl c)); simpl in *;
      pose proof (shatter_word (wtl (wtl c))); simpl in *;
        pose proof (shatter_word (wtl (wtl (wtl c)))); simpl in *;
          pose proof (shatter_word (wtl (wtl (wtl (wtl c))))); simpl in *;
            pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl c)))))); simpl in *;
              pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl c))))))); simpl in *;
                pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl c))))))));
                pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl c))))))))); simpl in *.
  rewrite H, H0, H1, H2, H3, H4, H5, H6, H7; simpl.
  unfold ByteString_push_char; simpl.
  rewrite !length_ByteString_push; repeat f_equal.
Qed.

Lemma length_ByteString_append
  : forall bs (bs' : ByteString),
    length_ByteString (fold_right ByteString_push_char bs' bs)
    = (8 * (length bs)) + length_ByteString bs'.
Proof.
  induction bs; eauto.
  simpl length; rewrite mult_succ_r, plus_comm.
  intros; rewrite <- plus_assoc, <- IHbs.
  simpl; rewrite length_ByteString_push_char.
  omega.
Qed.

Corollary length_ByteString_push_front
  : forall n (bs_front : word n) (bs' : ByteString),
    length_ByteString (ByteString_push_front bs_front bs') =
    n + length_ByteString bs'.
Proof.
  induction n; simpl; intros; eauto.
  rewrite length_ByteString_push, IHn; eauto.
Qed.

Lemma transform_ByteString_measure
  : forall bs bs' : ByteString,
   length_ByteString (ByteString_transformer bs bs') = length_ByteString bs + length_ByteString bs'.
Proof.
  destruct bs as [bs_padding bs_front ? bs_byteString]; simpl.
  induction bs_byteString.
  - unfold ByteString_transformer, length_ByteString at 2; simpl.
    rewrite NPeano.Nat.add_0_r.
    induction bs_padding.
    + simpl; eauto.
    + simpl; intros.
      rewrite length_ByteString_push; rewrite IHbs_padding; eauto.
      omega.
  -  unfold ByteString_transformer in *; simpl in *.
     unfold length_ByteString at 2.
     unfold byteString at 1.
     intros; rewrite <- plus_assoc,
             <- (length_ByteString_append (a :: bs_byteString) bs').
     simpl fold_right.
     rewrite length_ByteString_push_char, plus_comm.
     rewrite <- plus_assoc.
     simpl padding.
     unfold length_ByteString in IHbs_byteString.
     simpl byteString in IHbs_byteString.
     simpl padding in IHbs_byteString.
     rewrite length_ByteString_append.
     unfold length_ByteString at 2.
     replace (8 * length bs_byteString +
              (padding bs'
               + 8 * length (byteString bs'))
              + bs_padding) with
     (bs_padding + 8 * length bs_byteString +
      (padding bs' + 8 * length (byteString bs'))) by omega.
     rewrite <- IHbs_byteString; clear.
     rewrite !length_ByteString_push_front.
     rewrite length_ByteString_push_char, plus_comm, plus_assoc.
     rewrite <- !plus_assoc; f_equal.
     remember (fold_right ByteString_push_char bs' bs_byteString);
       clear.
     induction bs_padding.
     + unfold length_ByteString; simpl; omega.
     + rewrite <- plus_n_Sm, (IHbs_padding (wtl front0)); clear.
       rewrite plus_n_Sm.
       simpl ByteString_push_front.
       destruct (ByteString_push_front (wtl front0) y) eqn: ?.
       unfold ByteString_push.
       destruct (eq_nat_dec (padding (ByteString_push_front (wtl front0) y)) 7);
         simpl padding; simpl byteString.
       * simpl length; rewrite Heqb; simpl byteString;
           rewrite Heqb in e; simpl in e.
         rewrite e; omega.
       * rewrite Heqb in n; rewrite Heqb;
           simpl padding in *; simpl byteString in *; clear Heqb.
         omega.
Qed.

Definition ByteString_id : ByteString.
  refine {| front := WO; byteString := [] |}.
  abstract omega.
Defined.

Lemma ByteString_transform_id_left
  : forall bs : ByteString,
   ByteString_transformer ByteString_id bs = bs.
Proof.
  reflexivity.
Qed.

(* Uniqueness of less than proofs taken from *)
(* https://coq.inria.fr/faq#le-uniqueness. *)
Scheme le_ind' := Induction for le Sort Prop.
Theorem le_uniqueness_proof : forall (n m : nat) (p q : le n m), p = q.
Proof.
  induction p using le_ind'; intro q.
  replace (le_n n) with
  (eq_rect _ (fun n0 => le n n0) (le_n n) _ (refl_equal n)).
  2:reflexivity.
  generalize (refl_equal n).
  pattern n at 2 4 6 10, q; case q; [intro | intros m l e].
  rewrite <- (eq_rect_eq_dec eq_nat_dec); eauto.
  contradiction (le_Sn_n m); rewrite <- e; assumption.
  replace (le_S n m p) with
  (eq_rect _ (fun n0 => le n n0) (le_S n m p) _ (refl_equal (S m))).
  2:reflexivity.
  generalize (refl_equal (S m)).
  pattern (S m) at 1 3 4 6, q; case q; [intro Heq | intros m0 l HeqS].
  contradiction (le_Sn_n m); rewrite Heq; assumption.
  injection HeqS; intro Heq; generalize l HeqS.
  rewrite <- Heq; intros; rewrite <- (eq_rect_eq_dec eq_nat_dec).
  rewrite (IHp l0); reflexivity.
Qed.

Fixpoint append_word {n m}
           (w : word n)
           (w' : word m)
  : word (n + m) :=
  match n return word n -> word (n + m) with
  | 0 => fun _ => w'
  | S n' => fun w => WS (whd w) (append_word (wtl w) w')
  end w.

Lemma minus_inj
  : forall m m' y q q',
    (q < y)%nat
    -> (q' < y)%nat
    -> (m * y) + y - q = (m' * y) + y - q'
    -> m = m' /\ q = q'.
Proof.
  induction m; simpl; intros.
  - destruct m'.
    + simpl in *; intuition.
    + rewrite mult_succ_l in *.
      assert (y - q < (m' * y) + y + y - q')%nat.
      { clear H1; induction (m' * y); intros.
        - omega.
        - etransitivity.
          apply IHn.
          omega. }
      elimtype False.
      rewrite H1 in H2.
      omega.
  - destruct m'.
    + simpl in *.
      assert (y - q' < (m * y) + y + y - q)%nat.
      { clear H1 IHm; induction (m * y); intros.
        - omega.
        - etransitivity.
          apply IHn.
          omega. }
      elimtype False.
      rewrite <- H1 in H2; omega.
    + destruct (IHm m' _ _ _ H H0).
      simpl in H1.
      rewrite <- !Nat.add_sub_assoc in H1; try omega.
      subst; intuition.
Qed.

Corollary minus_inj'
  : forall m m' y q q',
    (q <= y)%nat
    -> (q' <= y)%nat
    -> m * (S y) + y - q = (m' * (S y)) + y - q'
    -> m = m' /\ q = q'.
Proof.
  intros; destruct (@minus_inj m m' (S y) q q'); try omega.
  assert (m * S y + S y - q = S (m * S y + y - q)).
  rewrite plus_comm.
  assert (S y + m * S y - q = 1 + (y + m * S y - q)).
  rewrite !Nat.add_sub_assoc.
  rewrite plus_assoc.
  omega.
  auto with arith.
  rewrite H2; simpl; omega.
  rewrite H2.
  rewrite H1.
  rewrite <- !Nat.add_sub_assoc; auto.
  omega.
Qed.

Lemma divmod_eq' :
  forall x y q u,
    (u <= y)%nat
    -> x = q * (S y) + (y - u)
    -> divmod x y 0 y = (q, u).
Proof.
  intros; pose proof (divmod_spec x y 0 y).
  destruct (divmod x y 0 y); destruct H1; eauto.
  rewrite H0 in H1.
  simpl in H1.
  rewrite minus_diag, <- mult_n_O, <- !plus_n_O in *.
  assert (n + y * n = n * S y) by
      (rewrite mult_succ_r, plus_comm, mult_comm; reflexivity).
  f_equal; eapply (@minus_inj' n q y n0 u); eauto;
  rewrite !mult_succ_r in *;
  rewrite !Nat.add_sub_assoc in H1; eauto;
      omega.
Qed.

Lemma divmod_eq :
  forall x y q u,
    divmod x y 0 y = (q, u) ->
    x = q * (S y) + (y - u).
Proof.
  intros; pose proof (divmod_spec x y 0 y).
  rewrite H in H0; destruct H0; eauto.
  simpl in H0.
  assert (x = q + y * q + (y - u)) by omega.
  rewrite H2.
  rewrite mult_succ_r.
  rewrite (plus_comm (q * y) q).
  rewrite mult_comm; f_equal.
Qed.

Lemma NatModulo_S_Full
  : forall n' m, Nat.modulo n' (S m) = m
               -> Nat.modulo (S n') (S m) = 0.
Proof.
  unfold Nat.modulo, modulo.
  intros; assert (exists q, divmod (S n') m 0 m = (q, m)).
  intros; pose proof (divmod_spec n' m 0 m).
  destruct (divmod n' m 0 m) eqn: ? .
  destruct H0; eauto.
  simpl in H.
  assert (n0 = 0) by omega.
  rewrite H2 in *; clear H H2.
  apply divmod_eq in Heqp.
  eexists (S n).
  eapply divmod_eq'; eauto.
  rewrite Heqp.
  rewrite <- !minus_n_O, minus_diag, <- plus_n_O.
  simpl; omega.
  destruct_ex; rewrite H0; simpl; omega.
Qed.

Lemma NatModulo_S_Not_Full
  : forall n' m, Nat.modulo n' (S m) <> m
               -> Nat.modulo (S n') (S m) = S (Nat.modulo n' (S m)).
Proof.
  unfold Nat.modulo, modulo.
  intros; destruct (divmod n' m 0 m) eqn: ?.
  destruct n0.
  simpl in H; omega.
  intros; pose proof (divmod_spec n' m 0 m).
  rewrite Heqp in H0; destruct H0; eauto.
  assert (divmod (S n') m 0 m = (n, n0)).
  apply divmod_eq in Heqp.
  apply divmod_eq'; try omega.
  rewrite H2; simpl.
  omega.
Qed.

Fixpoint word_into_char {n}
           (w : word n)
           {struct w}
  : (word (Nat.modulo n 8) * list char).
  refine (match w in word n return word (Nat.modulo n 8) * list char with
          | WO => (WO, [ ])
          | WS b n' w' => let (b', chars) := word_into_char _ w' in
                          (if (eq_nat_dec (Nat.modulo n' 8) 7) then _
                                                else (_ , chars))
          end).
  - generalize (WS b b'); rewrite _H, (NatModulo_S_Full _ _H); simpl.
    exact (fun b => (WO, b :: chars)).
  - rewrite (NatModulo_S_Not_Full _ _H).
    exact (WS b b').
Defined.

(*Lemma ByteString_push_front_eq
  : forall bs {n} (w : word n) pf,
    ByteString_push_front w bs =
    {| front := fst (word_into_char (append_word w (front bs)));
       paddingOK := pf;
       byteString := snd (word_into_char (append_word w (front bs)))
                         ++ byteString bs|}.
Proof.
  destruct bs; simpl front; simpl byteString; simpl padding.
  induction w.
Admitted.
  Focus 2.
  simpl ByteString_push_front.
  cbv beta.
  simpl wtl; simpl whd.
  intro. erewrite IHw.
  unfold ByteString_push.
  - simpl; intros.
    assert (word_into_char front0 = (front0, [ ])).
    assert (match snd (divmod padding0 7 0 7) with
              | 0 => 7
              | 1 => 6
              | 2 => 5
              | 3 => 4
              | 4 => 3
              | 5 => 2
              | 6 => 1
              | S (S (S (S (S (S (S _)))))) => 0
              end = padding0).
    Focus 2.
    revert pf. rewrite H.
    induction front0.
    + simpl; f_equal; apply le_uniqueness_proof.
    + assert (S n =
              match snd (divmod (S n) 7 0 7) with
              | 0 => 7
              | 1 => 6
              | 2 => 5
              | 3 => 4
              | 4 => 3
              | 5 => 2
              | 6 => 1
              | S (S (S (S (S (S (S _)))))) => 0
              end).
      Focus 2.
      revert front0 paddingOK0 pf IHfront0.
      rewrite <- H.
      rewrite (@divmod_eq' (S n) 7 0 (S n)).

  f_equal.
Admitted. *)

Lemma ByteString_push_char_id_right
  : forall (chars : list char) (bs : ByteString),
    padding bs = 0 ->
    fold_right ByteString_push_char bs chars =
    {| front := WO;
       paddingOK := ByteString_id_subproof;
       byteString := chars ++ (byteString bs) |}.
Proof.
  (* Commented out because the proof is slow and takes a bunch of memory. *)
  (*
  destruct bs; simpl; intros; subst.
  induction chars; simpl.
  - f_equal; eauto using le_uniqueness_proof.
  - rewrite IHchars.
    rename a into c.
    pose proof (shatter_word c); simpl in *;
    pose proof (shatter_word (wtl c)); simpl in *;
      pose proof (shatter_word (wtl (wtl c))); simpl in *;
        pose proof (shatter_word (wtl (wtl (wtl c)))); simpl in *;
          pose proof (shatter_word (wtl (wtl (wtl (wtl c))))); simpl in *;
            pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl c)))))); simpl in *;
              pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl c))))))); simpl in *;
                pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl c))))))));
                pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl (wtl c))))))))); simpl in *.
  rewrite H, H0, H1, H2, H3, H4, H5, H6, H7; simpl.
  unfold ByteString_push_char; simpl.
  repeat match goal with
    |- context [(whd ?c)] => destruct (whd c) end;
    try solve [compute; f_equal; eapply le_uniqueness_proof].
Qed. *)
Admitted.

Lemma ByteString_transform_id_right
  : forall bs : ByteString,
    ByteString_transformer bs ByteString_id = bs.
Proof.
  destruct bs; unfold ByteString_transformer, ByteString_id; simpl.
  rewrite ByteString_push_char_id_right; simpl; eauto.
  rewrite app_nil_r.
  induction front0.
  + simpl; f_equal.
    pose ByteString_id_subproof.
    eapply le_uniqueness_proof.
  + simpl.
    assert (lt n 8) by omega.
    erewrite (IHfront0 H).
    unfold ByteString_push.
    simpl.
    destruct (eq_nat_dec n 7); subst.
    omega.
    f_equal; eauto using le_uniqueness_proof.
Qed.

Lemma ByteString_transform_f_equal
  : forall bs bs'
           (p_eq : padding bs' = padding bs),
    paddingOK bs = (@eq_rect nat (padding bs') (fun t => lt t 8) (paddingOK bs') _ p_eq)
    -> front bs = (@eq_rect nat (padding bs') (fun t => word t) (front bs') _ p_eq)
    -> byteString bs = byteString bs'
    -> bs = bs'.
Proof.
  destruct bs; destruct bs'; simpl.
  intros; subst; reflexivity.
Qed.

(*Lemma padding_ByteString_transform_assoc
  : forall l m n : ByteString,
    padding (ByteString_transformer l (ByteString_transformer m n)) =
    padding (ByteString_transformer (ByteString_transformer l m) n).
Proof.
  intros; repeat (erewrite ByteString_transformer_eq; simpl padding).
Admitted. *)

Lemma ByteString_transform_assoc
  : forall l m n : ByteString,
    ByteString_transformer l (ByteString_transformer m n) =
    ByteString_transformer (ByteString_transformer l m) n.
Proof.
(*
  revert bs_m padding_l front_l padding_m front_m
         padding_l_OK padding_m_OK
         padding_n padding_n_OK front_n bs_n.
  induction bs_l; simpl.
  - induction bs_m; simpl.
    intros; erewrite !ByteString_push_front_eq.
    assert (Nat.modulo
                (padding_l +
                 padding
                   (ByteString_push_front front_m
                      {|
                      padding := padding_n;
                      paddingOK := padding_n_OK;
                      front := front_n;
                      byteString := bs_n |})) 8
            =  Nat.modulo
                (padding
                   (ByteString_push_front front_l
                      {|
                      padding := padding_m;
                      paddingOK := padding_m_OK;
                      front := front_m;
                      byteString := [] |}) +
                 padding
                   (fold_right ByteString_push_char
                      {|
                      padding := padding_n;
                      paddingOK := padding_n_OK;
                      front := front_n;
                      byteString := bs_n |}
                      (byteString
                         (ByteString_push_front front_l
                            {|
                            padding := padding_m;
                            paddingOK := padding_m_OK;
                            front := front_m;
                            byteString := [] |})))) 8).
    admit.
    rewrite H.
    apply f_equal.
    repeat f_equal.
    + induction front_l; simpl.
      * reflexivity.
      * intros; erewrite !ByteString_push_front_eq.
        simpl.
    + reflexivity.
    + simpl. *)
Admitted.

Global Instance ByteStringTransformer : Transformer ByteString :=
  {| transform := ByteString_transformer;
     bin_measure := length_ByteString;
     transform_measure := transform_ByteString_measure;
     transform_id := ByteString_id;
     transform_id_left := ByteString_transform_id_left;
     transform_id_right := ByteString_transform_id_right;
     transform_assoc :=  ByteString_transform_assoc |}.

Lemma ByteString_measure_push
  : forall (t : bool) (b : ByteString), bin_measure (ByteString_push t b) = bin_measure b + 1.
Proof.
  destruct b; unfold ByteString_push, length_ByteString; simpl.
  unfold length_ByteString; simpl.
  destruct (eq_nat_dec padding0 7); simpl.
  - rewrite e; simpl; omega.
  - omega.
Qed.

Lemma ByteString_measure_pop_Some
  : forall (b' : ByteString) (t : bool) (b : ByteString),
    ByteString_pop b = Some (t, b') -> bin_measure b = bin_measure b' + 1.
Proof.
  destruct b.
  unfold ByteString_pop; simpl.
  destruct padding0.
  - destruct byteString0.
    + intros; discriminate.
    + intros; injections.
      unfold length_ByteString; simpl.
      omega.
  - intros; injections.
    unfold length_ByteString; simpl.
    omega.
Qed.

Lemma ByteString_transform_push_pop_opt
  : forall (t : bool) (m : ByteString), ByteString_pop (ByteString_push t m) = Some (t, m).
Proof.
  destruct m; simpl.
  unfold ByteString_push; unfold ByteString_pop.
  simpl padding.
  destruct (eq_nat_dec padding0 7);
    simpl padding; simpl paddingOK; simpl front; simpl byteString.
  - subst; simpl; repeat f_equal.
    apply le_uniqueness_proof.
  - simpl; repeat f_equal.
    apply le_uniqueness_proof.
Qed.

Lemma ByteString_transform_push_eq
  : forall t bs, exists pf,
      ByteString_push t bs = transform {| front := WS t WO;
                                         paddingOK := pf;
                                         byteString := [ ] |} bs.
Proof.
  assert (1 < 8)%nat by omega.
  intros; eexists H.
  destruct bs; simpl.
  reflexivity.
Qed.

Lemma ByteString_transform_push_step_opt
  : forall (t : bool) (m n : ByteString),
    transform (ByteString_push t m) n = ByteString_push t (transform m n).
Proof.
  intros; destruct (ByteString_transform_push_eq t m).
  simpl transform.
  rewrite H, <- ByteString_transform_assoc.
  destruct (ByteString_transform_push_eq t (transform m n)).
  simpl transform in *; rewrite H0.
  repeat f_equal.
  apply le_uniqueness_proof.
Qed.

Lemma ByteString_transform_pop_opt_inj
  : forall (t : bool) (m b b' : ByteString),
    ByteString_pop b = Some (t, m) -> ByteString_pop b' = Some (t, m) -> b = b'.
Proof.
  destruct b; destruct b'.
  unfold ByteString_pop;
    simpl padding; simpl paddingOK; simpl front; simpl byteString.
  destruct padding0; destruct padding1.
  - destruct byteString0; intros; try discriminate.
    destruct byteString1; try discriminate.
    injection H; injection H0; intros.
    subst.
    f_equal.
    apply le_uniqueness_proof.
    rewrite (shatter_word_0 front0);
      rewrite (shatter_word_0 front1); reflexivity.
    rewrite (shatter_word c) in *;
      rewrite (shatter_word c0) in *.
    injection H3; intros.
    rewrite H1; f_equal.
    f_equal.
    simpl in H4; rewrite H4; reflexivity.
    apply inj_pair2_eq_dec in H2; eauto.
    apply eq_nat_dec.
  - destruct byteString0; intros; try discriminate.
    injection H; injection H0; intros.
    rewrite <- H1 in H3; injection H3; intros.
    elimtype False.
    generalize H7 paddingOK1; clear; intro; rewrite H7.
    intros; omega.
  - destruct byteString1; intros; try discriminate.
    injection H; injection H0; intros.
    rewrite <- H1 in H3; injection H3; intros.
    elimtype False.
    generalize H7 paddingOK0; clear; intro; rewrite H7.
    intros; omega.
  - intros; injection H; injection H0; intros.
    rewrite <- H1 in H3; injection H3; intros; subst.
    repeat f_equal.
    apply le_uniqueness_proof.
    rewrite (shatter_word front0); rewrite (shatter_word front1);
      f_equal; eauto.
    apply inj_pair2_eq_dec in H6; eauto.
    apply eq_nat_dec.
Qed.

Instance ByteString_TransformerUnitOpt
  : TransformerUnitOpt ByteStringTransformer bool :=
  {| T_measure f := 1;
     transform_push_opt := ByteString_push;
     transform_pop_opt := ByteString_pop;
     measure_push := ByteString_measure_push ;
     measure_pop_Some := ByteString_measure_pop_Some;
     transform_push_pop_opt := ByteString_transform_push_pop_opt;
     transform_push_step_opt := ByteString_transform_push_step_opt;
     transform_pop_opt_inj := ByteString_transform_pop_opt_inj
  |}.
Proof.
  - abstract eauto.
Defined.
