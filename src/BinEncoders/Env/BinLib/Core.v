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
  { padding : nat;
    front : word padding;
    paddingOK : lt padding 8;
    byteString : list char (* The bytestring. *)
  }.

Local Ltac destruct_matches :=
  repeat match goal with
         | [ |- appcontext[match ?e with _ => _ end] ] => destruct e eqn:?
         end.

Definition ByteString_push
         (b : bool)
         (bs : ByteString)
  : ByteString.
  refine (if (eq_nat_dec (padding bs) 7) then
            {| front := WO;
               byteString := WS b _
                                :: byteString bs |}
  else
    {| front := WS b (front bs);
       padding := S (padding bs);
       byteString := byteString bs |}).
  abstract omega.
  { pose proof (front bs) as w; generalize dependent (padding bs).
    intros ?? w; subst; exact w. }
  { abstract (pose proof (paddingOK bs); omega). }
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
  match n return word n -> ByteString with
  | 0 => fun _ => bs
  | S n' => fun w =>
              ByteString_push (whd w) (ByteString_push_word (wtl w) bs)
  end w.

Definition ByteString_push_char (c : char) (bs : ByteString)
  := ByteString_push_word c bs.

Definition ByteString_transformer
           (bs bs' : ByteString)
  : ByteString :=
  let bs'' := fold_right ByteString_push_char bs' (byteString bs) in
  ByteString_push_word (front bs) bs''.

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

Corollary length_ByteString_push_word
  : forall n (bs_front : word n) (bs' : ByteString),
    length_ByteString (ByteString_push_word bs_front bs') =
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
     rewrite !length_ByteString_push_word.
     rewrite length_ByteString_push_char, plus_comm, plus_assoc.
     rewrite <- !plus_assoc; f_equal.
     remember (fold_right ByteString_push_char bs' bs_byteString);
       clear.
     induction bs_padding.
     + unfold length_ByteString; simpl; omega.
     + rewrite <- plus_n_Sm, (IHbs_padding (wtl bs_front)); clear.
       rewrite plus_n_Sm.
       simpl ByteString_push_word.
       unfold ByteString_push.
       repeat match goal with
              | _ => progress simpl in *
              | _ => progress subst
              | _ => progress unfold eq_rec_r, eq_rec, eq_rect, eq_sym
              | _ => progress destruct_matches
              | [ H : context[padding ?x] |- _ ] => destruct x eqn:?
              | _ => omega
              end.
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

(* kludgy 8.4/8.5 compatibility hack *)
Module Import Nat_NPeano.
  Import Nat NPeano.
  Hint Unfold modulo : modulo_db.
End Nat_NPeano.
Module Import NPeano_Nat.
  Import NPeano Nat.
  Hint Unfold modulo : modulo_db.
End NPeano_Nat.

Import Nat.

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

Corollary divmod_eq'' :
  forall x y,
    x = (y - (snd (divmod x y 0 y))) + (fst (divmod x y 0 y)) * (S y).
Proof.
  intros; rewrite plus_comm; destruct (divmod x y 0 y) eqn: ? .
  simpl; eapply divmod_eq; assumption.
Defined.

Lemma NatModulo_S_Full
  : forall n' m, Nat.modulo n' (S m) = m
               -> Nat.modulo (S n') (S m) = 0.
Proof.
  autounfold with modulo_db.
  intros; assert (exists q, divmod (S n') m 0 m = (q, m)).
  intros; pose proof (divmod_spec n' m 0 m).
  destruct (divmod n' m 0 m) eqn: ? .
  destruct H0; eauto.
  simpl in H.
  assert (n0 = 0) by (simpl in H; omega).
  rewrite H2 in *; clear H H2.
  apply divmod_eq in Heqp.
  eexists (S n).
  eapply divmod_eq'; eauto.
  rewrite Heqp.
  rewrite <- !minus_n_O, minus_diag, <- plus_n_O.
  simpl; omega.
  destruct_ex; simpl in *; rewrite H0; simpl; omega.
Qed.

Lemma NatModulo_S_Not_Full
  : forall n' m, Nat.modulo n' (S m) <> m
               -> Nat.modulo (S n') (S m) = S (Nat.modulo n' (S m)).
Proof.
  autounfold with modulo_db.
  intros; destruct (divmod n' m 0 m) eqn: ?.
  destruct n0.
  simpl in H; simpl in *; omega.
  intros; pose proof (divmod_spec n' m 0 m).
  rewrite Heqp in H0; destruct H0; eauto.
  assert (divmod (S n') m 0 m = (n, n0)).
  apply divmod_eq in Heqp.
  apply divmod_eq'; try omega.
  simpl in *; rewrite H2; simpl.
  omega.
Qed.

Fixpoint word_split {n m}
         (w : word (n + m))
         {struct n}
  : word n * word m :=
  match n return word (n + m) -> word n * word m with
  | 0 => fun w => (WO, w)
  | S n' => fun w' =>
              let (wn, wm) := word_split (wtl w') in
              (WS (whd w') wn, wm)
  end w.

Fixpoint word_into_ByteString' {n}
         (w : word (n * 8))
  : list char :=
  match n return word (n * 8) -> list char with
  | 0 => fun _ => [ ]
  | S n' => fun w => let (c, w') := @word_split 8 (n' * 8) w in
                     c :: (word_into_ByteString' w')
  end w.

Definition word_into_ByteString
           {n m}
           (H : lt n 8)
           (w : word (n + (m * 8)))
  : ByteString :=
  {| front := fst (word_split w);
     paddingOK := H;
     byteString := word_into_ByteString' (snd (@word_split n _ w)) |}.

Definition list_into_ByteString
           (l : list bool)
  : ByteString :=
  fold_right ByteString_push ByteString_id l.

Lemma mult_succ_plus_comm_fuse
  : forall n m,
    S n * m = m + n * m.
Proof.
  intros; rewrite mult_succ_l, plus_comm; reflexivity.
Qed.

Fixpoint ByteString_into_word'
           (chars : list char)
           {struct chars} : word (length chars * 8).
Proof.
  refine (match chars return word (length chars * 8) with
          | [ ] => WO
          | char' :: chars' => _
          end).
  simpl length; rewrite mult_succ_plus_comm_fuse.
    exact (append_word char' (ByteString_into_word' chars')).
Defined.

Definition ByteString_into_word
           (bs : ByteString)
  : word (padding bs + (length (byteString bs) * 8)) :=
  append_word (front bs) (ByteString_into_word' (byteString bs)).


Fixpoint wordToList {n}
           (w : word n)
  : list bool :=
  match n return word n -> list bool with
  | 0 => fun _ => [ ]
  | S n' => fun w => whd w :: wordToList (wtl w)
  end w.

Fixpoint ByteString_into_list'
           (chars : list char)
           {struct chars} : list bool :=
  match chars return list bool with
  | [ ] => [ ]
  | char' :: chars' =>
    app (wordToList char')
        (ByteString_into_list' chars')
  end.

Definition ByteString_into_list
           (bs : ByteString)
  : list bool :=
  app (wordToList (front bs)) (ByteString_into_list' (byteString bs)).

Lemma ByteString_f_equal
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

Lemma succ_eq_rect
  : forall b (n : nat) w m (e : n = m),
    WS b (eq_rect n word w m e) = eq_rect (S n) word (WS b w) (S m) (f_equal S e).
Proof.
  induction w.
  - intros; subst; simpl; eauto.
  - intros; subst.
    simpl; reflexivity.
Qed.

Lemma ByteString_into_word'_eq
  : forall bs,
    bs = word_into_ByteString' (ByteString_into_word' bs).
Proof.
  induction bs; simpl; f_equal.
  - rename a into c.
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
    repeat f_equal;
      unfold eq_rec_r, eq_rec; rewrite <- eq_rect_eq_dec;
        simpl; eauto using eq_nat_dec.
  - rename a into c.
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
      unfold eq_rec_r, eq_rec; rewrite <- eq_rect_eq_dec;
        simpl; eauto using eq_nat_dec.
Qed.

Lemma ByteString_into_word_eq
  : forall bs,
    bs = word_into_ByteString (paddingOK bs) (ByteString_into_word bs).
Proof.
  destruct bs; simpl.
  unfold word_into_ByteString, ByteString_into_word.
  f_equal.
  - destruct padding0 as [ | [ | [ | [ | [ | [ | [ | [ | ] ] ] ] ] ] ] ].
    + pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
        eauto.
    + pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
        pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
        eauto.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
        pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
          let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
        eauto.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      let H'' := fresh in pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
      let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl front0)))) as H'; simpl in H'; rewrite H';
        eauto.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      let H'' := fresh in pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
      let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl front0)))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl front0))))) as H'; simpl in H'; rewrite H';
     eauto.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      let H'' := fresh in pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
      let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl front0)))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl front0))))) as H'; simpl in H'; rewrite H';
let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl front0)))))) as H'; simpl in H'; rewrite H';
                           eauto.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      let H'' := fresh in pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
      let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl front0)))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl front0))))) as H'; simpl in H'; rewrite H';
       let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl front0)))))) as H'; simpl in H'; rewrite H';
let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl front0))))))) as H'; simpl in H'; rewrite H';
                     eauto.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      let H'' := fresh in pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
      let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl front0)))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl front0))))) as H'; simpl in H'; rewrite H';
       let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl front0)))))) as H'; simpl in H'; rewrite H';
let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl front0))))))) as H'; simpl in H'; rewrite H';
let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl front0)))))))) as H'; simpl in H'; rewrite H';
                     eauto.
    + omega.
  - destruct padding0 as [ | [ | [ | [ | [ | [ | [ | [ | ] ] ] ] ] ] ] ].
    + pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
        subst; simpl; eauto using ByteString_into_word'_eq.
    + pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
        pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
          simpl; eauto using ByteString_into_word'_eq.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
        pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
          let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
                               simpl; eauto using ByteString_into_word'_eq.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      let H'' := fresh in pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
      let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl front0)))) as H'; simpl in H'; rewrite H';
                           simpl; eauto using ByteString_into_word'_eq.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      let H'' := fresh in pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
      let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl front0)))) as H'; simpl in H'; rewrite H';
                           let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl front0))))) as H'; simpl in H'; rewrite H';
                                                simpl; eauto using ByteString_into_word'_eq.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      let H'' := fresh in pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
      let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl front0)))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl front0))))) as H'; simpl in H'; rewrite H';
let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl front0)))))) as H'; simpl in H'; rewrite H';
simpl; eauto using ByteString_into_word'_eq.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      let H'' := fresh in pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
      let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl front0)))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl front0))))) as H'; simpl in H'; rewrite H';
       let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl front0)))))) as H'; simpl in H'; rewrite H';
let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl front0))))))) as H'; simpl in H'; rewrite H';
                     simpl; eauto using ByteString_into_word'_eq.
    + let H' := fresh in
      pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      let H'' := fresh in pose proof (shatter_word (wtl front0)) as H''; simpl in H''; rewrite H'';
      let H' := fresh in pose proof (shatter_word (wtl (wtl front0))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl front0)))) as H'; simpl in H'; rewrite H';
      let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl front0))))) as H'; simpl in H'; rewrite H';
       let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl front0)))))) as H'; simpl in H'; rewrite H';
let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl front0))))))) as H'; simpl in H'; rewrite H';
let H' := fresh in pose proof (shatter_word (wtl (wtl (wtl (wtl (wtl (wtl (wtl front0)))))))) as H'; simpl in H'; rewrite H';
simpl; eauto using ByteString_into_word'_eq.
      + omega.
Qed.

Lemma ByteString_into_list_eq
  : forall bs,
    bs = list_into_ByteString (ByteString_into_list bs).
Proof.
  destruct bs; unfold list_into_ByteString, ByteString_into_list;
    simpl.
  induction padding0.
  - simpl; induction byteString0.
    + unfold ByteString_id; simpl; repeat f_equal.
      apply (shatter_word front0).
      apply le_uniqueness_proof.
    + simpl; rewrite <- IHbyteString0; simpl.
      unfold ByteString_push at 8; simpl.
      unfold ByteString_push at 7; simpl.
      unfold ByteString_push at 6; simpl.
      unfold ByteString_push at 5; simpl.
      unfold ByteString_push at 4; simpl.
      unfold ByteString_push at 3; simpl.
      unfold ByteString_push at 2; simpl.
      unfold ByteString_push at 1; simpl.
      f_equal.
      * apply (shatter_word front0).
      * apply le_uniqueness_proof.
      * f_equal; unfold eq_rec_r; simpl.
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
        repeat f_equal.
        symmetry; apply (shatter_word front0).
  - pose proof (shatter_word front0) as H'; simpl in H'; rewrite H';
      eauto.
    assert (padding0 < 8)%nat by omega.
    simpl; erewrite <- (IHpadding0 _ H).
    unfold ByteString_push; simpl.
    destruct (eq_nat_dec padding0 7); simpl.
    elimtype False; rewrite e in paddingOK0; eapply Lt.lt_irrefl; eauto.
    f_equal.
    apply le_uniqueness_proof.
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

Lemma ByteString_push_word_WS
  : forall a n front0 bs,
    ByteString_push_word (WS a front0) bs
    = ByteString_push a (@ByteString_push_word n front0 bs).
Proof.
  intros; reflexivity.
Qed.

Corollary ByteString_push_char_WS
  : forall a front0 bs,
    ByteString_push_char (WS a front0) bs
    = ByteString_push a (@ByteString_push_word _ front0 bs).
Proof.
  intros; apply ByteString_push_word_WS.
Qed.

Lemma ByteString_push_char_id_right
  : forall (chars : list char) (bs : ByteString),
    padding bs = 0 ->
    fold_right ByteString_push_char bs chars =
    {| front := WO;
       paddingOK := ByteString_id_subproof;
       byteString := chars ++ (byteString bs) |}.
Proof.
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
  rewrite !ByteString_push_char_WS.
  rewrite !ByteString_push_word_WS.
  simpl.
  unfold ByteString_push at 8; simpl.
  unfold ByteString_push at 7; simpl.
  unfold ByteString_push at 6; simpl.
  unfold ByteString_push at 5; simpl.
  unfold ByteString_push at 4; simpl.
  unfold ByteString_push at 3; simpl.
  unfold ByteString_push at 2; simpl.
  unfold ByteString_push at 1; simpl.
  f_equal.
  eapply le_uniqueness_proof.
Qed.

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
    assert (lt n 8) by (unfold lt; omega).
    erewrite (IHfront0 H).
    unfold ByteString_push.
    simpl.
    destruct (eq_nat_dec n 7); subst.
    omega.
    f_equal; eauto using le_uniqueness_proof.
Qed.

Lemma ByteString_transform_list_into
  : forall l l',
    ByteString_transformer (list_into_ByteString l) (list_into_ByteString l') = list_into_ByteString (app l l').
Proof.
  induction l; simpl.
  - unfold ByteString_transformer; simpl; eauto.
  - intro; rewrite <- IHl; clear IHl.
    unfold ByteString_transformer.
    destruct (list_into_ByteString l); simpl.
    unfold ByteString_push; simpl.
    destruct (eq_nat_dec padding0 7); subst.
    + unfold front at 1; unfold byteString at 1.
      unfold ByteString_push_word at 1; unfold padding at 1.
      unfold eq_rec_r, eq_rec, eq_rect, Logic.eq_sym.
      simpl fold_right.
      destruct (eq_nat_dec
                  (padding
                     (ByteString_push_word front0
                                            (fold_right ByteString_push_char (list_into_ByteString l') byteString0))) 7).
    * rewrite ByteString_push_char_WS.
      assert (0 = padding (ByteString_push a ((ByteString_push_word front0)
                                                (fold_right ByteString_push_char (list_into_ByteString l') byteString0)))).
      { induction (fold_right ByteString_push_char (list_into_ByteString l') byteString0).
        unfold ByteString_push.
        destruct (eq_nat_dec
         (padding
            (ByteString_push_word front0
               {|
               padding := padding0;
               front := front1;
               paddingOK := paddingOK1;
               byteString := byteString1 |})) 7).
        simpl; reflexivity.
        elimtype False; apply n.
        apply e.
      }
      apply ByteString_transform_f_equal with (p_eq := H).
      apply le_uniqueness_proof.
      destruct (fold_right
                   ByteString_push_char
                   (list_into_ByteString l')
                   byteString0).
      (* *) unfold front at 3; unfold padding at 2.
      destruct (ByteString_push_word
                    front0
                    {|
                      padding := padding0;
                      front := front1;
                      paddingOK := paddingOK1;
                      byteString := byteString1 |}).
        revert H; unfold ByteString_push; simpl in *.
        destruct (eq_nat_dec padding1 7); simpl; intros.
        apply eq_rect_eq_dec; eauto using eq_nat_dec.
        congruence.
        (* *) destruct (fold_right
                          ByteString_push_char
                          (list_into_ByteString l')
                          byteString0).
        unfold byteString at 2.
        unfold ByteString_push at 1.
        destruct (ByteString_push_word
                    front0
                    {|
                      padding := padding0;
                      front := front1;
                      paddingOK := paddingOK1;
                      byteString := byteString1 |}).
        simpl padding.
        destruct (eq_nat_dec padding1 7).
        simpl.
        repeat f_equal.
        unfold eq_rec_r, eq_rec_r, eq_rec.
        unfold Logic.eq_sym.
        unfold eq_rect.
        assert (e0 = e) by (apply eq_proofs_unicity; intros; omega).
        rewrite H0; eauto.
        simpl in e; congruence.
    * rewrite ByteString_push_char_WS.
      assert (S (padding
                (ByteString_push_word front0
                                      (fold_right ByteString_push_char (list_into_ByteString l') byteString0)))
          = padding (ByteString_push a ((ByteString_push_word front0)
                                                (fold_right ByteString_push_char (list_into_ByteString l') byteString0)))).
      { destruct (ByteString_push_word front0
           (fold_right ByteString_push_char (list_into_ByteString l') byteString0)).
        simpl in *.
        unfold ByteString_push.
        destruct (eq_nat_dec
         (padding
            {|
            padding := padding0;
            front := front1;
            paddingOK := paddingOK1;
            byteString := byteString1 |}) 7).
        simpl in *|-; congruence.
        reflexivity.
      }
      apply ByteString_transform_f_equal with (p_eq := H).
      apply le_uniqueness_proof.
      unfold front at 3; unfold padding at 2.
      destruct (ByteString_push_word
                  front0
                  (fold_right ByteString_push_char
                              (list_into_ByteString l') byteString0)).
      simpl.
      revert H; unfold ByteString_push; simpl in *.
      destruct (eq_nat_dec padding0 7).
      simpl; intros.
      congruence.
      simpl; intros.
      apply eq_rect_eq_dec; eauto using eq_nat_dec.
      destruct (ByteString_push_word
                  front0
                  (fold_right ByteString_push_char
                              (list_into_ByteString l') byteString0)).
      simpl.
      revert H; unfold ByteString_push; simpl in *.
      destruct (eq_nat_dec padding0 7).
      simpl; intros.
      congruence.
      simpl; intros.
      reflexivity.
    + unfold front at 1; unfold byteString at 1.
      destruct (eq_nat_dec
       (padding
          (ByteString_push_word front0
             (fold_right ByteString_push_char (list_into_ByteString l') byteString0)))
       7).
      setoid_rewrite ByteString_push_word_WS.
      assert (0 = padding (ByteString_push a ((ByteString_push_word front0)
                                                (fold_right ByteString_push_char (list_into_ByteString l') byteString0)))).
      { induction (fold_right ByteString_push_char (list_into_ByteString l') byteString0).
        unfold ByteString_push.
        destruct (eq_nat_dec
         (padding
            (ByteString_push_word front0
               {|
               padding := padding1;
               front := front1;
               paddingOK := paddingOK1;
               byteString := byteString1 |})) 7).
        simpl; reflexivity.
        congruence.
      }
      apply ByteString_transform_f_equal with (p_eq := H).
      apply le_uniqueness_proof.
      destruct (fold_right
                   ByteString_push_char
                   (list_into_ByteString l')
                   byteString0).
      (* *) unfold front at 3; unfold padding at 2.
      destruct (ByteString_push_word
                    front0
                    {|
                      padding := padding1;
                      front := front1;
                      paddingOK := paddingOK1;
                      byteString := byteString1 |}).
        revert H; unfold ByteString_push; simpl in *.
        destruct (eq_nat_dec padding2 7); simpl; intros.
        apply eq_rect_eq_dec; eauto using eq_nat_dec.
        congruence.
        (* *) destruct (fold_right
                          ByteString_push_char
                          (list_into_ByteString l')
                          byteString0).
        unfold byteString at 2.
        unfold ByteString_push at 1.
        destruct (ByteString_push_word
                    front0
                    {|
                      padding := padding1;
                      front := front1;
                      paddingOK := paddingOK1;
                      byteString := byteString1 |}).
        simpl padding.
        destruct (eq_nat_dec padding2 7).
        simpl.
        repeat f_equal.
        apply eq_proofs_unicity; intros; omega.
        simpl in e; congruence.
        setoid_rewrite ByteString_push_word_WS.
        assert (S (padding
                     (ByteString_push_word front0
                                           (fold_right ByteString_push_char (list_into_ByteString l') byteString0)))
                = padding (ByteString_push a ((ByteString_push_word front0)
                                                (fold_right ByteString_push_char (list_into_ByteString l') byteString0)))).
      { destruct (ByteString_push_word front0
           (fold_right ByteString_push_char (list_into_ByteString l') byteString0)).
        simpl in *.
        unfold ByteString_push.
        destruct (eq_nat_dec
         (padding
            {|
            padding := padding1;
            front := front1;
            paddingOK := paddingOK1;
            byteString := byteString1 |}) 7).
        simpl in *|-; congruence.
        reflexivity.
      }
      apply ByteString_transform_f_equal with (p_eq := H).
      apply le_uniqueness_proof.
      unfold front at 3; unfold padding at 2.
      destruct (ByteString_push_word
                  front0
                  (fold_right ByteString_push_char
                              (list_into_ByteString l') byteString0)).
      simpl.
      revert H; unfold ByteString_push; simpl in *.
      destruct (eq_nat_dec padding1 7).
      simpl; intros.
      congruence.
      simpl; intros.
      apply eq_rect_eq_dec; eauto using eq_nat_dec.
      destruct (ByteString_push_word
                  front0
                  (fold_right ByteString_push_char
                              (list_into_ByteString l') byteString0)).
      simpl.
      revert H; unfold ByteString_push; simpl in *.
      destruct (eq_nat_dec padding1 7).
      simpl; intros.
      congruence.
      simpl; intros.
      reflexivity.
Qed.

Fixpoint plus_assoc' (n : nat) {struct n}
  : forall m p : nat, n + (m + p) = n + m + p.
  refine match n return
               forall m p : nat,
                 n + (m + p) = n + m + p with
         | 0 => fun m p => eq_refl _
         | S n' => fun m p => _
         end.
  simpl; destruct (plus_assoc' n' m p); reflexivity.
Defined.

Lemma append_word_assoc {n m p}
  : forall w w' w'',
    append_word w (append_word w' w'') = eq_rect _ _ (append_word (append_word w w') w'') _ (eq_sym (plus_assoc' n m p)).
Proof.
  induction w; simpl; intros.
  - reflexivity.
  - rewrite IHw; clear.
    rewrite succ_eq_rect.
    f_equal.
    apply eq_proofs_unicity; intros.
    destruct (eq_nat_dec x y); eauto.
Qed.

Lemma ByteString_transform_assoc
  : forall l m n : ByteString,
    ByteString_transformer l (ByteString_transformer m n) =
    ByteString_transformer (ByteString_transformer l m) n.
Proof.
  intros.
  rewrite (ByteString_into_list_eq m),
  (ByteString_into_list_eq n),
  (ByteString_into_list_eq l).
  erewrite !ByteString_transform_list_into.
  rewrite app_assoc.
  reflexivity.
Qed.

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
  simpl.
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
  intros t m n; destruct (ByteString_transform_push_eq t m).
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
    injection H3; intros.
    apply inj_pair2_eq_dec in H2; eauto.
    f_equal.
    rewrite (shatter_word_0 front0);
      rewrite (shatter_word_0 front1); reflexivity.
    apply le_uniqueness_proof.
    rewrite (shatter_word c) in *;
      rewrite (shatter_word c0) in *.
    injection H3; intros.
    rewrite H1; f_equal.
    f_equal.
    simpl in H4; rewrite H4; reflexivity.
    apply inj_pair2_eq_dec in H6; eauto.
    apply eq_nat_dec.
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
    rewrite (shatter_word front0); rewrite (shatter_word front1);
      f_equal; eauto.
    apply inj_pair2_eq_dec in H6; eauto.
    apply eq_nat_dec.
    apply le_uniqueness_proof.
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

Print Assumptions ByteString_TransformerUnitOpt.
