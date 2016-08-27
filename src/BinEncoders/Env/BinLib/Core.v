Require Import
        Bedrock.Word
        Coq.NArith.NArith
        Coq.Arith.Arith
        Coq.Numbers.Natural.Peano.NPeano
        Coq.Logic.Eqdep_dec
        Fiat.BinEncoders.Env.Common.Specs.
Import NPeano.

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

Definition ByteString_append
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
   length_ByteString (ByteString_append bs bs') = length_ByteString bs + length_ByteString bs'.
Proof.
  destruct bs as [bs_padding bs_front ? bs_byteString]; simpl.
  induction bs_byteString.
  - unfold ByteString_append, length_ByteString at 2; simpl.
    rewrite NPeano.Nat.add_0_r.
    induction bs_padding.
    + simpl; eauto.
    + simpl; intros.
      rewrite length_ByteString_push; rewrite IHbs_padding; eauto.
      omega.
  -  unfold ByteString_append in *; simpl in *.
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
   ByteString_append ByteString_id bs = bs.
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

Hint Unfold modulo Nat.modulo : modulo_db.

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

Lemma list_into_ByteString_eq
  : forall l,
    l = ByteString_into_list (list_into_ByteString l).
Proof.
  induction l; simpl; try reflexivity.
  rewrite IHl, <- ByteString_into_list_eq; clear IHl.
  destruct (list_into_ByteString l).
  unfold ByteString_push; simpl.
  destruct (eq_nat_dec padding0 7) eqn: ?.
  - unfold ByteString_into_list; simpl.
    f_equal; subst.
    shatter_word front0; reflexivity.
  - reflexivity.
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
    ByteString_append bs ByteString_id = bs.
Proof.
  destruct bs; unfold ByteString_append, ByteString_id; simpl.
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
    ByteString_append (list_into_ByteString l) (list_into_ByteString l') = list_into_ByteString (app l l').
Proof.
  induction l; simpl.
  - unfold ByteString_append; simpl; eauto.
  - intro; rewrite <- IHl; clear IHl.
    unfold ByteString_append.
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

Lemma list_into_ByteString_append
  : forall b b',
    ByteString_into_list (ByteString_append b b') = app (ByteString_into_list b)
                                                        (ByteString_into_list b').
Proof.
  intros.
  rewrite (ByteString_into_list_eq b), (ByteString_into_list_eq b').
  rewrite ByteString_transform_list_into.
  rewrite <- !ByteString_into_list_eq.
  rewrite list_into_ByteString_eq; reflexivity.
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
    ByteString_append l (ByteString_append m n) =
    ByteString_append (ByteString_append l m) n.
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
  {| transform := ByteString_append;
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

Lemma padding_list_into_ByteString :
  forall l,
    padding (list_into_ByteString l) = NPeano.modulo (length l) 8.
Proof.
  induction l.
  simpl; eauto.
  simpl length.
  destruct (Peano_dec.eq_nat_dec (NPeano.modulo (length l) 8) 7).
  - rewrite NatModulo_S_Full.
    simpl.
    unfold ByteString_push.
    destruct (Peano_dec.eq_nat_dec (padding (list_into_ByteString l)) 7).
    simpl; eauto.
    elimtype False.
    rewrite IHl in n; congruence.
    eauto.
  - rewrite NatModulo_S_Not_Full; eauto.
    unfold NPeano.Nat.modulo in IHl |- *; rewrite <- IHl.
    simpl.
    unfold ByteString_push.
    unfold NPeano.modulo, NPeano.Nat.modulo in IHl, n; rewrite <- IHl in n.
    destruct (Peano_dec.eq_nat_dec (padding (list_into_ByteString l)) 7);
      simpl; eauto.
    congruence.
Qed.

Lemma list_into_ByteString_push
  : forall a l, ByteString_push a (list_into_ByteString l) =
                list_into_ByteString (a :: l).
Proof.
  reflexivity.
Qed.

Lemma ByteString_append_padding_eq
  : forall b b',
    padding (ByteString_append b b') = NPeano.modulo (padding b + padding b') 8.
Proof.
  intros.
  rewrite (ByteString_into_list_eq b),
  (ByteString_into_list_eq b').
  rewrite ByteString_transform_list_into.
  rewrite !padding_list_into_ByteString.
  rewrite app_length.
  rewrite NPeano.Nat.add_mod; eauto.
Qed.

Lemma padding_eq_mod_8
  : forall b,
    padding b = NPeano.modulo (length_ByteString b) 8.
Proof.
  intros.
  rewrite (ByteString_into_list_eq b).
  unfold length_ByteString.
  rewrite !padding_list_into_ByteString.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_r; eauto.
  rewrite (fun c => proj2 (NPeano.Nat.mod_divides (8 * _) 8 c));
    eauto.
  rewrite <- plus_n_O, NPeano.Nat.mod_mod; eauto.
Qed.

Lemma length_list_into_ByteString
  : forall l,
    length_ByteString (list_into_ByteString l) = length l.
Proof.
  induction l; simpl.
  - reflexivity.
  - rewrite ByteString_measure_push; simpl; rewrite IHl; omega.
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

Lemma hd_error_app {A}
  : forall (a : A) (l l' : list A),
    hd_error l = Some a -> hd_error (l ++ l') = Some a.
Proof.
  destruct l; simpl; intros; first [ discriminate | eauto].
Qed.

Lemma list_into_ByteString_inj :
  forall l l',
    list_into_ByteString l = list_into_ByteString l'
    -> l = l'.
Proof.
  induction l; destruct l'; simpl; intros; eauto.
  - apply (f_equal length_ByteString) in H;
      rewrite length_ByteString_push in H;
      compute in H; discriminate.
  - apply (f_equal length_ByteString) in H;
      rewrite length_ByteString_push in H;
      compute in H; discriminate.
  - apply (f_equal ByteString_pop) in H;
      rewrite !ByteString_transform_push_pop_opt in H.
    injections; f_equal; eauto.
Qed.

Lemma rev_inj {A}
  : forall (l l' : list A),
    rev l = rev l' -> l = l'.
Proof.
  intros; apply (f_equal (@rev _)) in H; rewrite !rev_involutive in H;
    eauto.
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

Definition ByteString_enqueue
         (b : bool)
         (bs : ByteString)
  : ByteString.
  refine (if (eq_nat_dec (padding bs) 7) then
            {| front := WO;
               byteString := (byteString bs) ++ [WS b _] |}
  else
    {| front := WS b (front bs);
       padding := S (padding bs);
       byteString := byteString bs |}).
  abstract omega.
  { pose proof (front bs) as w; generalize dependent (padding bs).
    intros ?? w; subst; exact w. }
  { abstract (pose proof (paddingOK bs); omega). }
Defined.

Fixpoint word_dequeue sz
           (w : word (S sz))
  : bool * word sz :=
  match sz return word (S sz) -> bool * word sz with
  | 0 => fun w => (whd w, WO)
  | S sz' =>
    fun w => let (b, w') := word_dequeue (wtl w) in
             (b, WS (whd w) w')
  end w.

Fixpoint CharList_dequeue
         (l : list char)
  : option (bool * (list char) * word 7) :=
  match l with
  | nil => None (* This case should never be called. *)
  | c :: l' =>
    let (b, w') := word_dequeue c in
    match CharList_dequeue l' with
      | Some (b', l'', tail) =>
        Some (b, WS b' w' :: l'', tail)
      | None => Some (b, [ ], w')
    end
  end.

Definition ByteString_dequeue
         (bs : ByteString)
  : option (bool * ByteString).
  refine (match padding bs as n return
                word n
                -> lt n 8
                -> _ with
          | 0 =>
            fun _ _ =>
              match CharList_dequeue (byteString bs) with
              | None => None
              | Some (b', l'', tail) =>
                Some (b', {| front := tail;
                             byteString := l'' |})
              end
          | S n => fun front' lt_n =>
                     match CharList_dequeue (byteString bs) with
                     | None =>
                       let (b, w') := word_dequeue front' in
                       Some (b, {| front := w';
                                   byteString := [] |})
                     | Some (b', l'', tail) =>
                       let (b, w') := word_dequeue front' in
                       Some (b', {| front := w';
                                    byteString := l'' ++ [WS b tail] |})
                     end
          end (front bs) (paddingOK bs)).
  abstract omega.
  abstract omega.
  abstract omega.
Defined.

Fixpoint ByteString_enqueue_word
           {n}
           (w : word n)
           (bs : ByteString) :=
  match n return word n -> ByteString with
  | 0 => fun _ => bs
  | S n' => fun w =>
              (ByteString_enqueue (whd w) (ByteString_enqueue_word (wtl w) bs))
  end w.

Definition ByteString_enqueue_char (bs : ByteString) (c : char)
  := ByteString_enqueue_word c bs.

Definition ByteString_enqueue_ByteString
           (bs bs' : ByteString)
  : ByteString :=
  let bs'' := fold_left ByteString_enqueue_char (byteString bs') bs in
  ByteString_enqueue_word (front bs') bs''.

Lemma app_cons_assoc {A}
  : forall a (l l' : list A),
    l ++ (a :: l') = (l ++ [a]) ++ l'.
Proof.
  intros; rewrite <- app_assoc; reflexivity.
Qed.

Definition queue_into_ByteString
           (l : list bool)
  : ByteString :=
  fold_left (fun bs b => ByteString_enqueue b bs) l ByteString_id.

Fixpoint wordToQueue {n}
           (w : word n)
  : list bool :=
  match n return word n -> list bool with
  | 0 => fun _ => [ ]
  | S n' => fun w => wordToQueue (wtl w) ++ [whd w]
  end w.

Fixpoint ByteString_into_queue'
           (chars : list char)
           {struct chars} : list bool :=
  match chars return list bool with
  | [ ] => [ ]
  | char' :: chars' =>
    app (wordToQueue char')
      (ByteString_into_queue' chars')
  end.

Definition ByteString_into_queue
           (bs : ByteString)
  : list bool :=
  app (ByteString_into_queue' (byteString bs)) (wordToQueue (front bs)).

(* Lemma enqueue_queue_into_ByteString
  : forall b bs l,
    fold_right ByteString_enqueue (ByteString_enqueue b bs) l
    = ByteString_enqueue b (fold_right ByteString_enqueue bs l).
Proof.
  induction l; simpl; eauto.
  rewrite IHl. *)

Lemma length_ByteString_enqueue
  : forall b bs,
    length_ByteString (ByteString_enqueue b bs) = S (length_ByteString bs).
Proof.
  destruct bs; unfold ByteString_enqueue; simpl.
  destruct (eq_nat_dec padding0 7); simpl.
  - unfold length_ByteString; simpl.
    rewrite app_length; simpl.
    omega.
  - unfold length_ByteString; simpl.
    omega.
Qed.

Lemma length_padding_ByteString_into_queue_eq'
  : forall l bs,
    length_ByteString
      (fold_left (fun (bs : ByteString) (b : bool) => ByteString_enqueue b bs)
                 l bs) = length l + length_ByteString bs.
Proof.
  intros; rewrite <- fold_left_rev_right.
  rewrite <- rev_length.
  induction (rev l); simpl; eauto.
  rewrite <- IHl0.
  rewrite length_ByteString_enqueue; reflexivity.
Qed.

Lemma length_wordToQueue
  : forall sz (w : word sz), length (wordToQueue w) = sz.
Proof.
  induction w; simpl; eauto.
  rewrite app_length, IHw; simpl; omega.
Qed.

Lemma length_ByteString_into_queue'
  : forall bs, length (ByteString_into_queue' bs) = 8 * (length bs).
Proof.
  induction bs; simpl; eauto.
  rewrite IHbs.
  simpl; omega.
Qed.

Lemma length_padding_ByteString_into_queue_eq
  : forall bs,
    length_ByteString bs = length_ByteString (queue_into_ByteString (ByteString_into_queue bs)).
Proof.
  destruct bs; unfold queue_into_ByteString, ByteString_into_queue;
    unfold length_ByteString at 1; simpl padding; simpl byteString.
  rewrite fold_left_app.
  rewrite length_padding_ByteString_into_queue_eq'.
  rewrite length_wordToQueue; f_equal.
  rewrite <- length_ByteString_into_queue'.
  induction (ByteString_into_queue' byteString0); simpl.
  reflexivity.
  rewrite length_padding_ByteString_into_queue_eq'.
  rewrite IHl, length_padding_ByteString_into_queue_eq'.
  unfold length_ByteString; simpl; omega.
Qed.

Lemma padding_ByteString_into_queue_eq
  : forall bs,
    padding bs = padding (queue_into_ByteString (ByteString_into_queue bs)).
Proof.
  intros; rewrite !padding_eq_mod_8.
  rewrite <- length_padding_ByteString_into_queue_eq; reflexivity.
Qed.

Lemma ByteString_into_queue_eq
  : forall bs,
    bs = queue_into_ByteString (ByteString_into_queue bs).
Proof.
  destruct bs; unfold queue_into_ByteString, ByteString_into_queue;
    simpl.
  rewrite <- fold_left_rev_right, rev_app_distr, fold_right_app.
  induction padding0.
  - shatter_word front0.
    rewrite <- (app_nil_l byteString0) at 1.
    remember nil.
    replace ByteString_id with {| padding := 0;
                                 front := WO;
                                 paddingOK := paddingOK0;
                                 byteString := l |}.
    simpl; clear Heql; revert l; induction byteString0; simpl.
    + intros; rewrite app_nil_r; simpl; repeat f_equal.
    + intros; rewrite !fold_right_app.
      simpl.
      unfold char in a; shatter_word a.
      unfold ByteString_enqueue at 8; simpl.
      unfold ByteString_enqueue at 7; simpl.
      unfold ByteString_enqueue at 6; simpl.
      unfold ByteString_enqueue at 5; simpl.
      unfold ByteString_enqueue at 4; simpl.
      unfold ByteString_enqueue at 3; simpl.
      unfold ByteString_enqueue at 2; simpl.
      rewrite app_cons_assoc.
      rewrite IHbyteString0.
      repeat f_equal.
      apply le_uniqueness_proof.
    + rewrite Heql; unfold ByteString_id; repeat f_equal.
      apply le_uniqueness_proof.
  - rewrite (shatter_word front0).
    simpl.
    rewrite rev_app_distr, fold_right_app.
    simpl.
    assert (lt padding0 8) by omega.
    erewrite <- (IHpadding0 _ H).
    unfold ByteString_enqueue; simpl.
    destruct (eq_nat_dec padding0 7).
    subst; omega.
    repeat f_equal.
    apply le_uniqueness_proof.
Qed.

Lemma ByteString_enqueue_into_list
  : forall b (l : list bool),
    ByteString_enqueue b (queue_into_ByteString l)
    = queue_into_ByteString (l ++ [b]).
Proof.
  unfold queue_into_ByteString; intros.
  remember ByteString_id.
  clear Heqb0; revert b0; induction l; simpl.
  - intros; reflexivity.
  - simpl; intros.
    eapply IHl.
Qed.

Fixpoint split_list_bool
         (l : list bool)
  : (list char) * {n : nat & word n} :=
  match l return (list char) * {n : nat & word n} with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l' =>
    let (l'', back) := split_list_bool l' in
    (WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))) :: l'', back)
  | [b0; b1; b2; b3; b4; b5; b6] =>
    ([], existT _ _ (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))))
  | [b0; b1; b2; b3; b4; b5] =>
    ([], existT _ _ (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))
  | [b0; b1; b2; b3; b4] =>
    ([], existT _ _ (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))
  | [b0; b1; b2; b3] =>
    ([], existT _ _ (WS b3 (WS b2 (WS b1 (WS b0 WO)))))
  | [b0; b1; b2] =>
    ([], existT _ _ (WS b2 (WS b1 (WS b0 WO))))
  | [b0; b1] =>
    ([], existT _ _ (WS b1 (WS b0 WO)))
  | [b0] =>
    ([], existT _ _  (WS b0 WO))
  | _ => ([], existT _ _ WO)
  end.

Lemma ByteString_enqueue_ByteString_id_right
  : forall bs, ByteString_enqueue_ByteString bs ByteString_id = bs.
Proof.
  reflexivity.
Qed.

Lemma empty_padding_ByteString_eq_byteString
  : forall b paddingOK',
    padding b = 0
    -> b = {| padding := 0; front := WO; paddingOK := paddingOK'; byteString := byteString b |}.
Proof.
  destruct b; intros; simpl in *; subst.
  shatter_word front0.
  simpl; repeat f_equal.
  apply le_uniqueness_proof.
Qed.

Lemma ByteString_enqueue_simpl
  : forall b bs (paddingOK' : lt (padding bs) 7),
    ByteString_enqueue b bs
    = {| front := WS b (front bs);
         paddingOK := lt_n_S _ _ paddingOK';
         byteString := byteString bs |}.
  destruct bs; simpl; intros.
  unfold ByteString_enqueue; simpl.
  destruct (eq_nat_dec padding0 7); simpl in *; try omega.
  repeat f_equal; eapply le_uniqueness_proof.
Qed.

Lemma fold_left_enqueue_simpl
  : forall b0 b1 b2 b3 b4 b5 b6 b7 l  byteString0 paddingOK0,
    fold_left (fun (bs : ByteString) (b : bool) => ByteString_enqueue b bs)
     (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l)
     {|
     padding := 0;
     front := WO;
     paddingOK := paddingOK0;
     byteString := byteString0 |} =
   fold_left (fun (bs : ByteString) (b : bool) => ByteString_enqueue b bs) l
     {|
     padding := 0;
     front := WO;
     paddingOK := lt_0_Sn 7;
     byteString := byteString0 ++
                   [WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))] |}.
Proof.
  simpl; intros.
  f_equal.
  unfold ByteString_enqueue at 7; simpl.
  unfold ByteString_enqueue at 6; simpl.
  unfold ByteString_enqueue at 5; simpl.
  unfold ByteString_enqueue at 4; simpl.
  unfold ByteString_enqueue at 3; simpl.
  unfold ByteString_enqueue at 2; simpl.
  unfold ByteString_enqueue at 1; simpl.
  repeat f_equal.
  apply le_uniqueness_proof.
Qed.

Lemma queue_into_ByteString_eq_split_list_bool
  : forall l,
    exists paddingOK',
    queue_into_ByteString l =
    {|
      front := projT2 (snd (split_list_bool l));
      paddingOK := paddingOK';
      byteString := fst (split_list_bool l) |}.
Proof.
  intro; generalize (le_refl (length l)); remember (length l).
  unfold queue_into_ByteString.
  replace (fst (split_list_bool l)) with
  ((byteString ByteString_id) ++ (fst (split_list_bool l))) by reflexivity.
  assert (padding ByteString_id = 0) as H' by reflexivity;
    revert H'.
  generalize ByteString_id.
  setoid_rewrite Heqn at 1; clear Heqn; revert l;
    induction n.
  - intros; destruct l; simpl; intros.
    + setoid_rewrite app_nil_r; eexists (lt_0_Sn _).
      eauto using empty_padding_ByteString_eq_byteString.
    + inversion H0.
  - intros l b H0 H;
      destruct l as [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? ] ] ] ] ] ] ] ];
      try match goal with
            |- exists _ : lt ?z 8, _ =>
            let H := fresh in
            try (assert (lt z 8) as H by (simpl; omega); exists H;
                 simpl in H);
              solve [unfold queue_into_ByteString, ByteString_id; simpl;
                     destruct b; simpl in *; subst;
                     erewrite ByteString_enqueue_simpl by (simpl; omega);
                     shatter_word front0; repeat f_equal;
                     eauto using app_nil_r, le_uniqueness_proof]
  end.
    + unfold queue_into_ByteString, ByteString_id;
        simpl; unfold ByteString_enqueue; simpl; repeat f_equal;
          rewrite app_nil_r;
          eauto using empty_padding_ByteString_eq_byteString.
    + destruct (split_list_bool l) eqn : ?.
      destruct b.
      destruct (IHn l {| front := WO;
                         paddingOK := lt_0_Sn _;
                         byteString :=
                           byteString0 ++ [ WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))] |}).
      simpl in *; omega.
      simpl in *; omega.
      simpl split_list_bool.
      revert x H0 H1; rewrite Heqp; intros; clear Heqp.
      exists x.
      simpl byteString.
      unfold fst.
      rewrite (app_cons_assoc _ _ l0).
      match goal with
        H : _ = ?a
        |- _ = ?a' => replace a' with a by reflexivity;
                        rewrite <- H
      end.
      clear H1 H x s IHn.
      simpl in H0.
      revert front0 paddingOK0; rewrite H0.
      intros; shatter_word front0.
      erewrite <- fold_left_enqueue_simpl.
      apply f_equal.
      apply f_equal.
      reflexivity.
      Grab Existential Variables.
      omega.
      simpl; omega.
      simpl; omega.
      simpl; omega.
      simpl; omega.
      simpl; omega.
      simpl; omega.
      simpl; omega.
Qed.

Lemma queue_into_ByteString_app
  : forall l' l,
    queue_into_ByteString (l ++ l') =
    fold_left (fun bs b => ByteString_enqueue b bs)
              l' (queue_into_ByteString l).
Proof.
  induction l'; simpl; intros.
  - rewrite app_nil_r; eauto.
  - rewrite ByteString_enqueue_into_list.
    rewrite <- IHl', <- app_assoc; reflexivity.
Qed.

Lemma ByteString_enqueue_ByteString_enqueue
  : forall (l' l : bin)
           (b : bool),
    ByteString_enqueue_ByteString (queue_into_ByteString l) (ByteString_enqueue b (queue_into_ByteString l')) =
   ByteString_enqueue b (ByteString_enqueue_ByteString (queue_into_ByteString l) (queue_into_ByteString l')).
Proof.
  intro; destruct (queue_into_ByteString l').
  unfold ByteString_enqueue at 1; simpl.
  destruct (eq_nat_dec padding0 7); simpl.
  - unfold ByteString_enqueue_ByteString; simpl; subst;
      clear paddingOK0.
    intros; rewrite fold_left_app;
      shatter_word front0;
      unfold ByteString_enqueue_char; simpl.
    reflexivity.
  - reflexivity.
Qed.

Lemma ByteString_enqueue_ByteString_into_list
  : forall (l' l : list bool),
    ByteString_enqueue_ByteString (queue_into_ByteString l) (queue_into_ByteString l')
    = queue_into_ByteString (l ++ l').
Proof.
  intro; generalize (le_refl (length l')); remember (length l').
  setoid_rewrite Heqn at 1; clear Heqn; revert l';
    induction n.
  - intros; destruct l'; simpl; intros.
    + rewrite ByteString_enqueue_ByteString_id_right,
      app_nil_r; reflexivity.
    + inversion H.
  - intros; rewrite queue_into_ByteString_app.
    rewrite <- (rev_involutive l') in *.
    clear IHn H.
    induction (rev l'); simpl.
    + rewrite ByteString_enqueue_ByteString_id_right; reflexivity.
    + rewrite <- ByteString_enqueue_into_list.
      rewrite fold_left_app; simpl.
      rewrite <- IHl0.
      apply ByteString_enqueue_ByteString_enqueue.
Qed.

Lemma massage_queue_into_ByteString
  : forall n w1
           paddingOK' paddingOK'' paddingOK'''
           l' l,
    {|
      padding := n;
      front := w1;
      paddingOK := paddingOK';
      byteString := l ++ l' |} =
    ByteString_enqueue_ByteString
      {|
      padding := 0;
      front := WO;
      paddingOK := paddingOK''';
      byteString := l|}
      {|
        padding := n;
        front := w1;
        paddingOK := paddingOK'';
        byteString := l' |}.
Proof.
  induction l'.
  - simpl.
    intros; rewrite app_nil_r.
    unfold ByteString_enqueue_ByteString; simpl.
    destruct n as [ | [ | [ | [ | [ | [ | [ | [ | ] ] ] ] ] ] ] ];
      try solve [inversion paddingOK'];
      try shatter_word w1; simpl;
        unfold queue_into_ByteString; simpl; repeat f_equal.
    + apply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue,
      ByteString_enqueue; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue,
      ByteString_enqueue; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue;
        simpl.
      unfold ByteString_enqueue at 3; simpl;
        unfold ByteString_enqueue at 2; simpl;
          unfold ByteString_enqueue at 1; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue; simpl.
      unfold ByteString_enqueue at 4; simpl.
        unfold ByteString_enqueue at 3; simpl;
          unfold ByteString_enqueue at 2; simpl.
        unfold ByteString_enqueue at 1; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue; simpl.
      unfold ByteString_enqueue at 5; simpl;
        unfold ByteString_enqueue at 4; simpl;
          unfold ByteString_enqueue at 3; simpl;
            unfold ByteString_enqueue at 2; simpl;
              unfold ByteString_enqueue at 1; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue; simpl.
      unfold ByteString_enqueue at 6; simpl;
        unfold ByteString_enqueue at 5; simpl;
          unfold ByteString_enqueue at 4; simpl;
            unfold ByteString_enqueue at 3; simpl;
              unfold ByteString_enqueue at 2; simpl;
                unfold ByteString_enqueue at 1; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id; simpl.
      unfold ByteString_enqueue at 7; simpl;
        unfold ByteString_enqueue at 6; simpl;
          unfold ByteString_enqueue at 5; simpl;
            unfold ByteString_enqueue at 4; simpl;
              unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                  unfold ByteString_enqueue at 1; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + omega.
  - intros.
    rewrite app_cons_assoc.
    simpl.
    pose proof (IHl' (l ++ [a])) as e; simpl in e;
      rewrite e; clear e IHl'.
    unfold ByteString_enqueue_ByteString; simpl.
    f_equal.
    unfold ByteString_enqueue_char at 3; simpl.
    unfold ByteString_enqueue at 7; simpl;
        unfold ByteString_enqueue at 6; simpl;
          unfold ByteString_enqueue at 5; simpl;
            unfold ByteString_enqueue at 4; simpl;
              unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                  unfold ByteString_enqueue at 1; simpl.
    unfold char in *.
    shatter_word a.
    simpl.
    repeat f_equal.
    apply le_uniqueness_proof.
Qed.

Lemma ByteString_dequeue_into_list
  : forall (l : list bool),
    ByteString_dequeue (queue_into_ByteString l)
    = match l with
      | b :: l' => Some (b, queue_into_ByteString l')
      | _ => None
      end.
Proof.
  intro; destruct (queue_into_ByteString_eq_split_list_bool l);
    rewrite H.
  generalize (le_refl (length l)); remember (length l).
  setoid_rewrite Heqn at 1; clear Heqn; revert l x H;
    induction n.
  - intros; destruct l; simpl; intros.
    + reflexivity.
    + inversion H0.
  - intros l x H H0;
      destruct l as [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? ] ] ] ] ] ] ] ].
    + simpl; reflexivity.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue; simpl;
        repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue,
      ByteString_enqueue; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue,
      ByteString_enqueue; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue;
        simpl.
      unfold ByteString_enqueue at 3; simpl;
        unfold ByteString_enqueue at 2; simpl;
          unfold ByteString_enqueue at 1; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue; simpl.
      unfold ByteString_enqueue at 4; simpl.
        unfold ByteString_enqueue at 3; simpl;
          unfold ByteString_enqueue at 2; simpl.
        unfold ByteString_enqueue at 1; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue; simpl.
      unfold ByteString_enqueue at 5; simpl;
        unfold ByteString_enqueue at 4; simpl;
          unfold ByteString_enqueue at 3; simpl;
            unfold ByteString_enqueue at 2; simpl;
              unfold ByteString_enqueue at 1; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue; simpl.
      unfold ByteString_enqueue at 6; simpl;
        unfold ByteString_enqueue at 5; simpl;
          unfold ByteString_enqueue at 4; simpl;
            unfold ByteString_enqueue at 3; simpl;
              unfold ByteString_enqueue at 2; simpl;
                unfold ByteString_enqueue at 1; simpl.
      repeat f_equal; eapply le_uniqueness_proof.
    + unfold queue_into_ByteString, ByteString_id; simpl.
      unfold ByteString_enqueue at 7; simpl;
        unfold ByteString_enqueue at 6; simpl;
          unfold ByteString_enqueue at 5; simpl;
            unfold ByteString_enqueue at 4; simpl;
              unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                  unfold ByteString_enqueue at 1; simpl.
      simpl in *.
      destruct (split_list_bool l) eqn : ? ; simpl in *.
      simpl in H.
      destruct (queue_into_ByteString_eq_split_list_bool l).
      assert (length l <= n)%nat as l_OK by omega.
      pose proof (IHn l _ H1 l_OK).
      unfold queue_into_ByteString in H; simpl in H.
      unfold ByteString_enqueue at 7 in H; simpl in H;
        unfold ByteString_enqueue at 6 in H; simpl in H;
          unfold ByteString_enqueue at 5 in H; simpl in H;
            unfold ByteString_enqueue at 4 in H; simpl in H;
              unfold ByteString_enqueue at 3 in H; simpl in H;
                unfold ByteString_enqueue at 2 in H; simpl in H;
                  unfold ByteString_enqueue at 1 in H; simpl in H.
      destruct (split_list_bool l); simpl in *.
      simpl in H2; revert H2; injection Heqp; clear.
      intros G G'.
      revert x x0; rewrite G, G'; subst; intros.
      unfold ByteString_dequeue in *;
        repeat match goal with
                 |- context [ByteString_enqueue_subproof0 ?z ?q ?m] =>
                 generalize (ByteString_enqueue_subproof0 z q m); intros; simpl in *
               | |- context [ByteString_enqueue_subproof ?z ?q ?m] =>
                 generalize (ByteString_enqueue_subproof z q m); intros; simpl in *
               end.
      destruct s as [[ | ?] ? ]; simpl in *.
      * destruct (CharList_dequeue l0) as [ [ [? ?] ?] | ] eqn : ? ;
          try discriminate.
        destruct l; simpl in H2; try discriminate; injections.
        simpl.
        unfold eq_rec_r at 2; unfold eq_sym; simpl.
        match goal with
          |- context[fold_left _ _ ?q] =>
          replace q
          with
          (queue_into_ByteString [b0; b1; b2; b3; b4; b5; b6; b8]) by
              (unfold queue_into_ByteString; simpl;
             unfold ByteString_enqueue at 7; simpl;
             unfold ByteString_enqueue at 6; simpl;
             unfold ByteString_enqueue at 5; simpl;
             unfold ByteString_enqueue at 4; simpl;
             unfold ByteString_enqueue at 3; simpl;
             unfold ByteString_enqueue at 2; simpl;
             unfold ByteString_enqueue at 1; simpl;
             repeat f_equal; intros; apply le_uniqueness_proof)
        end.
        rewrite <- queue_into_ByteString_app.
        rewrite <- ByteString_enqueue_ByteString_into_list.
        rewrite <- H.
        clear.
        repeat f_equal.
        unfold queue_into_ByteString at 1; simpl.
        unfold ByteString_enqueue at 7; simpl;
        unfold ByteString_enqueue at 6; simpl;
          unfold ByteString_enqueue at 5; simpl;
            unfold ByteString_enqueue at 4; simpl;
              unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                  unfold ByteString_enqueue at 1; simpl.
        erewrite <- massage_queue_into_ByteString;
          reflexivity.
        destruct l; try discriminate; simpl.
        repeat f_equal.
        apply le_uniqueness_proof.
      * destruct (CharList_dequeue l0) as [ [ [? ?] ?] | ] eqn : ? ;
          try discriminate; destruct (word_dequeue w).
        destruct l; try discriminate; injections;
          simpl.
        unfold eq_rec_r at 2; unfold eq_sym; simpl.
        match goal with
          |- context[fold_left _ _ ?q] =>
          replace q
          with
          (queue_into_ByteString [b0; b1; b2; b3; b4; b5; b6; b9]) by
              (unfold queue_into_ByteString; simpl;
             unfold ByteString_enqueue at 7; simpl;
             unfold ByteString_enqueue at 6; simpl;
             unfold ByteString_enqueue at 5; simpl;
             unfold ByteString_enqueue at 4; simpl;
             unfold ByteString_enqueue at 3; simpl;
             unfold ByteString_enqueue at 2; simpl;
             unfold ByteString_enqueue at 1; simpl;
             repeat f_equal; intros; apply le_uniqueness_proof)
        end.
        rewrite <- queue_into_ByteString_app.
        rewrite <- ByteString_enqueue_ByteString_into_list.
        rewrite <- H.
        clear.
        repeat f_equal.
        unfold queue_into_ByteString at 1; simpl.
        unfold ByteString_enqueue at 7; simpl;
        unfold ByteString_enqueue at 6; simpl;
          unfold ByteString_enqueue at 5; simpl;
            unfold ByteString_enqueue at 4; simpl;
              unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                  unfold ByteString_enqueue at 1; simpl.
        erewrite <- massage_queue_into_ByteString;
          reflexivity.
        destruct l; try discriminate; injections;
          simpl.
        unfold eq_rec_r at 2; unfold eq_sym; simpl.
        match goal with
          |- context[fold_left _ _ ?q] =>
          replace q
          with
          (queue_into_ByteString [b0; b1; b2; b3; b4; b5; b6; b8]) by
              (unfold queue_into_ByteString; simpl;
             unfold ByteString_enqueue at 7; simpl;
             unfold ByteString_enqueue at 6; simpl;
             unfold ByteString_enqueue at 5; simpl;
             unfold ByteString_enqueue at 4; simpl;
             unfold ByteString_enqueue at 3; simpl;
             unfold ByteString_enqueue at 2; simpl;
             unfold ByteString_enqueue at 1; simpl;
             repeat f_equal; intros; apply le_uniqueness_proof)
        end.
        rewrite <- queue_into_ByteString_app.
        rewrite <- ByteString_enqueue_ByteString_into_list.
        rewrite <- H.
        clear.
        repeat f_equal.
        unfold queue_into_ByteString at 1; simpl.
        unfold ByteString_enqueue at 7; simpl;
        unfold ByteString_enqueue at 6; simpl;
          unfold ByteString_enqueue at 5; simpl;
            unfold ByteString_enqueue at 4; simpl;
              unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                  unfold ByteString_enqueue at 1; simpl.
        erewrite <- massage_queue_into_ByteString;
          reflexivity.
Qed.

Lemma ByteString_enqueue_ByteString_id_left
  : forall bs, ByteString_enqueue_ByteString ByteString_id bs = bs.
Proof.
  intros; rewrite (ByteString_into_queue_eq bs),
          (ByteString_into_queue_eq ByteString_id).
  rewrite ByteString_enqueue_ByteString_into_list.
  reflexivity.
Qed.

Lemma length_ByteString_queue_into_ByteString'
  : forall l b,
    length_ByteString
      (fold_left (fun (bs : ByteString) (b : bool) => ByteString_enqueue b bs) l
                 b) =
    length l + length_ByteString b.
Proof.
  induction l; simpl; eauto.
  intros; rewrite IHl, length_ByteString_enqueue; omega.
Qed.

Corollary length_ByteString_queue_into_ByteString
  : forall l,
    length_ByteString (queue_into_ByteString l) = length l.
Proof.
  intro; unfold queue_into_ByteString;
    rewrite length_ByteString_queue_into_ByteString'.
  unfold length_ByteString; simpl; omega.
Qed.

Lemma ByteString_enqueue_ByteString_measure
  : forall b b' : ByteString,
    length_ByteString (ByteString_enqueue_ByteString b b') =
    length_ByteString b + length_ByteString b'.
Proof.
  intros; rewrite (ByteString_into_queue_eq b), (ByteString_into_queue_eq b'), ByteString_enqueue_ByteString_into_list.
  rewrite length_ByteString_queue_into_ByteString.
  rewrite app_length.
  rewrite <- !length_ByteString_queue_into_ByteString.
  reflexivity.
Qed.

Lemma ByteString_enqueue_ByteString_assoc
  : forall l m n : ByteString,
    ByteString_enqueue_ByteString l (ByteString_enqueue_ByteString m n) =
    ByteString_enqueue_ByteString (ByteString_enqueue_ByteString l m) n.
Proof.
  intros; rewrite (ByteString_into_queue_eq l),
          (ByteString_into_queue_eq m),
          (ByteString_into_queue_eq n),
          !ByteString_enqueue_ByteString_into_list,
          <- app_assoc; eauto.
Qed.

Global Instance ByteStringQueueTransformer : Transformer ByteString :=
  {| transform := ByteString_enqueue_ByteString;
     bin_measure := length_ByteString;
     transform_id := ByteString_id;
     transform_measure := ByteString_enqueue_ByteString_measure;
     transform_id_left := ByteString_enqueue_ByteString_id_left;
     transform_id_right := ByteString_transform_id_left;
     transform_assoc := ByteString_enqueue_ByteString_assoc
  |}.

Lemma ByteString_measure_dequeue_Some
  : forall (b' : ByteString) (t : bool) (b : ByteString),
    ByteString_dequeue b = Some (t, b') -> bin_measure b = bin_measure b' + 1.
Proof.
  intros ? ? ?; rewrite (ByteString_into_queue_eq b),
  ByteString_dequeue_into_list.
  destruct (ByteString_into_queue b); intros;
    try discriminate; injections.
  simpl.
  rewrite !length_ByteString_queue_into_ByteString; simpl;
    omega.
Qed.

Lemma ByteString_dequeue_transform_opt :
  forall t b b' b'',
    ByteString_dequeue b = Some (t, b')
    -> ByteString_dequeue (ByteString_enqueue_ByteString b b'') = Some (t, ByteString_enqueue_ByteString b' b'').
Proof.
  intros ? ? ? ? ;
    rewrite (ByteString_into_queue_eq b),
    (ByteString_into_queue_eq b'),
    (ByteString_into_queue_eq b'').
  rewrite !ByteString_enqueue_ByteString_into_list.
  rewrite !ByteString_dequeue_into_list.
  destruct (ByteString_into_queue b) eqn : ?; intros; try discriminate;
    injections.
  simpl.
  rewrite <- !ByteString_enqueue_ByteString_into_list.
  rewrite H0; reflexivity.
Qed.

Lemma ByteString_dequeue_head_opt :
  forall t,
    ByteString_dequeue (ByteString_enqueue t ByteString_id) = Some (t, ByteString_id).
Proof.
  intros; unfold ByteString_enqueue, ByteString_id, ByteString_dequeue;
    simpl; repeat f_equal.
  apply le_uniqueness_proof.
Qed.

Lemma ByteString_dequeue_None :
  ByteString_dequeue ByteString_id = None.
Proof.
  reflexivity.
Qed.

Lemma split_list_bool_inj
  : forall l l',
    split_list_bool l = split_list_bool l'
    -> l = l'.
Proof.
  intro; generalize (le_refl (length l)); remember (length l).
  rewrite Heqn at 1; clear Heqn; revert l;
    induction n.
  - destruct l; simpl; intros.
    destruct l'; simpl in *; eauto.
    destruct l' as [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? ] ] ] ] ] ] ];
      try (simpl; intros; congruence).
    destruct (split_list_bool l); simpl; intros; discriminate.
    inversion H.
  - intros l H;
      destruct l as [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? ] ] ] ] ] ] ] ];
      try (simpl; intros; congruence);
    destruct l' as [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? [ | ? ] ] ] ] ] ] ] ];
    try (simpl; intros; first [discriminate
                              | congruence
                              | injection H0; congruence
                              | destruct (split_list_bool l); congruence]).
    simpl; intros.
    destruct (split_list_bool l) eqn : ? ;
      destruct (split_list_bool l0) eqn : ? .
    injections; repeat f_equal.
    eapply IHn; simpl in H; try omega.
    congruence.
Qed.

Lemma queue_into_ByteString_inj
  : forall l l',
    queue_into_ByteString l = queue_into_ByteString l'
    -> l = l'.
Proof.
  intros;
    destruct (queue_into_ByteString_eq_split_list_bool l);
    destruct (queue_into_ByteString_eq_split_list_bool l').
  eapply split_list_bool_inj.
  rewrite H1, H0 in H; clear H1 H0; injection H.
  intros; destruct (split_list_bool l);
    destruct (split_list_bool l'); simpl in *; subst.
  f_equal.
  destruct s; destruct s0; simpl in *.
  rewrite H1; reflexivity.
Qed.

Lemma ByteString_dequeue_opt_inj :
  forall t m b b',
    ByteString_dequeue b = Some (t, m) ->
    ByteString_dequeue b' = Some (t, m) ->
    b = b'.
Proof.
  intros; rewrite (ByteString_into_queue_eq b),
          (ByteString_into_queue_eq b'),
          !ByteString_dequeue_into_list in *.
  destruct (ByteString_into_queue b) eqn : ?;
    destruct (ByteString_into_queue b') eqn : ?;
    try discriminate; injections.
  revert H0; clear; intros.
  rewrite (queue_into_ByteString_inj l l0); eauto.
Qed.

Lemma length_ByteString_enqueue'
  : forall (b : bool) (b' : ByteString),
    length_ByteString (ByteString_enqueue b b') = length_ByteString b' + 1.
Proof.
  intros; rewrite length_ByteString_enqueue; omega.
Qed.

Lemma ByteString_enqueue_ByteString_enqueue_ByteString
  : forall (b : bool) (b' b'' : ByteString),
    ByteString_enqueue b (ByteString_enqueue_ByteString b' b'') =
    ByteString_enqueue_ByteString b' (ByteString_enqueue b b'').
Proof.
  intros; rewrite (ByteString_into_queue_eq b'),
          (ByteString_into_queue_eq b''),
          !ByteString_enqueue_ByteString_into_list,
          !ByteString_enqueue_into_list.
  replace [b] with
  (ByteString_into_queue (ByteString_enqueue b ByteString_id))
    by reflexivity.
  rewrite !ByteString_enqueue_ByteString_into_list,
  app_assoc; reflexivity.
Qed.

Instance ByteString_QueueTransformerOpt
  : QueueTransformerOpt ByteStringQueueTransformer bool
  :=
  { B_measure f := 1;
    enqueue_opt := ByteString_enqueue;
    dequeue_opt := ByteString_dequeue;
    measure_enqueue := length_ByteString_enqueue';
    measure_dequeue_Some := ByteString_measure_dequeue_Some;
    dequeue_transform_opt := ByteString_dequeue_transform_opt;
    enqueue_transform_opt := ByteString_enqueue_ByteString_enqueue_ByteString;
    dequeue_head_opt := ByteString_dequeue_head_opt;
    dequeue_None := ByteString_dequeue_None;
    dequeue_opt_inj := ByteString_dequeue_opt_inj
  }.
Proof.
  - abstract eauto.
Defined.
