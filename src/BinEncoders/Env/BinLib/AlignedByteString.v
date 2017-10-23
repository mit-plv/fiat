Require Import
        Bedrock.Word
        Coq.NArith.NArith
        Coq.Arith.Arith
        Coq.Numbers.Natural.Peano.NPeano
        Coq.Logic.Eqdep_dec
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.BinLib.Core.

Record ByteString :=
  { padding : nat;
    front : word padding;
    paddingOK : (padding < 8)%nat;
    numBytes : nat;
    byteString : Vector.t char numBytes (* The bytestring. *)
  }.

Definition length_ByteString (bs : ByteString) := padding bs + 8 * numBytes bs.

Definition ByteString_enqueue_full_word
           (b : bool)
           (bs : ByteString)
           (H_eq : padding bs = 7)
  : word 7.
Proof.
  pose proof (front bs) as w; generalize dependent (padding bs);
    intros ?? w; subst; exact w.
Defined.

Global Opaque ByteString_enqueue_word.

Definition ByteString_enqueue
         (b : bool)
         (bs : ByteString)
  : ByteString.
  refine (match (eq_nat_dec (padding bs) 7) with
          | left e =>
            {| front := WO;
               byteString := Vector.append (byteString bs)
                                           (Vector.cons _ ((WS b _)) _ (@Vector.nil _)) |}
          | _ => {| front := WS b (front bs);
                          padding := S (padding bs);
                          byteString := byteString bs |}
          end).
  abstract omega.
  exact (ByteString_enqueue_full_word b bs e).
  abstract (pose proof (paddingOK bs); omega).
Defined.

Fixpoint word_dequeue {sz}
           (w : word (S sz))
  : bool * word sz :=
  match sz return word (S sz) -> bool * word sz with
  | 0 => fun w => (whd w, WO)
  | S sz' =>
    fun w => let (b, w') := word_dequeue (wtl w) in
             (b, WS (whd w) w')
  end w.

Fixpoint CharList_dequeue
         {numBytes}
         (l : Vector.t char (S numBytes))
  : bool * (Vector.t char numBytes) * word 7 :=
  let (b, w') := word_dequeue (Vector.hd l) in
  match numBytes return
        Vector.t char (S numBytes) -> _ with
  | S numBytes' =>
    fun l =>
      match CharList_dequeue (Vector.tl l) with
      | (b', l'', tail) =>
        (b, Vector.cons _ (WS b' w') _ l'', tail)
      end
  | 0 => fun _ => (b, Vector.nil _, w')
  end l.

Definition ByteString_dequeue
         (bs : ByteString)
  : option (bool * ByteString).
  refine (match padding bs as n return
                word n
                -> (n < 8)%nat
                -> _ with
          | 0 =>
            match numBytes bs as nb return
                  Vector.t char nb
                  -> _ with
            | S n' =>
              fun l _ _ =>
                match CharList_dequeue l with
                | (b', l'', tail) =>
                  Some (b', {| front := tail;
                               byteString := l'' |})
                end
            | _ => fun _ _ _ => None
            end (byteString bs)
          | S n =>
            fun front' lt_n =>
              match numBytes bs as nb return
                    Vector.t char nb
                    -> _ with
              | S n' =>
                fun l =>
                  match CharList_dequeue l with
                  | (b', l'', tail) =>
                    let (b, w') := word_dequeue front' in
                    Some (b', {| front := w';
                                 byteString := Vector.append l''
                                                             (Vector.cons _ (WS b tail) _ (@Vector.nil _))
                              |})
                  end
              | _ => fun _ =>
                       let (b, w') := word_dequeue front' in
                       Some (b, {| front := w';
                                   byteString := Vector.nil _ |})
              end (byteString bs)
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

Definition ByteString_enqueue_char (bs : ByteString) (b : char)
  := ByteString_enqueue_word b bs.

Definition ByteString_enqueue_ByteString
           (bs bs' : ByteString)
  : ByteString :=
  let bs'' := Vector.fold_left ByteString_enqueue_char bs (byteString bs') in
  ByteString_enqueue_word (front bs') bs''.

Definition ByteString_id : ByteString.
  refine {| front := WO; byteString := Vector.nil _ |}.
  abstract omega.
Defined.

Definition BoundedByteStringToByteString
           (bs : ByteString)
  : Core.ByteString :=
  {| Core.padding := padding bs;
     Core.front := front bs;
     Core.paddingOK := paddingOK bs;
     Core.byteString := Vector.to_list (byteString bs)
  |}.

Definition ByteStringToBoundedByteString
           (bs : Core.ByteString)
  : ByteString :=
  {| padding := Core.padding bs;
     front := Core.front bs;
     paddingOK := Core.paddingOK bs;
     byteString := Vector.of_list (Core.byteString bs)
  |}.

Lemma Vector_to_list_of_list_eq {A}
  : forall (v : list A),
    Vector.to_list (Vector.of_list v) = v.
Proof.
  induction v; simpl.
  reflexivity.
  replace (a :: v) with (a :: Vector.to_list (Vector.of_list v)).
  reflexivity.
  rewrite IHv; reflexivity.
Qed.

Lemma BoundedByteStringToByteString_ByteStringToBoundedByteString_eq :
  forall bs, BoundedByteStringToByteString (ByteStringToBoundedByteString bs) = bs.
Proof.
  unfold BoundedByteStringToByteString, ByteStringToBoundedByteString; destruct bs; simpl;
    f_equal.
  apply Vector_to_list_of_list_eq.
Qed.

Lemma ByteString_f_equal
  : forall bs bs'
           (p_eq : padding bs' = padding bs)
           (numBytes_eq : numBytes bs' = numBytes bs),
    front bs = eq_rect (padding bs') (fun t : nat => word t) (front bs') (padding bs) p_eq
    -> byteString bs = eq_rect (numBytes bs') _ (byteString bs') (numBytes bs) numBytes_eq
    -> bs = bs'.
Proof.
  destruct bs; destruct bs'; simpl; intros.
  subst.
  f_equal.
  apply le_uniqueness_proof.
Qed.

Lemma length_Vector_to_list {A}
  : forall n (v : Vector.t A n),
    n = length (Vector.to_list v).
Proof.
  induction v; simpl; eauto.
Qed.

Lemma eq_rect_Vector_cons {A}
  : forall n m a v H H',
    eq_rect (S n) (Vector.t A) (VectorDef.cons A a n v) (S m) H =
    Vector.cons _ a _ (eq_rect n (Vector.t A) v _ H').
Proof.
  intros.
  destruct H'; simpl; symmetry;
    apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
Qed.

Lemma ByteStringToBoundedByteString_BoundedByteStringToByteString_eq :
  forall bs, ByteStringToBoundedByteString (BoundedByteStringToByteString bs) = bs.
Proof.
  unfold BoundedByteStringToByteString, ByteStringToBoundedByteString; destruct bs; simpl;
    eapply ByteString_f_equal; simpl.
  apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
  instantiate (1 := length_Vector_to_list _ byteString0).
  clear; induction byteString0; simpl.
  - apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
  - unfold Vector.to_list in *; rewrite IHbyteString0; clear.
    erewrite eq_rect_Vector_cons; f_equal.
    Grab Existential Variables.
    reflexivity.
Qed.

Lemma byteString_f_equal
  : forall bs bs'
           (padding_eq : padding bs' = padding bs)
           (numBytes_eq : numBytes bs' = numBytes bs),
    front bs = (@eq_rect nat (padding bs') (fun t => word t) (front bs') _ padding_eq)
    -> byteString bs = @eq_rect nat (numBytes bs') (Vector.t char) (byteString bs') _ numBytes_eq
    -> bs = bs'.
Proof.
  destruct bs; destruct bs'; simpl; intros.
  subst.
  f_equal.
  apply Core.le_uniqueness_proof.
Qed.

Lemma ByteString_enqueue_ByteStringToBoundedByteString_eq
  : forall (b : bool) (b' : Core.ByteString),
    ByteString_enqueue b (ByteStringToBoundedByteString b') =
    ByteStringToBoundedByteString (Core.ByteString_enqueue b b').
Proof.
  destruct b'; simpl.
  unfold Core.ByteString_enqueue; simpl.
  match goal with
  |- context [match ?z with _ => _ end] => destruct z; simpl
  end.
  - unfold ByteStringToBoundedByteString; simpl.
    unfold ByteString_enqueue; simpl.
    match goal with
      |- context [match ?z with _ => _ end] => destruct z; try omega
    end.
    eapply byteString_f_equal; simpl.
    + instantiate (1 := eq_refl _); reflexivity.
    + unfold ByteString_enqueue_full_word; simpl.
      instantiate (1 := app_length _ _ ); simpl.
      subst; clear.
      unfold eq_rec_r, eq_rec; simpl.
      replace e0 with (eq_refl 7); simpl.
      generalize (app_length byteString0 [WS b front0]).
      induction byteString0; simpl; intros.
      * replace e with (eq_refl 1); auto.
        eapply UIP_dec; eauto with arith.
      * injection e; intros.
        rewrite (IHbyteString0 H); clear.
        erewrite eq_rect_Vector_cons.
        reflexivity.
      * eapply UIP_dec; eauto with arith.
  - unfold ByteStringToBoundedByteString; simpl.
    unfold ByteString_enqueue; simpl.
    match goal with
      |- context [match ?z with _ => _ end] => destruct z; try omega
    end.
    eapply byteString_f_equal; simpl.
    + instantiate (1 := eq_refl); reflexivity.
    + instantiate (1 := eq_refl); reflexivity.
Qed.

Lemma ByteStringToBoundedByteString_enqueue_word
  : forall n (front : word n) bs,
    ByteStringToBoundedByteString (Core.ByteString_enqueue_word front bs)
    = ByteString_enqueue_word front (ByteStringToBoundedByteString bs).
Proof.
  Local Transparent Core.ByteString_enqueue_word.
  induction front0; simpl.
  - reflexivity.
  - intros.
    rewrite <- ByteString_enqueue_ByteStringToBoundedByteString_eq.
    rewrite IHfront0; reflexivity.
  Opaque Core.ByteString_enqueue_word.
Qed.

Lemma fold_left_cons {A B}
  : forall (f : B -> A -> B)
           (l : list A)
           (b : B)
           (a : A),
    fold_left f l (f b a) = fold_left f (a :: l) b.
Proof.
  reflexivity.
Qed.

Lemma ByteString_enqueue_ByteString_ByteStringToBoundedByteString
  : forall bs bs',
    ByteString_enqueue_ByteString (ByteStringToBoundedByteString bs)
                                  (ByteStringToBoundedByteString bs')
    = ByteStringToBoundedByteString (Core.ByteString_enqueue_ByteString bs bs').
Proof.
  intros; revert bs; destruct bs'; revert padding0 front0 paddingOK0.
  unfold ByteStringToBoundedByteString at 2; simpl; intros.
  unfold ByteString_enqueue_ByteString; simpl.
  unfold Core.ByteString_enqueue_ByteString; simpl.
  rewrite ByteStringToBoundedByteString_enqueue_word.
  f_equal; clear.
  symmetry; revert bs; induction byteString0.
  - reflexivity.
  - intros.
    pose proof (IHbyteString0 (Core.ByteString_enqueue_char bs a)).
    replace
      (fold_left Core.ByteString_enqueue_char (a :: byteString0) bs) with
      (fold_left Core.ByteString_enqueue_char byteString0 (Core.ByteString_enqueue_char bs a)).
    rewrite IHbyteString0; simpl.
    f_equal.
    apply ByteStringToBoundedByteString_enqueue_word.
    apply fold_left_cons.
Qed.

Lemma length_ByteString_ByteStringToBoundedByteString_eq
  : forall bs,
    length_ByteString (ByteStringToBoundedByteString bs) =
    Core.length_ByteString bs.
Proof.
  destruct bs; simpl.
  reflexivity.
Qed.

Lemma BoundedByteStringToByteString_ByteString_id_eq
  : BoundedByteStringToByteString ByteString_id = Core.ByteString_id.
Proof.
  unfold ByteString_id, Core.ByteString_id; simpl.
  unfold BoundedByteStringToByteString; simpl.
  f_equal.
  apply le_uniqueness_proof.
Qed.

Instance ByteStringQueueTransformer : Transformer ByteString.
Proof.
  refine {| transform := ByteString_enqueue_ByteString;
            bin_measure := length_ByteString;
            transform_id := ByteString_id |}.
  - abstract (intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b),
                      <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b'),
                      ByteString_enqueue_ByteString_ByteStringToBoundedByteString,
                      !length_ByteString_ByteStringToBoundedByteString_eq,
                      ByteString_enqueue_ByteString_measure;
              reflexivity).
  - abstract (intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq ByteString_id),
                      <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq l),
                      ByteString_enqueue_ByteString_ByteStringToBoundedByteString,
                      BoundedByteStringToByteString_ByteString_id_eq,
                      ByteString_enqueue_ByteString_id_left; reflexivity).
  - abstract (intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq ByteString_id),
                      <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq l),
                      ByteString_enqueue_ByteString_ByteStringToBoundedByteString,
                      BoundedByteStringToByteString_ByteString_id_eq,
                      ByteString_enqueue_ByteString_id_right; reflexivity).
  - abstract (intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq l),
                     <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq m),
                     <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq n),
                     !ByteString_enqueue_ByteString_ByteStringToBoundedByteString,
                     ByteString_enqueue_ByteString_assoc; reflexivity).
Defined.


Lemma ByteString_enqueue_ByteStringToBoundedByteString_eq'
  : forall (b : bool) (b' : ByteString),
    Core.ByteString_enqueue b (BoundedByteStringToByteString b') =
    BoundedByteStringToByteString (ByteString_enqueue b b').
Proof.
  destruct b'; simpl.
  unfold Core.ByteString_enqueue; simpl.
  match goal with
    |- context [match ?z with _ => _ end] => destruct z; try omega
  end.
  - unfold ByteStringToBoundedByteString; simpl.
    unfold ByteString_enqueue; simpl.
    match goal with
      |- context [match ?z with _ => _ end] => destruct z; try omega
    end.
    unfold  BoundedByteStringToByteString; simpl.
    f_equal.
    + apply le_uniqueness_proof.
    + unfold ByteString_enqueue_full_word; simpl.
      subst; clear.
      unfold eq_rec_r, eq_rec; simpl.
      replace e0 with (eq_refl 7); simpl.
      induction byteString0; simpl; intros.
      * reflexivity.
      * unfold Vector.to_list.
        f_equal.
        apply IHbyteString0.
      * eapply UIP_dec; eauto with arith.
  - unfold BoundedByteStringToByteString; simpl.
    unfold ByteString_enqueue; simpl.
    match goal with
      |- context [match ?z with _ => _ end] => destruct z; try omega
    end.
    f_equal.
    + apply le_uniqueness_proof.
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

Fixpoint ByteString_into_queue' {sz}
           (chars : Vector.t char sz)
           {struct chars} : list bool :=
  match chars return list bool with
  | Vector.nil => [ ]
  | Vector.cons char' _ chars' =>
    app (wordToQueue char')
      (ByteString_into_queue' chars')
  end.

Definition ByteString_into_queue
           (bs : ByteString)
  : list bool :=
  app (ByteString_into_queue' (byteString bs)) (wordToQueue (front bs)).

Definition build_aligned_ByteString
           {numBytes}
           (v : Vector.t char numBytes)
  : ByteString.
  refine {| front := WO;
            byteString := v |}.
  abstract omega.
Defined.

Lemma build_aligned_ByteString_append
      {numBytes'}
  : forall (v' : Vector.t char numBytes') {numBytes} (v : Vector.t char numBytes),
    build_aligned_ByteString (Vector.append v v') = ByteString_enqueue_ByteString (build_aligned_ByteString v) (build_aligned_ByteString v').
Proof.
  simpl; intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq (build_aligned_ByteString v)),
                 <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq (build_aligned_ByteString v')),
                 ByteString_enqueue_ByteString_ByteStringToBoundedByteString.
  unfold build_aligned_ByteString; simpl.
  unfold BoundedByteStringToByteString; simpl.
  erewrite <- massage_queue_into_ByteString.
  unfold ByteStringToBoundedByteString; simpl.
  assert (Datatypes.length
            ((Vector.to_list v) ++ (Vector.to_list v'))
          = numBytes0 + numBytes').
  rewrite app_length, <- !length_Vector_to_list; reflexivity.
  eapply byteString_f_equal with (numBytes_eq := H); simpl.
  apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
  induction v; simpl in *.
  induction v'.
  - apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
  - simpl in H; injection H; intros.
    simpl; rewrite eq_rect_Vector_cons with (H' := H0); simpl.
    f_equal.
    eapply IHv'.
  -  simpl in H; injection H; intros.
     simpl; rewrite eq_rect_Vector_cons with (H' := H0); simpl.
     f_equal.
     eapply IHv.
     Grab Existential Variables.
     reflexivity.
     omega.
Qed.

Lemma build_aligned_ByteString_cons
      {numBytes}
  : forall (v : Vector.t char (S numBytes)),
    (build_aligned_ByteString v) = ByteString_enqueue_ByteString (build_aligned_ByteString (Vector.cons _ (Vector.hd v) _ (Vector.nil _))) (build_aligned_ByteString (Vector.tl v)).
Proof.
  intros; rewrite <- (build_aligned_ByteString_append (Vector.tl v)
                                                      (Vector.cons _ (Vector.hd v) _ (Vector.nil _))).
  pattern numBytes, v; apply VectorDef.caseS; simpl; intros; reflexivity.
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
    pose proof (build_aligned_ByteString_append byteString0 (Vector.nil _)).
    unfold ByteString_enqueue_ByteString in H; simpl in H.
    unfold build_aligned_ByteString in H; simpl in H.
    replace paddingOK0 with (build_aligned_ByteString_subproof numBytes0 byteString0)
      by apply le_uniqueness_proof; rewrite H.
    simpl.
    rewrite fold_left_rev_right.
    replace {|
    padding := 0;
    front := WO;
    paddingOK := build_aligned_ByteString_subproof 0 (Vector.nil char);
    numBytes := 0;
    byteString := Vector.nil char |} with ByteString_id.
    generalize ByteString_id; clear.
    induction byteString0.
    + simpl; eauto.
    + intros; simpl Vector.fold_left.
      rewrite IHbyteString0.
      simpl ByteString_into_queue'.
      rewrite <- !fold_left_cons.
      reflexivity.
    + eapply byteString_f_equal; simpl;
        instantiate (1 := eq_refl); reflexivity.
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

Lemma ByteStringToBoundedByteString_into_queue_eq
  : forall l,
    ByteStringToBoundedByteString (Core.queue_into_ByteString l)
    = queue_into_ByteString l.
Proof.
  unfold queue_into_ByteString, Core.queue_into_ByteString.
  intros.
  replace Core.ByteString_id with
  (BoundedByteStringToByteString ByteString_id)
    by apply BoundedByteStringToByteString_ByteString_id_eq.
  generalize ByteString_id.
  induction l; intros.
  - apply ByteStringToBoundedByteString_BoundedByteStringToByteString_eq.
  - rewrite <- !fold_left_cons; simpl.
    rewrite <- IHl.
    rewrite ByteString_enqueue_ByteStringToBoundedByteString_eq'; reflexivity.
Qed.

Lemma BoundedByteStringToByteString_into_queue_eq
  : forall l,
    Core.queue_into_ByteString l = BoundedByteStringToByteString (queue_into_ByteString l).
Proof.
  unfold queue_into_ByteString, Core.queue_into_ByteString.
  intros.
  replace Core.ByteString_id with
  (BoundedByteStringToByteString ByteString_id)
    by apply BoundedByteStringToByteString_ByteString_id_eq.
  generalize ByteString_id.
  induction l; intros.
  - reflexivity.
  - rewrite <- !fold_left_cons; simpl.
    rewrite <- IHl.
    rewrite ByteString_enqueue_ByteStringToBoundedByteString_eq'; reflexivity.
Qed.

Lemma ByteStringToBoundedByteString_into_queue_eq'
  : forall bs,
    ByteString_into_queue (ByteStringToBoundedByteString bs)
    = Core.ByteString_into_queue bs.
Proof.
  destruct bs; unfold ByteStringToBoundedByteString; simpl.
  unfold ByteString_into_queue, Core.ByteString_into_queue; simpl.
  f_equal.
  clear; induction byteString0; simpl; eauto.
  rewrite IHbyteString0; reflexivity.
Qed.

Fixpoint split_Vector_bool
         (l : list bool)
  : {n : nat & Vector.t char n} * {n : nat & word n} :=
  match l return {n : nat & Vector.t char n} * {n : nat & word n} with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l' =>
    let (l'', back) := split_Vector_bool l' in
    (existT _ _ (Vector.cons _ (WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))) _ (projT2 l'')), back)
  | [b0; b1; b2; b3; b4; b5; b6] =>
    (existT _ _ (Vector.nil _), existT _ _ (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))))
  | [b0; b1; b2; b3; b4; b5] =>
    (existT _ _ (Vector.nil _), existT _ _ (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))
  | [b0; b1; b2; b3; b4] =>
    (existT _ _ (Vector.nil _), existT _ _ (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))
  | [b0; b1; b2; b3] =>
    (existT _ _ (Vector.nil _), existT _ _ (WS b3 (WS b2 (WS b1 (WS b0 WO)))))
  | [b0; b1; b2] =>
    (existT _ _ (Vector.nil _), existT _ _ (WS b2 (WS b1 (WS b0 WO))))
  | [b0; b1] =>
    (existT _ _ (Vector.nil _), existT _ _ (WS b1 (WS b0 WO)))
  | [b0] =>
    (existT _ _ (Vector.nil _), existT _ _  (WS b0 WO))
  | _ => (existT _ _ (Vector.nil _), existT _ _ WO)
  end.

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

Lemma Vector_append_nil_r {A}
  : forall (sz : nat)
           (v : Vector.t A sz),
    v = eq_rect (sz + 0) _ (Vector.append v (Vector.nil A)) sz (sym_eq (plus_n_O _)).
Proof.
  induction v; simpl;
    try (rewrite <- eq_rect_eq_dec; eauto with arith).
  rewrite IHv.
  erewrite eq_rect_Vector_cons; f_equal.
  repeat f_equal; eauto.
Qed.

Lemma fold_left_enqueue_simpl
  : forall b0 b1 b2 b3 b4 b5 b6 b7 l sz (byteString0 : Vector.t _ sz) paddingOK0,
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
     byteString := Vector.append byteString0
                                 (Vector.cons _ (WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))) _ (Vector.nil _)) |}.
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

Lemma queue_into_ByteString_eq_split_Vector_bool
  : forall l,
    exists paddingOK',
    queue_into_ByteString l =
    {|
      front := projT2 (snd (split_Vector_bool l));
      paddingOK := paddingOK';
      byteString := projT2 (fst (split_Vector_bool l)) |}.
Proof.
  intro; generalize (le_refl (length l)); remember (length l).
  unfold queue_into_ByteString.
  replace (projT2 (fst (split_Vector_bool l))) with
  (Vector.append (byteString ByteString_id) (projT2 (fst (split_Vector_bool l)))) by reflexivity.
  assert (padding ByteString_id = 0) as H' by reflexivity;
    revert H'.
  assert (forall sz bs,
             padding bs = 0 ->
             numBytes bs = sz ->
             (n <= n)%nat ->
             exists paddingOK' : (projT1 (snd (split_Vector_bool l)) < 8)%nat,
               fold_left (fun (bs : ByteString) (b : bool) => ByteString_enqueue b bs) l bs =
               {|
                 padding := projT1 (snd (split_Vector_bool l));
                 front := projT2 (snd (split_Vector_bool l));
                 paddingOK := paddingOK';
                 numBytes := _ + projT1 (fst (split_Vector_bool l));
                 byteString := Vector.append (byteString bs) (projT2 (fst (split_Vector_bool l))) |});
    [ | intros; eapply (H 0); eauto ].
  setoid_rewrite Heqn at 1; clear Heqn; revert l;
    induction n.
  - intros; destruct l; simpl; intros.
    + eexists (lt_0_Sn _).
      symmetry in H0.
      symmetry in H.
      destruct bs; simpl in *. subst.
      eapply byteString_f_equal with (padding_eq :=  _); simpl.
      * instantiate (1 := eq_refl); simpl; shatter_word front0; reflexivity.
      * instantiate (1 := sym_eq (plus_n_O numBytes0)).
        eauto using Vector_append_nil_r.
    + inversion H1.
  - intros l sz b H0 H'' H;
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
                     eauto using app_nil_r, le_uniqueness_proof;
                     simpl; intros;
              eapply byteString_f_equal; simpl;
                try (instantiate (1 := eq_refl); reflexivity);
                eauto using Vector_append_nil_r]
      end.
    + unfold queue_into_ByteString, ByteString_id;
        simpl; unfold ByteString_enqueue; simpl; repeat f_equal.
      eexists (lt_0_Sn _).
      symmetry in H0.
      symmetry in H''.
      destruct b; simpl in *. subst.
      eapply byteString_f_equal with (padding_eq :=  _); simpl.
      * instantiate (1 := eq_refl); simpl; shatter_word front0; reflexivity.
      * instantiate (1 := sym_eq (plus_n_O numBytes0)).
        eauto using Vector_append_nil_r.
    + destruct (split_Vector_bool l) eqn : ?.
      destruct b.
      destruct (IHn l (S sz) {| front := WO;
                         paddingOK := lt_0_Sn _;
                         byteString :=
                           Vector.append byteString0 (Vector.cons _ (WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))) _ (Vector.nil _)) |}).
      simpl in *; omega.
      simpl in *; omega.
      simpl in *; omega.
      simpl split_Vector_bool.
      revert x H0 H1; rewrite Heqp; intros; clear Heqp.
      exists x.
      simpl byteString.
      unfold fst.
      simpl in H0.
      revert front0 paddingOK0 H''.
      rewrite H0; intros.
      shatter_word front0.
      rewrite fold_left_enqueue_simpl, H1; intros; simpl.
      assert (numBytes0 + (S (projT1 s)) = numBytes0 + 1 + projT1 s) by omega.
      eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      instantiate (1 := H2).
      clear; induction byteString0; simpl; intros.
      * erewrite eq_rect_Vector_cons; f_equal.
        instantiate (1 := eq_refl); reflexivity.
      * erewrite eq_rect_Vector_cons; f_equal.
        erewrite IHbyteString0; f_equal.
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

Lemma Vector_fold_left_app
  : forall (A B : Type) (f : A -> B -> A) sz (l : Vector.t B sz) sz' (l' : Vector.t B sz') (i : A),
    Vector.fold_left f i (Vector.append l l') = Vector.fold_left f (Vector.fold_left f i l) l'.
Proof.
  induction l; simpl; eauto.
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
  - unfold ByteString_enqueue_ByteString; simpl; subst.
    intros; rewrite Vector_fold_left_app;
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
    + rewrite ByteStringQueueTransformer_subproof1,
      app_nil_r; reflexivity.
    + inversion H.
  - intros; rewrite queue_into_ByteString_app.
    rewrite <- (rev_involutive l') in *.
    clear IHn H.
    induction (rev l'); simpl.
    + rewrite ByteStringQueueTransformer_subproof1; reflexivity.
    + rewrite <- ByteString_enqueue_into_list.
      rewrite fold_left_app; simpl.
      rewrite <- IHl0.
      apply ByteString_enqueue_ByteString_enqueue.
Qed.

Lemma Vector_append_nil_r' {A}
  : forall sz (v : Vector.t A sz),
    Vector.append v (VectorDef.nil A) = eq_rect sz (Vector.t A) v (sz + 0) (plus_n_O sz).
Proof.
  induction v; simpl;
    try (rewrite <- eq_rect_eq_dec; eauto with arith).
  rewrite IHv.
  erewrite eq_rect_Vector_cons; f_equal.
Qed.

Lemma massage_queue_into_ByteString
  : forall n w1
           paddingOK' paddingOK'' paddingOK'''
           sz' (l' : Vector.t _ sz')
           sz (l : Vector.t _ sz),
    {|
      padding := n;
      front := w1;
      paddingOK := paddingOK';
      byteString := Vector.append l l' |} =
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
  - simpl; intros.
    unfold ByteString_enqueue_ByteString; simpl.
    rewrite (Vector_append_nil_r _ l) at -1.
    destruct n as [ | [ | [ | [ | [ | [ | [ | [ | ] ] ] ] ] ] ] ];
      try solve [inversion paddingOK'];
      try shatter_word w1; simpl;
        unfold queue_into_ByteString; simpl; repeat f_equal.
    + eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      instantiate (1 := plus_n_O _).
      rewrite  Vector_append_nil_r' at 1.
      simpl.
      f_equal.
      apply Vector_append_nil_r.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue,
      ByteString_enqueue; simpl.
      eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      instantiate (1 := plus_n_O _).
      rewrite  Vector_append_nil_r' at 1.
      simpl.
      f_equal.
      apply Vector_append_nil_r.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue,
      ByteString_enqueue; simpl.
      eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      instantiate (1 := plus_n_O _).
      rewrite  Vector_append_nil_r' at 1.
      simpl.
      f_equal.
      apply Vector_append_nil_r.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue;
        simpl.
      unfold ByteString_enqueue at 3; simpl;
        unfold ByteString_enqueue at 2; simpl;
          unfold ByteString_enqueue at 1; simpl.
      eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      instantiate (1 := plus_n_O _).
      rewrite  Vector_append_nil_r' at 1.
      simpl.
      f_equal.
      apply Vector_append_nil_r.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue; simpl.
      unfold ByteString_enqueue at 4; simpl.
        unfold ByteString_enqueue at 3; simpl;
          unfold ByteString_enqueue at 2; simpl.
        unfold ByteString_enqueue at 1; simpl.
        eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      instantiate (1 := plus_n_O _).
      rewrite  Vector_append_nil_r' at 1.
      simpl.
      f_equal.
      apply Vector_append_nil_r.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue; simpl.
      unfold ByteString_enqueue at 5; simpl;
        unfold ByteString_enqueue at 4; simpl;
          unfold ByteString_enqueue at 3; simpl;
            unfold ByteString_enqueue at 2; simpl;
              unfold ByteString_enqueue at 1; simpl.
      eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      instantiate (1 := plus_n_O _).
      rewrite  Vector_append_nil_r' at 1.
      simpl.
      f_equal.
      apply Vector_append_nil_r.
    + unfold queue_into_ByteString, ByteString_id, ByteString_dequeue; simpl.
      unfold ByteString_enqueue at 6; simpl;
        unfold ByteString_enqueue at 5; simpl;
          unfold ByteString_enqueue at 4; simpl;
            unfold ByteString_enqueue at 3; simpl;
              unfold ByteString_enqueue at 2; simpl;
                unfold ByteString_enqueue at 1; simpl.
      eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      instantiate (1 := plus_n_O _).
      rewrite  Vector_append_nil_r' at 1.
      simpl.
      f_equal.
      apply Vector_append_nil_r.
    + unfold queue_into_ByteString, ByteString_id; simpl.
      unfold ByteString_enqueue at 7; simpl;
        unfold ByteString_enqueue at 6; simpl;
          unfold ByteString_enqueue at 5; simpl;
            unfold ByteString_enqueue at 4; simpl;
              unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                  unfold ByteString_enqueue at 1; simpl.
      eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      instantiate (1 := plus_n_O _).
      rewrite  Vector_append_nil_r' at 1.
      simpl.
      f_equal.
      apply Vector_append_nil_r.
    + omega.
  - intros.
    pose proof (IHl' _ (Vector.append l (Vector.cons _ h _ (Vector.nil _)))) as e; simpl in e.
    unfold ByteString_enqueue_ByteString in *; simpl in *.
    revert e.
    unfold ByteString_enqueue_char at 3; simpl.
    unfold ByteString_enqueue at 7; simpl;
        unfold ByteString_enqueue at 6; simpl;
          unfold ByteString_enqueue at 5; simpl;
            unfold ByteString_enqueue at 4; simpl;
              unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                  unfold ByteString_enqueue at 1; simpl.
    unfold char in *.
    shatter_word h.
    simpl.
    intros H'.
    assert (sz + 1 + n0 = sz + (S n0)) by omega.
    transitivity {|
       padding := n;
       front := w1;
       paddingOK := paddingOK';
       numBytes := sz + 1 + n0;
       byteString := Vector.append
                       (Vector.append l
                          (Vector.cons (word 8) (WS x (WS x0 (WS x1 (WS x2 (WS x3 (WS x4 (WS x5 (WS x6 WO))))))))
                             0 (Vector.nil (word 8)))) l' |}.
    * eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      instantiate (1 := H7).
      clear; induction l; simpl; intros.
      erewrite eq_rect_Vector_cons; f_equal.
      instantiate (1 := eq_refl); reflexivity.
      erewrite eq_rect_Vector_cons; f_equal.
      erewrite IHl; f_equal.
    * rewrite H'.
      f_equal; f_equal.
      eapply byteString_f_equal; simpl;
      try (instantiate (1 := eq_refl); reflexivity).
      Grab Existential Variables.
      omega.
Qed.

Lemma ByteString_dequeue_into_list
  : forall (l : list bool),
    ByteString_dequeue (queue_into_ByteString l)
    = match l with
      | b :: l' => Some (b, queue_into_ByteString l')
      | _ => None
      end.
Proof.
  intro; destruct (queue_into_ByteString_eq_split_Vector_bool l);
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
      destruct (split_Vector_bool l) eqn : ? ; simpl in *.
      simpl in H.
      destruct (queue_into_ByteString_eq_split_Vector_bool l).
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
      destruct (split_Vector_bool l); simpl in *.
      simpl in H2; revert H2; injection Heqp; clear.
      intros G G'.
      revert x x0; try rewrite G, G'; subst; intros.
      unfold ByteString_dequeue in *;
        repeat match goal with
                 |- context [ByteString_enqueue_subproof0 ?z ?q ?m] =>
                 generalize (ByteString_enqueue_subproof0 z q m); intros; simpl in *
               | |- context [ByteString_enqueue_subproof ?z ?q ?m] =>
                 generalize (ByteString_enqueue_subproof z q m); intros; simpl in *
               end.
      destruct s as [[ | ?] ? ]; simpl in *.
      destruct s0 as [[ | ?] ? ]; simpl in *.
      * destruct (CharList_dequeue (Vector.cons _ (WS b (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))))
                                                _ (Vector.nil _)))
          as [ [? ?] ] eqn : ? ;
          try discriminate.
        destruct l; simpl in H2; try discriminate; injections.
        simpl.
        f_equal; f_equal;
          eapply byteString_f_equal; simpl;
            try (instantiate (1 := eq_refl); reflexivity).
      * destruct (word_dequeue w).
        destruct l; try discriminate; injections;
          simpl.
        match goal with
          |- context[fold_left _ _ ?q] =>
          replace q
          with
          (queue_into_ByteString [b0; b1; b2; b3; b4; b5; b6; b8]);
            [ | unfold queue_into_ByteString; simpl;
                unfold ByteString_enqueue at 7; simpl;
                unfold ByteString_enqueue at 6; simpl;
                unfold ByteString_enqueue at 5; simpl;
                unfold ByteString_enqueue at 4; simpl;
                unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                unfold ByteString_enqueue at 1; simpl ]
        end.
        rewrite <- queue_into_ByteString_app.
        f_equal; f_equal.
        rewrite <- ByteString_enqueue_ByteString_into_list.
        rewrite <- H.
        clear.
        unfold queue_into_ByteString at 1; simpl.
        unfold ByteString_enqueue at 7; simpl;
        unfold ByteString_enqueue at 6; simpl;
          unfold ByteString_enqueue at 5; simpl;
            unfold ByteString_enqueue at 4; simpl;
              unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                  unfold ByteString_enqueue at 1; simpl.
        erewrite <- massage_queue_into_ByteString.
        eapply byteString_f_equal; simpl;
          instantiate (1 := eq_refl); try reflexivity.
        eapply byteString_f_equal; simpl;
          instantiate (1 := eq_refl); try reflexivity.
      * destruct s0 as [[ | ?] ? ]; simpl in *.
        destruct (CharList_dequeue t) as [ [? ?] ? ] eqn : ? .
        destruct l; try discriminate; injections;
          simpl.
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
        destruct l; try discriminate; injections;
          simpl.
        destruct (CharList_dequeue t) as [ [? ?] ? ] eqn : ? ;
          try discriminate; destruct (word_dequeue w).
        discriminate.
        destruct (CharList_dequeue t) as [ [? ?] ? ] eqn : ? ;
          try discriminate; destruct (word_dequeue w).
        match goal with
          |- context[fold_left _ _ ?q] =>
          replace q
          with
          (queue_into_ByteString [b0; b1; b2; b3; b4; b5; b6; b8]);
            [ | unfold queue_into_ByteString; simpl;
                unfold ByteString_enqueue at 7; simpl;
                unfold ByteString_enqueue at 6; simpl;
                unfold ByteString_enqueue at 5; simpl;
                unfold ByteString_enqueue at 4; simpl;
                unfold ByteString_enqueue at 3; simpl;
                unfold ByteString_enqueue at 2; simpl;
                unfold ByteString_enqueue at 1; simpl ]
        end.
        rewrite <- queue_into_ByteString_app.
        rewrite <- ByteString_enqueue_ByteString_into_list.
        f_equal; f_equal.
        injection H2; intros.
        rewrite <- H.
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
        simpl.
        eapply byteString_f_equal; simpl;
        instantiate (1 := eq_refl); try reflexivity.
        simpl.
        injection H2; intros; subst.
        reflexivity.
Qed.

Lemma ByteString_dequeue_ByteStringToBoundedByteString_eq
  : forall (b' : Core.ByteString),
    ByteString_dequeue (ByteStringToBoundedByteString b') =
    Ifopt (Core.ByteString_dequeue b')
    as bbs
         Then Some (fst bbs, ByteStringToBoundedByteString (snd bbs))
         Else None.
Proof.
  intros; rewrite (Core.ByteString_into_queue_eq b').
  rewrite ByteStringToBoundedByteString_into_queue_eq.
  rewrite ByteString_dequeue_into_list.
  rewrite Core.ByteString_dequeue_into_list.
  destruct (Core.ByteString_into_queue b'); simpl;
  rewrite <- ?ByteStringToBoundedByteString_into_queue_eq; eauto.
Qed.

Lemma ByteString_dequeue_ByteStringToBoundedByteString_eq'
  : forall (b' : ByteString),
    Core.ByteString_dequeue (BoundedByteStringToByteString b') =
    Ifopt (ByteString_dequeue b')
    as bbs
         Then Some (fst bbs, BoundedByteStringToByteString (snd bbs))
         Else None.
Proof.
  intros.
  rewrite (Core.ByteString_into_queue_eq (BoundedByteStringToByteString b')).
  rewrite Core.ByteString_dequeue_into_list.
  rewrite (ByteString_into_queue_eq b').
  rewrite ByteString_dequeue_into_list.
  rewrite <- ByteString_into_queue_eq.
  rewrite <- ByteStringToBoundedByteString_into_queue_eq'.
  rewrite ByteStringToBoundedByteString_BoundedByteStringToByteString_eq.
  destruct (ByteString_into_queue b'); simpl;
    rewrite  ?BoundedByteStringToByteString_into_queue_eq; reflexivity.
Qed.

Lemma AlignedByteString_dequeue_opt
  : forall (t : bool) (b b' b'' : ByteString),
    ByteString_dequeue b = Some (t, b')
    -> ByteString_dequeue (transform b b'') = Some (t, transform b' b'').
Proof.
   simpl; intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b),
                   <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b') in *;
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b'').
    rewrite ByteString_dequeue_ByteStringToBoundedByteString_eq in H;
    destruct (Core.ByteString_dequeue (BoundedByteStringToByteString b)) eqn : ?; simpl in *;
      try discriminate; destruct p; simpl in *.
    injection H; intros; subst.
    apply ByteString_dequeue_transform_opt with (b'' := BoundedByteStringToByteString b'') in Heqo;
          simpl in *.
    rewrite ByteString_enqueue_ByteString_ByteStringToBoundedByteString.
    rewrite ByteString_dequeue_ByteStringToBoundedByteString_eq.
    rewrite Heqo; simpl.
    rewrite ByteString_enqueue_ByteString_ByteStringToBoundedByteString.
    f_equal; f_equal; f_equal; f_equal.
    rewrite ByteStringToBoundedByteString_BoundedByteStringToByteString_eq in H.
    injection H; intros; subst.
    rewrite BoundedByteStringToByteString_ByteStringToBoundedByteString_eq; reflexivity.
Qed.

Instance ByteString_QueueTransformerOpt
  : QueueTransformerOpt ByteStringQueueTransformer bool.
Proof.
refine {| B_measure f := 1;
          enqueue_opt := ByteString_enqueue;
          dequeue_opt := ByteString_dequeue |}.
  - abstract eauto.
  - abstract (simpl; intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b'),
                             ByteString_enqueue_ByteStringToBoundedByteString_eq,
                             !length_ByteString_ByteStringToBoundedByteString_eq,
                             length_ByteString_enqueue';
              reflexivity).
  - abstract (simpl; intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b) in *;
              rewrite ByteString_dequeue_ByteStringToBoundedByteString_eq in H;
              destruct (Core.ByteString_dequeue (BoundedByteStringToByteString b)) eqn : ?; simpl in *;
              try discriminate; injections;
              destruct p; apply ByteString_measure_dequeue_Some in Heqo;
              simpl in Heqo;
              rewrite length_ByteString_ByteStringToBoundedByteString_eq; simpl in *;
              first [ rewrite Heqo; reflexivity
                    | rewrite <- Heqo; rewrite <- length_Vector_to_list, <- length_ByteString_ByteStringToBoundedByteString_eq,
                                       ByteStringToBoundedByteString_BoundedByteStringToByteString_eq; reflexivity]).
  - apply AlignedByteString_dequeue_opt.
  - abstract (simpl; intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b'),
                             <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b''),
                             !ByteString_enqueue_ByteString_ByteStringToBoundedByteString,
                             ByteString_enqueue_ByteStringToBoundedByteString_eq,
                             ByteString_enqueue_ByteString_enqueue_ByteString,
                             !ByteStringToBoundedByteString_BoundedByteStringToByteString_eq,
                             ByteString_enqueue_ByteStringToBoundedByteString_eq',
                             <- ByteString_enqueue_ByteString_ByteStringToBoundedByteString,
                             !ByteStringToBoundedByteString_BoundedByteStringToByteString_eq;
              reflexivity).
  - abstract (simpl; intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq ByteString_id),
                             ByteString_enqueue_ByteStringToBoundedByteString_eq,
                             ByteString_dequeue_ByteStringToBoundedByteString_eq;
              replace (BoundedByteStringToByteString ByteString_id)
              with Core.ByteString_id;
              [rewrite ByteString_dequeue_head_opt; reflexivity
              | unfold ByteString_id, Core.ByteString_id, BoundedByteStringToByteString; simpl;
                f_equal;
                apply le_uniqueness_proof]).
  - abstract reflexivity.
  - intros ? ? ? ?.
    simpl; intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b),
                   <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b'),
                   !ByteString_dequeue_ByteStringToBoundedByteString_eq in *.
    destruct (Core.ByteString_dequeue (BoundedByteStringToByteString b)) eqn : ?;
      simpl in *; try discriminate.
    destruct (Core.ByteString_dequeue (BoundedByteStringToByteString b')) eqn : ?;
      simpl in *; try discriminate.
    destruct p; destruct p0.
    simpl in *; rewrite <- H in H0.
    rewrite (ByteString_dequeue_opt_inj (BoundedByteStringToByteString b) (BoundedByteStringToByteString b') Heqo).
    reflexivity.
    rewrite Heqo0; repeat f_equal.
    injection H0; eauto.
    assert (ByteStringToBoundedByteString b3 = ByteStringToBoundedByteString b1) by congruence.
    rewrite <- (BoundedByteStringToByteString_ByteStringToBoundedByteString_eq b3),
    <-  (BoundedByteStringToByteString_ByteStringToBoundedByteString_eq b1), H1.
    reflexivity.
Defined.

Lemma DecodeBindOpt_assoc:
  forall (A B C D : Type)
         (a_opt : option (A * B))
         (f : A -> B -> option (C * B))
         (g : C -> B -> option (D * B)),
    (`(c, b) <- (`(a, b) <- a_opt; f a b); g c b) =
    (`(a, b) <- a_opt;
      `(c, b) <- f a b;
      g c b).
Proof.
  destruct a_opt as [ [? ?] | ]; simpl; intros.
  - destruct (f a b) as [ [? ?] | ]; reflexivity.
  - reflexivity.
Qed.

Lemma DecodeBindOpt_under_bind:
  forall (A B C : Type) (a_opt : option (A * B)) (f f' : A -> B -> option (C * B)),
  (forall (a : A) (b : B), f a b = f' a b) -> (`(a, b) <- a_opt;
                                                 f a b ) = (`(a, b) <- a_opt;
                                                              f' a b).
Proof.
  destruct a_opt as [ [? ?] | ]; simpl; intros; eauto.
Qed.

Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.


Require Import Fiat.BinEncoders.Env.Lib2.WordOpt.

Lemma aligned_decode_char_eq
      {numBytes}
  : forall (v : Vector.t char (S numBytes)),
    WordOpt.decode_word' (transformerUnit := ByteString_QueueTransformerOpt) 8 (build_aligned_ByteString v)
    = Some (Vector.hd v, build_aligned_ByteString (Vector.tl v)).
Proof.
  simpl; intros.
  etransitivity.
  apply DecodeBindOpt_under_bind; intros; set_evars; rewrite !DecodeBindOpt_assoc.
  repeat (unfold H; apply DecodeBindOpt_under_bind; intros; set_evars; rewrite !DecodeBindOpt_assoc).
  unfold H5; higher_order_reflexivity.
  simpl.
  pattern numBytes, v; eapply Vector.caseS; intros; simpl; clear v numBytes.
  replace (build_aligned_ByteString t) with (ByteString_enqueue_ByteString ByteString_id (build_aligned_ByteString t)).
  unfold char in h.
  shatter_word h.
  pose proof (@dequeue_transform_opt _ _ _ ByteString_QueueTransformerOpt).
  rewrite build_aligned_ByteString_cons; simpl.
  simpl in H7.
  erewrite H7 with (t := x6)
                     (b' := {| front := WS x (WS x0 (WS x1 (WS x2 (WS x3 (WS x4 (WS x5 WO))))));
                               byteString := Vector.nil _ |}); simpl.
  erewrite H7 with (t := x5)
                     (b' := {| front := WS x (WS x0 (WS x1 (WS x2 (WS x3 (WS x4 WO)))));
                               byteString := Vector.nil _ |}); simpl.
  erewrite H7 with (t := x4)
                     (b' := {| front := WS x (WS x0 (WS x1 (WS x2 (WS x3 WO))));
                               byteString := Vector.nil _ |}); simpl.
  erewrite H7 with (t := x3)
                     (b' := {| front := WS x (WS x0 (WS x1 (WS x2 WO)));
                               byteString := Vector.nil _ |}); simpl.
  erewrite H7 with (t := x2)
                     (b' := {| front := WS x (WS x0 (WS x1 WO));
                               byteString := Vector.nil _ |}); simpl.
  erewrite H7 with (t := x1)
                     (b' := {| front := WS x (WS x0 WO);
                               byteString := Vector.nil _ |}); simpl.
  erewrite H7 with (t := x0)
                     (b' := {| front := WS x WO;
                            byteString := Vector.nil _ |}); simpl.
  erewrite H7 with (t := x)
                     (b' := {| front := WO;
                            byteString := Vector.nil _ |}); simpl.
  reflexivity.
  unfold dequeue_opt.
  simpl.
  compute; repeat f_equal; apply Core.le_uniqueness_proof.
  compute; repeat f_equal; apply Core.le_uniqueness_proof.
  compute; repeat f_equal; apply Core.le_uniqueness_proof.
  compute; repeat f_equal; apply Core.le_uniqueness_proof.
  compute; repeat f_equal; apply Core.le_uniqueness_proof.
  compute; repeat f_equal; apply Core.le_uniqueness_proof.
  compute; repeat f_equal; apply Core.le_uniqueness_proof.
  unfold build_aligned_ByteString.
  unfold ByteString_dequeue; simpl.
  repeat f_equal; apply Core.le_uniqueness_proof.
  apply (@transform_id_left _ ByteStringQueueTransformer).
Qed.



Fixpoint Vector_split {A} (n m : nat) (v : Vector.t A (n + m)) :
  Vector.t A n * Vector.t A m :=
  match n return Vector.t A (n + m)
                 -> Vector.t A n * Vector.t A m with
  | 0 => fun v => (Vector.nil _, v)
  | S n' => fun v => let (v', v'') := Vector_split n' m (Vector.tl v) in
                     (Vector.cons _ (Vector.hd v) _ v', v'')
  end v.

Fixpoint VectorByteToWord {numBytes} (v : t char numBytes) : word (8 * numBytes) :=
  match numBytes return
        t char numBytes
        -> word (8 * numBytes) with
  | 0 => fun _ => WO
  | S numBytes' => fun v => eq_rect _ word (Core.append_word (VectorByteToWord (Vector.tl v)) (Vector.hd v))
                                    (8 * S numBytes')  (sym_eq (NPeano.Nat.mul_succ_r _ _))
  end v.

Lemma SW_word_eq_rect_eq
  : forall (m n: nat)
           (b : bool)
           (a : word m) H H',
    SW_word b (eq_rect m word a n H) =
    eq_rect (S m) word (SW_word b a) (S n) H'.
Proof.
  destruct H; simpl; intros.
  apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
Qed.

Lemma Some_eq_rect_eq
  : forall n m w H b,
    eq_rect n (fun n : nat => option (word n * ByteString)) (Some  (w, b)) m H
    = Some (eq_rect n word w _ H, b).
Proof.
  destruct H; simpl; reflexivity.
Qed.

Lemma None_eq_rect_eq
  : forall n m H,
    eq_rect n (fun n : nat => option (word n * ByteString)) (None) m H
    = None.
Proof.
  destruct H; simpl; reflexivity.
Qed.

Require Import Fiat.Common.Equality.

Lemma WS_eq_rect_eq
  : forall n m b (w : word n) H H',
    WS b (eq_rect n word w m H)
    = eq_rect (S n) word (WS b w) (S m) H'.
Proof.
  destruct H; simpl; intros.
  apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
Qed.

Lemma eq_rect_decode_word
  : forall n m H b,
    eq_rect n (fun n0 : nat => option (word n0 * ByteString)) (decode_word' n b) m H =
    decode_word' m b.
Proof.
  induction n; simpl; intros; subst; simpl.
  - reflexivity.
  - reflexivity.
Qed.

Lemma decode_word_plus : forall n m (v : ByteString),
    WordOpt.decode_word' (n + m) v =
    (`(w, v') <- WordOpt.decode_word' (m + n) v;
      Some (eq_rect _ word w _ (Plus.plus_comm _ _), v')).
Proof.
  induction n; simpl; intros.
  - revert v; induction m; simpl; intros.
    + repeat f_equal; apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
    + destruct (ByteString_dequeue v) as [ [? ?] | ]; simpl; eauto.
      rewrite IHm, !DecodeBindOpt_assoc; apply DecodeBindOpt_under_bind; intros.
      simpl; eauto.
      repeat f_equal; clear.
      eapply SW_word_eq_rect_eq.
  - etransitivity.
    apply DecodeBindOpt_under_bind; intros.
    set_evars; rewrite IHn, !DecodeBindOpt_assoc.
    unfold H; reflexivity.
    simpl; replace (WordOpt.decode_word' (m + S n) v) with
      (`(w', v') <- WordOpt.decode_word' (S (m + n)) v; Some (eq_rect _ word w' _ (plus_n_Sm _ _), v')).
    + simpl; repeat (rewrite !DecodeBindOpt_assoc; apply DecodeBindOpt_under_bind; intros).
      simpl; repeat f_equal;  erewrite SW_word_eq_rect_eq; rewrite <- transport_pp; f_equal.
    + simpl; rewrite !DecodeBindOpt_assoc.
      etransitivity.
      apply DecodeBindOpt_under_bind; intros.
      set_evars; rewrite !DecodeBindOpt_assoc; simpl.
      unfold H; reflexivity.
      simpl.
      pose proof (IHn (S m) v); simpl in H.
      rewrite !DecodeBindOpt_assoc in H; simpl.
      destruct (ByteString_dequeue v) as [ [? ?] | ]; simpl in *.
      setoid_rewrite DecodeBindOpt_assoc in H; simpl.
      destruct (decode_word' (m + n) b0) as [ [? ?] | ]; simpl in *.
      assert (n + S m = m + S n) by omega.
      assert (eq_rect _ (fun n => option (word n * ByteString)) (decode_word' (n + S m) v) (m + S n) H0
              = eq_rect _ (fun n => option (word n * ByteString))
                        (Some (eq_rect (S (m + n)) word (SW_word b w) (n + S m) (plus_comm (S m) n), b1))
                        (m + S n) H0)
             by (intros; rewrite H; reflexivity).
      rewrite Some_eq_rect_eq in H1.
      rewrite <- transport_pp in H1.
      erewrite Eqdep_dec.eq_proofs_unicity with (p1 := (plus_n_Sm m n));
        intros; try omega.
      match goal with
        H: _ = ?a' |- ?a = _ => replace a with a' by reflexivity
      end.
      assert (n + S m = m + S n) by omega.
      rewrite <- eq_rect_decode_word with (H := H0), H; simpl.
      destruct H0; reflexivity.
      assert (n + S m = m + S n) by omega.
      rewrite <- eq_rect_decode_word with (H := H0), H; simpl.
      destruct H0; reflexivity.
      assert (n + S m = m + S n) by omega.
      rewrite <- eq_rect_decode_word with (H := H0), H; simpl.
      destruct H0; reflexivity.
Qed.

Lemma aligned_decode_char_eq'
          {numBytes numBytes'}
  : forall (v : Vector.t char (S numBytes' + numBytes)),
    WordOpt.decode_word' (transformerUnit := ByteString_QueueTransformerOpt) (8 * (S numBytes')) (build_aligned_ByteString v)
    = let (v', v'') := Vector_split (S numBytes') numBytes v in
      Some (VectorByteToWord v', build_aligned_ByteString v'').
Proof.
  induction numBytes'.
  - intros; rewrite aligned_decode_char_eq.
    unfold Vector_split; simpl.
    repeat f_equal; generalize (Vector.hd v); intro; unfold char in c; shatter_word c.
    fold Nat.add.
    apply Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
  - revert IHnumBytes'; generalize (S numBytes'); intros.
    match goal with
      |- ?k = _ =>
      replace k
      with (`(w, v') <-  Some (Vector.hd v, build_aligned_ByteString (Vector.tl v));
            `(w', v'') <- WordOpt.decode_word' (8 * n) v';
            Some (eq_rect _ word (Core.append_word w' w) _ (sym_eq (NPeano.Nat.mul_succ_r _ _)), v''))
    end.
    simpl.
    rewrite IHnumBytes'; simpl.
    destruct (Vector_split n numBytes (Vector.tl v)); simpl; repeat f_equal; clear.
    unfold DecodeBindOpt at 1; unfold BindOpt, If_Opt_Then_Else.
    assert (8 + 8 * n = 8 * S n) by omega.
    rewrite <- eq_rect_decode_word with (H := H).
    assert (8 * n + 8 = 8 + 8 * n) by omega.
    match goal with
      |- context [decode_word' ?m (build_aligned_ByteString ?b) ] =>
      replace (decode_word' m (build_aligned_ByteString b))
      with (`(w, v') <- Some (hd b, build_aligned_ByteString (tl b));
            `(w', v'') <- decode_word' (8 * n) v';
            Some (eq_rect _ word (append_word w' w) _ H0, v''))
    end.
    unfold DecodeBindOpt at 2; unfold BindOpt, If_Opt_Then_Else.
    destruct (decode_word' (8 * n) (build_aligned_ByteString (tl v))) as [ [? ?] | ]; try reflexivity.
    unfold DecodeBindOpt, If_Opt_Then_Else, BindOpt; simpl.
    rewrite Some_eq_rect_eq.
    rewrite <- transport_pp.
    repeat f_equal.
    apply Eqdep_dec.eq_proofs_unicity; try intros; omega.
    simpl; symmetry; apply None_eq_rect_eq.
    rewrite <- aligned_decode_char_eq.
    simpl.
    repeat (rewrite !DecodeBindOpt_assoc; simpl; apply DecodeBindOpt_under_bind; intros).
    clear.
    repeat f_equal.
    simpl in H0.
    revert a7 H0; generalize (n + (n + (n + (n + (n + (n + (n + (n + 0)))))))); clear; intros n0 w.
    induction w; simpl; intros.
    symmetry.
    apply Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
    erewrite <- IHw; clear.
    erewrite WS_eq_rect_eq; reflexivity.
    Grab Existential Variables.
    omega.
Qed.

Definition LetIn {A B} (a : A) (k : A -> B) : B := let a' := a in k a'.

Notation "'Let' a ':=' b 'in' k" := (LetIn b (fun a => k))
                                    (at level 81, right associativity,
                                     format "'[v' 'Let'  a  ':='  b  'in' '/' k ']'").

Lemma VectorByteToWord_cons :
  forall n v h H,
    VectorByteToWord (Vector.cons char h n v)
    = eq_rect _ _ (Core.append_word (VectorByteToWord v) h) _ H.
Proof.
  induction v; simpl; intros.
  rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
  repeat f_equal; apply Eqdep_dec.eq_proofs_unicity; intros; omega.
Qed.

Lemma Vector_nth_tl {A} : forall n (v : Vector.t A (S n)) p,
    Vector.nth v (Fin.FS p) = Vector.nth (Vector.tl v) p.
Proof.
  intros ? ?; pattern n, v; apply Vector.rectS; simpl; intros.
  inversion p.
  reflexivity.
Qed.

Lemma Vector_nth_hd {A} : forall n (v : Vector.t A (S n)),
    Vector.nth v Fin.F1 = Vector.hd v.
Proof.
  intros ? ?; pattern n, v; apply Vector.rectS; simpl; reflexivity.
Qed.

Fixpoint decode_list'
         {A : Type}
         {cache : Cache}
         (n : nat)
         (A_decode: nat -> CacheDecode -> (A * CacheDecode))
         (cd : CacheDecode) {struct n}
  : (list A * CacheDecode) :=
  match n return (nat -> CacheDecode -> (A * CacheDecode))
                 -> _
  with
  | 0 => fun _ => ([ ], cd)
  | S n' => fun A_decode' => Let a := A_decode' 0 cd in
        Let a' := decode_list' n' (fun p => A_decode' (S p)) (snd a) in
                                            (fst a :: (fst a'), snd a')
  end A_decode.
