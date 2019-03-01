Require Import
        Bedrock.Word
        Coq.omega.Omega
        Coq.NArith.NArith
        Coq.Arith.Arith
        Coq.Numbers.Natural.Peano.NPeano
        Coq.Logic.Eqdep_dec
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.BinLib.Core.

Require Export
        Fiat.Narcissus.Formats.ByteBuffer.

Hint Unfold
     ByteBuffer.t
     ByteBuffer.nil ByteBuffer.cons
     ByteBuffer.hd ByteBuffer.tl
     ByteBuffer.of_list ByteBuffer.to_list
     ByteBuffer.append ByteBuffer.fold_left : ByteBuffer.

Record ByteString :=
  { padding : nat;
    front : word padding;
    paddingOK : (padding < 8)%nat;
    numBytes : nat;
    byteString : ByteBuffer.t numBytes (* The bytestring. *)
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
               byteString := ByteBuffer.append (byteString bs)
                                              (ByteBuffer.cons ((WS b _)) (ByteBuffer.nil)) |}
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
         (l : ByteBuffer.t (S numBytes))
  : bool * (ByteBuffer.t numBytes) * word 7 :=
  let (b, w') := word_dequeue (ByteBuffer.hd l) in
  match numBytes return
        ByteBuffer.t (S numBytes) -> _ with
  | S numBytes' =>
    fun l =>
      match CharList_dequeue (ByteBuffer.tl l) with
      | (b', l'', tail) =>
        (b, ByteBuffer.cons (WS b' w') l'', tail)
      end
  | 0 => fun _ => (b, ByteBuffer.nil, w')
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
                  ByteBuffer.t nb
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
                    ByteBuffer.t nb
                    -> _ with
              | S n' =>
                fun l =>
                  match CharList_dequeue l with
                  | (b', l'', tail) =>
                    let (b, w') := word_dequeue front' in
                    Some (b', {| front := w';
                                 byteString := ByteBuffer.append l''
                                                             (ByteBuffer.cons (WS b tail) (ByteBuffer.nil))
                              |})
                  end
              | _ => fun _ =>
                       let (b, w') := word_dequeue front' in
                       Some (b, {| front := w';
                                   byteString := ByteBuffer.nil |})
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
  let bs'' := ByteBuffer.fold_left ByteString_enqueue_char bs (byteString bs') in
  ByteString_enqueue_word (front bs') bs''.

Definition ByteString_id : ByteString.
  refine {| front := WO; byteString := ByteBuffer.nil |}.
  abstract omega.
Defined.

Definition BoundedByteStringToByteString
           (bs : ByteString)
  : Core.ByteString :=
  {| Core.padding := padding bs;
     Core.front := front bs;
     Core.paddingOK := paddingOK bs;
     Core.byteString := ByteBuffer.to_list (byteString bs)
  |}.

Definition ByteStringToBoundedByteString
           (bs : Core.ByteString)
  : ByteString :=
  {| padding := Core.padding bs;
     front := Core.front bs;
     paddingOK := Core.paddingOK bs;
     byteString := ByteBuffer.of_list (Core.byteString bs)
  |}.

Lemma BoundedByteStringToByteString_ByteStringToBoundedByteString_eq :
  forall bs, BoundedByteStringToByteString (ByteStringToBoundedByteString bs) = bs.
Proof.
  unfold BoundedByteStringToByteString, ByteStringToBoundedByteString; destruct bs; simpl;
    f_equal.
  apply ByteBuffer.to_list_of_list_eq.
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

Lemma ByteStringToBoundedByteString_BoundedByteStringToByteString_eq :
  forall bs, ByteStringToBoundedByteString (BoundedByteStringToByteString bs) = bs.
Proof.
  unfold BoundedByteStringToByteString, ByteStringToBoundedByteString; destruct bs; simpl;
    eapply ByteString_f_equal; simpl.
  apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
  instantiate (1 := ByteBuffer.to_list_length _ byteString0).
  apply ByteBuffer.of_list_to_list.
  Grab Existential Variables.
  reflexivity.
Qed.

Lemma byteString_f_equal
  : forall bs bs'
           (padding_eq : padding bs' = padding bs)
           (numBytes_eq : numBytes bs' = numBytes bs),
    front bs = (@eq_rect nat (padding bs') (fun t => word t) (front bs') _ padding_eq)
    -> byteString bs = @eq_rect nat (numBytes bs') (ByteBuffer.t) (byteString bs') _ numBytes_eq
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
        autounfold with ByteBuffer in *.
        simpl. rewrite (IHbyteString0 H); clear.
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

Instance ByteStringQueueMonoid : Monoid ByteString.
Proof.
  refine {| mappend := ByteString_enqueue_ByteString;
            bin_measure := length_ByteString;
            mempty := ByteString_id |}.
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
      * autounfold with ByteBuffer in *; unfold Vector.to_list in *.
        simpl; f_equal.
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
           (l : BitString)
  : ByteString :=
  fold_left (fun bs b => ByteString_enqueue b bs) l ByteString_id.

Fixpoint wordToQueue {n}
         (w : word n)
  : BitString :=
  match n return word n -> BitString with
  | 0 => fun _ => [ ]
  | S n' => fun w => wordToQueue (wtl w) ++ [whd w]
  end w.

Fixpoint ByteString_into_queue' {sz}
         (chars : ByteBuffer.t sz)
         {struct chars} : BitString :=
  match chars return BitString with
  | Vector.nil => [ ]
  | Vector.cons char' _ chars' =>
    app (wordToQueue char')
        (ByteString_into_queue' chars')
  end.

Definition ByteString_into_queue
           (bs : ByteString)
  : BitString :=
  app (ByteString_into_queue' (byteString bs)) (wordToQueue (front bs)).

Definition build_aligned_ByteString
           {numBytes}
           (v : ByteBuffer.t numBytes)
  : ByteString.
  refine {| front := WO;
            byteString := v |}.
  abstract omega.
Defined.

Lemma build_aligned_ByteString_append
      {numBytes'}
  : forall (v' : ByteBuffer.t numBytes') {numBytes} (v : ByteBuffer.t numBytes),
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
  rewrite app_length, <- !ByteBuffer.to_list_length; reflexivity.
  eapply byteString_f_equal with (numBytes_eq := H); simpl.
  apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
  induction v; simpl in *.
  induction v'.
  - apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
  - simpl in H; injection H; intros.
    autounfold with ByteBuffer in *.
    simpl; rewrite eq_rect_Vector_cons with (H' := H0); simpl.
    f_equal.
    eapply IHv'.
  -  simpl in H; injection H; intros.
     autounfold with ByteBuffer in *.
     simpl; rewrite eq_rect_Vector_cons with (H' := H0); simpl.
     f_equal.
     eapply IHv.
     Grab Existential Variables.
     reflexivity.
     omega.
Qed.

Lemma build_aligned_ByteString_cons
      {numBytes}
  : forall (v : ByteBuffer.t (S numBytes)),
    (build_aligned_ByteString v) = ByteString_enqueue_ByteString (build_aligned_ByteString (Vector.cons _ (Vector.hd v) _ (ByteBuffer.nil))) (build_aligned_ByteString (Vector.tl v)).
Proof.
  intros; rewrite <- (build_aligned_ByteString_append (Vector.tl v)
                                                      (Vector.cons _ (Vector.hd v) _ (ByteBuffer.nil))).
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
    pose proof (build_aligned_ByteString_append byteString0 (ByteBuffer.nil)).
    unfold ByteString_enqueue_ByteString in H; simpl in H.
    unfold build_aligned_ByteString in H; simpl in H.
    replace paddingOK0 with (build_aligned_ByteString_subproof)
      by apply le_uniqueness_proof; rewrite H.
    simpl.
    rewrite fold_left_rev_right.
    replace {|
        padding := 0;
        front := WO;
        paddingOK := build_aligned_ByteString_subproof;
        numBytes := 0;
        byteString := ByteBuffer.nil |} with ByteString_id
      by (eapply byteString_f_equal; simpl;
          instantiate (1 := eq_refl); reflexivity).
    generalize ByteString_id; clear.
    induction byteString0.
    + simpl. reflexivity.
    + autounfold with ByteBuffer in *.
      intros; simpl Vector.fold_left.
      first [ rewrite IHbyteString0
            | unfold Vector.fold_left;
              rewrite IHbyteString0].
      (* This arcane sequence is to prevent slowdown in 8.4. *)
      unfold ByteString_enqueue_char.
      unfold char in h.
      unfold ByteString_into_queue' at 2.
      fold (ByteString_into_queue' byteString0).
      rewrite fold_left_app.
      unfold wordToQueue.
      simpl app.
      rewrite <- !fold_left_cons.
      unfold fold_left at 3.
      unfold ByteString_enqueue_word; reflexivity.
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
(* 8.4 hangs forever on Qed :p *)

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
  rewrite <- IHbyteString0; reflexivity.
Qed.

Fixpoint split_Vector_bool
         (l : BitString)
  : {n : nat & ByteBuffer.t n} * {n : nat & word n} :=
  match l return {n : nat & ByteBuffer.t n} * {n : nat & word n} with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: l' =>
    let (l'', back) := split_Vector_bool l' in
    (existT _ _ (Vector.cons _ (WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))) _ (projT2 l'')), back)
  | [b0; b1; b2; b3; b4; b5; b6] =>
    (existT _ _ (ByteBuffer.nil), existT _ _ (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))))
  | [b0; b1; b2; b3; b4; b5] =>
    (existT _ _ (ByteBuffer.nil), existT _ _ (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))
  | [b0; b1; b2; b3; b4] =>
    (existT _ _ (ByteBuffer.nil), existT _ _ (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))
  | [b0; b1; b2; b3] =>
    (existT _ _ (ByteBuffer.nil), existT _ _ (WS b3 (WS b2 (WS b1 (WS b0 WO)))))
  | [b0; b1; b2] =>
    (existT _ _ (ByteBuffer.nil), existT _ _ (WS b2 (WS b1 (WS b0 WO))))
  | [b0; b1] =>
    (existT _ _ (ByteBuffer.nil), existT _ _ (WS b1 (WS b0 WO)))
  | [b0] =>
    (existT _ _ (ByteBuffer.nil), existT _ _  (WS b0 WO))
  | _ => (existT _ _ (ByteBuffer.nil), existT _ _ WO)
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
                                            (Vector.cons _ (WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))) _ (ByteBuffer.nil)) |}.
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
                                  Vector.append byteString0 (Vector.cons _ (WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO)))))))) _ (ByteBuffer.nil)) |}).
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
      *  autounfold with ByteBuffer in *; erewrite eq_rect_Vector_cons; f_equal.
        instantiate (1 := eq_refl); reflexivity.
      * unfold ByteBuffer.t in *; erewrite eq_rect_Vector_cons; f_equal.
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

Lemma ByteString_enqueue_into_BitString
  : forall b (l : BitString),
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
  - rewrite ByteString_enqueue_into_BitString.
    rewrite <- IHl', <- app_assoc; reflexivity.
Qed.

Lemma Vector_fold_left_app
  : forall (A B : Type) (f : A -> B -> A) sz (l : Vector.t B sz) sz' (l' : Vector.t B sz') (i : A),
    Vector.fold_left f i (Vector.append l l') = Vector.fold_left f (Vector.fold_left f i l) l'.
Proof.
  induction l; simpl; eauto.
Qed.

Lemma ByteString_enqueue_ByteString_enqueue
  : forall (l' l : BitString)
           (b : bool),
    ByteString_enqueue_ByteString (queue_into_ByteString l) (ByteString_enqueue b (queue_into_ByteString l')) =
    ByteString_enqueue b (ByteString_enqueue_ByteString (queue_into_ByteString l) (queue_into_ByteString l')).
Proof.
  intro; destruct (queue_into_ByteString l').
  unfold ByteString_enqueue at 1; simpl.
  destruct (eq_nat_dec padding0 7); simpl.
  - unfold ByteString_enqueue_ByteString; simpl; subst.
    intros; unfold ByteBuffer.fold_left, ByteBuffer.append.
    rewrite Vector_fold_left_app;
      shatter_word front0;
      unfold ByteString_enqueue_char; simpl.
    reflexivity.
  - reflexivity.
Qed.

Lemma ByteString_enqueue_ByteString_into_BitString
  : forall (l' l : BitString),
    ByteString_enqueue_ByteString (queue_into_ByteString l) (queue_into_ByteString l')
    = queue_into_ByteString (l ++ l').
Proof.
  intro; generalize (le_refl (length l')); remember (length l').
  setoid_rewrite Heqn at 1; clear Heqn; revert l';
    induction n.
  - intros; destruct l'; simpl; intros.
    + rewrite ByteStringQueueMonoid_subproof1,
      app_nil_r; reflexivity.
    + inversion H.
  - intros; rewrite queue_into_ByteString_app.
    rewrite <- (rev_involutive l') in *.
    clear IHn H.
    induction (rev l'); simpl.
    + rewrite ByteStringQueueMonoid_subproof1; reflexivity.
    + rewrite <- ByteString_enqueue_into_BitString.
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
    pose proof (IHl' _ (Vector.append l (Vector.cons _ h _ (ByteBuffer.nil)))) as e; simpl in e.
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
      unfold ByteBuffer.t; erewrite eq_rect_Vector_cons; f_equal.
      instantiate (1 := eq_refl); reflexivity.
      unfold ByteBuffer.t; erewrite eq_rect_Vector_cons; f_equal.
      erewrite IHl; f_equal.
    * autounfold with ByteBuffer in *.
      simpl in *.
      match goal with
        |- ?l'' = _ => replace l'' with
          (ByteString_enqueue_word w1
         (Vector.fold_left ByteString_enqueue_char
            {|
            padding := 0;
            front := WO;
            paddingOK := paddingOK''';
            numBytes := sz + 1;
            byteString := Vector.append l
                            (Vector.cons (word 8) (WS x (WS x0 (WS x1 (WS x2 (WS x3 (WS x4 (WS x5 (WS x6 WO)))))))) 0
                                         (Vector.nil char)) |} l'))
      end.
      f_equal; f_equal.
      eapply byteString_f_equal; simpl;
        try (instantiate (1 := eq_refl); reflexivity).
      rewrite <- H'; reflexivity.
      Grab Existential Variables.
      omega.
Qed.

Lemma ByteString_dequeue_into_BitString
  : forall (l : BitString),
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
                                                _ (ByteBuffer.nil)))
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
        rewrite <- ByteString_enqueue_ByteString_into_BitString.
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
        rewrite <- ByteString_enqueue_ByteString_into_BitString.
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
        rewrite <- ByteString_enqueue_ByteString_into_BitString.
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
  rewrite ByteString_dequeue_into_BitString.
  rewrite Core.ByteString_dequeue_into_BitString.
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
  rewrite Core.ByteString_dequeue_into_BitString.
  rewrite (ByteString_into_queue_eq b').
  rewrite ByteString_dequeue_into_BitString.
  rewrite <- ByteString_into_queue_eq.
  rewrite <- ByteStringToBoundedByteString_into_queue_eq'.
  rewrite ByteStringToBoundedByteString_BoundedByteStringToByteString_eq.
  destruct (ByteString_into_queue b'); simpl;
    rewrite  ?BoundedByteStringToByteString_into_queue_eq; reflexivity.
Qed.

Lemma AlignedByteString_dequeue_opt
  : forall (t : bool) (b b' b'' : ByteString),
    ByteString_dequeue b = Some (t, b')
    -> ByteString_dequeue (mappend b b'') = Some (t, mappend b' b'').
Proof.
  simpl; intros; rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b),
                 <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b') in *;
  rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b'').
  rewrite ByteString_dequeue_ByteStringToBoundedByteString_eq in H;
    destruct (Core.ByteString_dequeue (BoundedByteStringToByteString b)) eqn : ?; simpl in *;
    try discriminate; destruct p; simpl in *.
  injection H; intros; subst.
  apply ByteString_dequeue_mappend_opt with (b'' := BoundedByteStringToByteString b'') in Heqo;
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

Instance ByteString_QueueMonoidOpt
  : QueueMonoidOpt ByteStringQueueMonoid bool.
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
                    | rewrite <- Heqo; rewrite <- length_ByteBuffer_to_list, <- length_ByteString_ByteStringToBoundedByteString_eq,
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


Require Import Fiat.Narcissus.Formats.WordOpt.

Lemma aligned_decode_char_eq
      {numBytes}
  : forall (v : ByteBuffer.t (S numBytes)),
    WordOpt.decode_word' (monoidUnit := ByteString_QueueMonoidOpt) 8 (build_aligned_ByteString v)
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
  pose proof (@dequeue_mappend_opt _ _ _ ByteString_QueueMonoidOpt).
  rewrite build_aligned_ByteString_cons; simpl.
  simpl in H7.
  erewrite H7 with (t := x6)
                   (b' := {| front := WS x (WS x0 (WS x1 (WS x2 (WS x3 (WS x4 (WS x5 WO))))));
                             byteString := ByteBuffer.nil |}); simpl.
  erewrite H7 with (t := x5)
                   (b' := {| front := WS x (WS x0 (WS x1 (WS x2 (WS x3 (WS x4 WO)))));
                             byteString := ByteBuffer.nil |}); simpl.
  erewrite H7 with (t := x4)
                   (b' := {| front := WS x (WS x0 (WS x1 (WS x2 (WS x3 WO))));
                             byteString := ByteBuffer.nil |}); simpl.
  erewrite H7 with (t := x3)
                   (b' := {| front := WS x (WS x0 (WS x1 (WS x2 WO)));
                             byteString := ByteBuffer.nil |}); simpl.
  erewrite H7 with (t := x2)
                   (b' := {| front := WS x (WS x0 (WS x1 WO));
                             byteString := ByteBuffer.nil |}); simpl.
  erewrite H7 with (t := x1)
                   (b' := {| front := WS x (WS x0 WO);
                             byteString := ByteBuffer.nil |}); simpl.
  erewrite H7 with (t := x0)
                   (b' := {| front := WS x WO;
                             byteString := ByteBuffer.nil |}); simpl.
  erewrite H7 with (t := x)
                   (b' := {| front := WO;
                             byteString := ByteBuffer.nil |}); simpl.
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
  apply (@mempty_left _ ByteStringQueueMonoid).
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
  : forall (v : ByteBuffer.t (S numBytes' + numBytes)),
    WordOpt.decode_word' (monoidUnit := ByteString_QueueMonoidOpt) (8 * (S numBytes')) (build_aligned_ByteString v)
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

Lemma Vector_split_append {A} {m n}
  : forall (v : Vector.t A (m + n)),
    v = Vector.append (fst (Vector_split _ _ v)) (snd (Vector_split _ _ v)).
Proof.
  induction m; simpl; eauto.
  intros.
  generalize (IHm (Vector.tl v)); clear.
  fold plus; destruct (Vector_split m n (Vector.tl v)); simpl; intros.
  rewrite <- H.
  generalize v; clear; generalize (m + n).
  intros; pattern n0, v; apply Vector.caseS; simpl; intros.
  reflexivity.
Qed.

Lemma queue_into_ByteString_inj
  : forall l1 l2,
    queue_into_ByteString l1 = queue_into_ByteString l2
    -> l1 = l2.
Proof.
  intros.
  apply queue_into_ByteString_inj.
  rewrite !BoundedByteStringToByteString_into_queue_eq.
  rewrite H; reflexivity.
Qed.

Lemma app_inj {A}
  : forall l1 l2 l1' l2' : list A,
    List.length l2 = List.length l2'
    -> app l1 l2 = app l1' l2'
    -> l1 = l1'.
Proof.
  induction l1; simpl; intros.
  - destruct l1'; simpl; eauto.
    rewrite H0 in H; simpl in H.
    rewrite app_length in H; omega.
  - destruct l1'; simpl in *; intros.
    rewrite <- H0 in H; simpl in H; rewrite app_length in H; omega.
    injections.
    erewrite IHl1; eauto.
Qed.

Lemma app_inj' {A}
  : forall l1 l2 l1' l2' : list A,
    List.length l1 = List.length l1'
    -> app l1 l2 = app l1' l2'
    -> l2 = l2'.
Proof.
  induction l1; simpl; intros.
  - destruct l1'; simpl; eauto.
    simpl in H; discriminate.
  - destruct l1'; simpl in *; intros.
    discriminate.
    injections; eauto.
Qed.

Lemma length_ByteString_into_queue
  : forall bs bs',
    length_ByteString bs = length_ByteString bs'
    -> List.length (ByteString_into_queue bs) = List.length (ByteString_into_queue bs').
Proof.
  intros ? ?.
  rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq bs).
  rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq bs').
  rewrite !ByteStringToBoundedByteString_into_queue_eq'.
  unfold Core.ByteString_into_queue; rewrite !app_length, !length_ByteString_into_queue'.
  rewrite !length_ByteString_ByteStringToBoundedByteString_eq.
  unfold Core.length_ByteString.
  rewrite !length_wordToQueue.
  omega.
Qed.

Lemma ByteString_enqueue_ByteString_inj
  : forall bs1 bs2 bs1' bs2',
    ByteString_enqueue_ByteString bs1 bs2 =
    ByteString_enqueue_ByteString bs1' bs2'
    -> length_ByteString bs2 = length_ByteString bs2'
    -> bs1 = bs1'.
Proof.
  intros.
  rewrite (ByteString_into_queue_eq bs1),
  (ByteString_into_queue_eq bs2),
  (ByteString_into_queue_eq bs1'),
  (ByteString_into_queue_eq bs2') in H.
  rewrite !ByteString_enqueue_ByteString_into_BitString in H.
  apply queue_into_ByteString_inj in H.
  rewrite (ByteString_into_queue_eq bs1),
  (ByteString_into_queue_eq bs1').
  apply app_inj in H; eauto using length_ByteString_into_queue.
  rewrite H; eauto.
Qed.

Lemma ByteString_enqueue_ByteString_inj'
  : forall bs1 bs2 bs1' bs2',
    ByteString_enqueue_ByteString bs1 bs2 =
    ByteString_enqueue_ByteString bs1' bs2'
    -> length_ByteString bs1 = length_ByteString bs1'
    -> bs2 = bs2'.
Proof.
  intros.
  rewrite (ByteString_into_queue_eq bs1),
  (ByteString_into_queue_eq bs2),
  (ByteString_into_queue_eq bs1'),
  (ByteString_into_queue_eq bs2') in H.
  rewrite !ByteString_enqueue_ByteString_into_BitString in H.
  apply queue_into_ByteString_inj in H.
  rewrite (ByteString_into_queue_eq bs2),
  (ByteString_into_queue_eq bs2').
  apply app_inj' in H; eauto using length_ByteString_into_queue.
  rewrite H; eauto.
Qed.

Lemma build_aligned_ByteString_split :
  forall {n} (v : Vector.t _ n) {m} (v' : Vector.t _ m)  b,
    build_aligned_ByteString v = ByteString_enqueue_ByteString b (build_aligned_ByteString v')
    -> exists v'' : Vector.t _ (n - m),
      b = build_aligned_ByteString v''.
Proof.
  intros.
  assert (n = (n - m) + m).
  { rewrite plus_comm. eapply le_plus_minus.
    generalize (f_equal length_ByteString H); intros.
    unfold length_ByteString at 1 in H0; simpl in H0.
    replace (length_ByteString (ByteString_enqueue_ByteString b (build_aligned_ByteString v')))
      with (length_ByteString b + (8 * m)) in H0.
    omega.
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b).
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq (build_aligned_ByteString _)).
    rewrite ByteString_enqueue_ByteString_ByteStringToBoundedByteString.
    rewrite !length_ByteString_ByteStringToBoundedByteString_eq.
    rewrite ByteString_enqueue_ByteString_measure.
    unfold BoundedByteStringToByteString at 3.
    simpl.
    unfold Core.length_ByteString at 3; simpl.
    rewrite <- !ByteBuffer.to_list_length; omega.
  }
  revert v H; rewrite H0; intros; rewrite <- H0.
  rewrite (Vector_split_append v) in H.
  rewrite build_aligned_ByteString_append in H.
  eexists (fst (Vector_split (n - m) m v)).
  eapply ByteString_enqueue_ByteString_inj in H; eauto.
Qed.

Lemma build_aligned_ByteString_split' :
  forall {n} (v : Vector.t _ n) {m} (v' : Vector.t _ m)  b,
    build_aligned_ByteString v = ByteString_enqueue_ByteString (build_aligned_ByteString v') b
    -> exists v'' : Vector.t _ (n - m),
      b = build_aligned_ByteString v''.
Proof.
  intros.
  assert (n = m + (n - m)).
  { eapply le_plus_minus.
    generalize (f_equal length_ByteString H); intros.
    unfold length_ByteString at 1 in H0; simpl in H0.
    replace (length_ByteString (ByteString_enqueue_ByteString (build_aligned_ByteString v') b))
      with (length_ByteString b + (8 * m)) in H0.
    omega.
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b).
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq (build_aligned_ByteString _)).
    rewrite ByteString_enqueue_ByteString_ByteStringToBoundedByteString.
    rewrite !length_ByteString_ByteStringToBoundedByteString_eq.
    rewrite ByteString_enqueue_ByteString_measure.
    unfold BoundedByteStringToByteString at 2.
    simpl.
    unfold Core.length_ByteString at 2; simpl.
    rewrite <- !ByteBuffer.to_list_length.
    omega.
  }
  revert v H; rewrite H0; intros; rewrite <- H0.
  rewrite (Vector_split_append v) in H.
  rewrite build_aligned_ByteString_append in H.
  eexists (snd (Vector_split m (n - m) v)).
  eapply ByteString_enqueue_ByteString_inj' in H; eauto.
Qed.

Lemma build_aligned_ByteString_inj {n}:
  forall (v1 v2 : Vector.t _ n),
    build_aligned_ByteString v1 = build_aligned_ByteString v2
    -> v1 = v2.
Proof.
  unfold build_aligned_ByteString; intros.
  injection H.
  intro.
  rewrite <- (EqdepFacts.eq_sigT_snd H0); clear.
  generalize (EqdepFacts.eq_sigT_fst H0); clear H0; intros.
  replace e with (eq_refl n); try reflexivity.
  eapply UIP_dec; decide equality.
Qed.

Lemma length_ByteString_queue_into_ByteString'
  : forall (l : BitString) (bs : ByteString),
    length_ByteString (List.fold_left (fun bs' b => ByteString_enqueue b bs') l bs) =
    Datatypes.length l + length_ByteString bs.
Proof.
  induction l; simpl; intros; eauto.
  rewrite IHl; simpl.
  pose proof (@measure_enqueue ByteString _ _ _ a bs) as H;
    simpl in H; rewrite H; simpl; omega.
Qed.

Corollary length_ByteString_queue_into_ByteString
  : forall l,
    length_ByteString (queue_into_ByteString l) = List.length l.
Proof.
  unfold queue_into_ByteString in *; intros; rewrite length_ByteString_queue_into_ByteString'.
  unfold length_ByteString; simpl; omega.
Qed.

Lemma length_ByteString_enqueue_ByteString
  : forall bs1 bs2,
    length_ByteString (ByteString_enqueue_ByteString bs1 bs2) =
    length_ByteString bs1 + length_ByteString bs2.
Proof.
  intros; rewrite (ByteString_into_queue_eq bs1), (ByteString_into_queue_eq bs2).
  rewrite ByteString_enqueue_ByteString_into_BitString.
  rewrite !length_ByteString_queue_into_ByteString,
  app_length; reflexivity.
Qed.

Lemma ByteString_enqueue_ByteString_assoc
  : forall bs1 bs2 bs3,
    ByteString_enqueue_ByteString bs1 (ByteString_enqueue_ByteString bs2 bs3) =
    ByteString_enqueue_ByteString (ByteString_enqueue_ByteString bs1 bs2) bs3.
Proof.
  intros.
  rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq bs1),
  <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq bs2),
  <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq bs3).
  rewrite !ByteString_enqueue_ByteString_ByteStringToBoundedByteString.
  rewrite ByteString_enqueue_ByteString_assoc; reflexivity.
Qed.

Lemma padding_mod_8
  : forall bs,
    (padding bs) mod 8 = padding bs.
Proof.
  intros; pose proof (paddingOK bs).
  destruct (padding bs); simpl in *; try omega.
  do 8 (destruct n; simpl in *; try omega).
Qed.

Local Arguments modulo : simpl never.

Lemma padding_ByteString_queue_into_ByteString
  : forall l : BitString, padding (queue_into_ByteString l) = (List.length l) mod 8.
Proof.
  unfold queue_into_ByteString; intro.
  replace (List.length l mod 8) with ((List.length l mod 8 + (padding ByteString_id) mod 8) mod 8).
  generalize ByteString_id.
  induction l.
  - intros; simpl; rewrite !padding_mod_8; reflexivity.
  - intros.
    simpl; rewrite IHl.
    rewrite <- !Nat.add_mod by omega.
    destruct (le_lt_dec (padding b) 6).
    erewrite ByteString_enqueue_simpl; simpl.
    f_equal; omega.
    unfold ByteString_enqueue.
    pose proof (paddingOK b).
    destruct (eq_nat_dec (padding b) 7); try omega.
    simpl.
    rewrite e.
    replace (S (List.length l + 7)) with (List.length l + 8) by omega.
    rewrite Nat.add_mod with (b := 8) by omega.
    unfold modulo at 4; simpl.
    rewrite Nat.add_mod by omega; f_equal.
  - rewrite <- !Nat.add_mod by omega.
    simpl; f_equal; omega.
    Grab Existential Variables.
    omega.
Qed.

Lemma padding_ByteString_enqueue_ByteString
  : forall bs bs',
    padding (ByteString_enqueue_ByteString bs bs') =
    (padding bs + padding bs')%nat mod 8.
Proof.
  intros.
  rewrite (ByteString_into_queue_eq bs), (ByteString_into_queue_eq bs').
  rewrite ByteString_enqueue_ByteString_into_BitString.
  rewrite !padding_ByteString_queue_into_ByteString.
  rewrite app_length.
  rewrite Nat.add_mod by omega.
  reflexivity.
Qed.

Corollary padding_ByteString_enqueue_aligned_ByteString
  : forall bs bs',
    padding bs = 0
    -> padding (ByteString_enqueue_ByteString bs bs') = padding bs'.
Proof.
  intros; rewrite padding_ByteString_enqueue_ByteString.
  rewrite H, plus_O_n, padding_mod_8; reflexivity.
Qed.

Corollary numBytes_ByteString_enqueue_ByteString
  : forall bs bs',
    padding bs = 0
    -> numBytes (ByteString_enqueue_ByteString bs bs') =
       numBytes bs + numBytes bs'.
Proof.
  intros.
  pose proof (length_ByteString_enqueue_ByteString bs bs') as H';
    unfold length_ByteString in H'.
  rewrite padding_ByteString_enqueue_ByteString, H, !plus_O_n,
  padding_mod_8 in H'.
  omega.
Qed.

Lemma length_ByteString_no_padding
  : forall bs,
    padding bs = 0
    -> length_ByteString bs = 8* numBytes bs.
Proof.
  unfold length_ByteString; intros; rewrite H; omega.
Qed.

Lemma Vector_append_assoc {A}
  : forall m n o H (v1 : Vector.t A m) (v2 : Vector.t A n)
           (v3 : Vector.t A o),
    Vector.append v1 (Vector.append v2 v3) =
    eq_rect _ _ (Vector.append (Vector.append v1 v2) v3) _ H.
Proof.
  intros ? ? ? ?; induction v1; simpl; intros.
  - replace H with (eq_refl (n + o)); try reflexivity.
    eapply UIP_dec; intros; decide equality.
  - erewrite IHv1.
    erewrite eq_rect_Vector_cons.
    reflexivity.
    Grab Existential Variables.
    omega.
Qed.

Lemma Vector_append_assoc' {A}
  : forall m n o z H H' (v1 : Vector.t A m) (v2 : Vector.t A n)
           (v3 : Vector.t A o),
    Vector.append v1 (eq_rect _ _ (Vector.append v2 v3) z H) =
    eq_rect _ _ (Vector.append (Vector.append v1 v2) v3) _ H'.
Proof.
  induction v1; simpl; intros.
  - f_equal; eapply UIP_dec; intros; decide equality.
  - erewrite IHv1.
    erewrite eq_rect_Vector_cons.
    reflexivity.
    Grab Existential Variables.
    omega.
Qed.

Lemma Vector_append_assoc'' {A}
  : forall m n o z H H' (v1 : Vector.t A m) (v2 : Vector.t A n)
           (v3 : Vector.t A o),
    Vector.append (eq_rect _ _ (Vector.append v1 v2) z H) v3  =
    eq_rect _ _ (Vector.append (Vector.append v1 v2) v3) _ H'.
Proof.
  intros; subst; simpl.
  erewrite (UIP_dec _ _ (eq_refl _)); simpl.
  reflexivity.
  Grab Existential Variables.
  decide equality.
Qed.

Lemma Vector_append_split_fst:
  forall (A : Type) (m n : nat) (v1 : Vector.t A m) (v2 : Vector.t A n),
    v1 = fst (Vector_split m n (Vector.append v1 v2)).
Proof.
  induction v1; simpl; intros; eauto.
  rewrite (IHv1 v2) at 1.
  destruct (Vector_split n0 n (Vector.append v1 v2)); reflexivity.
Qed.

Lemma Vector_append_split_snd:
  forall (A : Type) (m n : nat) (v1 : Vector.t A m) (v2 : Vector.t A n),
    v2 = snd (Vector_split m n (Vector.append v1 v2)).
Proof.
  induction v1; simpl; intros; eauto.
  rewrite (IHv1 v2) at 1.
  destruct (Vector_split n0 n (Vector.append v1 v2)); reflexivity.
Qed.

Lemma Vector_split_lt {A} :
  forall m n
         (lt_m_n : (m <= n)%nat)
         (v : Vector.t A n),
  exists k
         (v1 : Vector.t A m)
         (v2 : Vector.t A k)
         (H : m + k = n),
    v = eq_rect _ (Vector.t A) (Vector.append v1 v2) _ H.
Proof.
  intros ? ? lt_m_n; induction lt_m_n; intros.
  - eexists 0, v, (Vector.nil _), _; apply Vector_append_nil_r.
  - revert IHlt_m_n; pattern m0, v; eapply Vector.caseS; intros.
    destruct (IHlt_m_n t) as [? [? [? [? ?] ] ] ]; subst; simpl; clear IHlt_m_n.
    eexists _, (fst (Vector_split _ _ (eq_rect _ _ (Vector.cons A h _ x0) _ (plus_comm 1 m)))),
    (Vector.append (snd (Vector_split _ _ (eq_rect _ _ (Vector.cons A h _ x0) _ (plus_comm 1 m)))) x1),
    (eq_sym (plus_n_Sm _ _)).
    erewrite Vector_append_assoc, <- Equality.transport_pp, <- Vector_split_append.
    pose proof (fun z H H' => Vector_append_assoc'' _ _ _ z H H'
                                                    (Vector.cons A h _ (Vector.nil _)) x0 x1).
    simpl in *.
    erewrite H.
    rewrite <- Equality.transport_pp.
    erewrite (UIP_dec _ _ (eq_refl _)); simpl.
    reflexivity.
    Grab Existential Variables.
    decide equality.
    omega.
    omega.
Qed.

Fixpoint initialize_Aligned_ByteString (n : nat) : ByteBuffer.t n :=
  match n with
  | 0 => ByteBuffer.nil
  | S n' => ByteBuffer.cons (wzero 8) (initialize_Aligned_ByteString n')
  end.

Lemma length_ByteString_id :
  length_ByteString ByteString_id = 0.
Proof.
  reflexivity.
Qed.

Global Instance ByteString_RichMonoidOpt
  : RichMonoidOpt ByteStringQueueMonoid :=
  {
  }.
Proof.
  abstract eauto using ByteString_enqueue_ByteString_inj.
Defined.