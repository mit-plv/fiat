Require Import
        Bedrock.Word
        Coq.NArith.NArith
        Coq.Arith.Arith
        Coq.Numbers.Natural.Peano.NPeano
        Coq.Logic.Eqdep_dec
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.BinLib.Core
        compcert.lib.Integers.

Import Byte.

Record ByteString :=
  { padding : nat;
    front : word padding;
    paddingOK : (padding < 8)%nat;
    numBytes : nat;
    byteString : Vector.t byte numBytes (* The bytestring. *)
  }.

Definition length_ByteString (bs : ByteString) := numBytes bs.

Definition wordToByte (w : word 8) : byte :=
  repr (BinInt.Z.of_N (wordToN w)).

Definition byteToWord (i : byte) : word 8 :=
  match intval i with
  | 0%Z => wzero 8
  | Zpos p => posToWord 8 p
  | _ => wzero 8
  end.

Definition ByteString_enqueue
         (b : bool)
         (bs : ByteString)
  : ByteString.
  refine (if (eq_nat_dec (padding bs) 7) then
            {| front := WO;
               byteString := Vector.append (byteString bs)
                                           (Vector.cons _ (wordToByte (WS b _)) _ (@Vector.nil _)) |}
  else
    {| front := WS b (front bs);
       padding := S (padding bs);
       byteString := byteString bs |}).
  abstract omega.
  abstract (pose proof (front bs) as w; generalize dependent (padding bs);
            intros ?? w; subst; exact w).
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
         (l : Vector.t byte (S numBytes))
  : bool * (Vector.t byte numBytes) * word 7 :=
  let (b, w') := word_dequeue (byteToWord (Vector.hd l)) in
  match numBytes return
        Vector.t byte (S numBytes) -> _ with
  | S numBytes' =>
    fun l =>
      match CharList_dequeue (Vector.tl l) with
      | (b', l'', tail) =>
        (b, Vector.cons _ (wordToByte (WS b' w')) _ l'', tail)
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
                  Vector.t byte nb
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
                    Vector.t byte nb
                    -> _ with
              | S n' =>
                fun l =>
                  match CharList_dequeue l with
                  | (b', l'', tail) =>
                    let (b, w') := word_dequeue front' in
                    Some (b', {| front := w';
                                 byteString := Vector.append l''
                                                             (Vector.cons _ (wordToByte (WS b tail)) _ (@Vector.nil _))
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

Definition ByteString_enqueue_char (bs : ByteString) (b : byte)
  := ByteString_enqueue_word (byteToWord b) bs.

Definition ByteString_enqueue_ByteString
           (bs bs' : ByteString)
  : ByteString :=
  let bs'' := Vector.fold_left ByteString_enqueue_char bs (byteString bs') in
  ByteString_enqueue_word (front bs') bs''.

Definition ByteString_id : ByteString.
  refine {| front := WO; byteString := Vector.nil _ |}.
  abstract omega.
Defined.

Definition CharStringToByteString
           (bs : ByteString)
  : Core.ByteString :=
  {| Core.padding := padding bs;
     Core.front := front bs;
     Core.paddingOK := paddingOK bs;
     Core.byteString := map byteToWord (Vector.to_list (byteString bs))
  |}.

Definition ByteStringToCharString
           (bs : Core.ByteString)
  : ByteString :=
  {| padding := Core.padding bs;
     front := Core.front bs;
     paddingOK := Core.paddingOK bs;
     byteString := Vector.map wordToByte (Vector.of_list (Core.byteString bs))
  |}.

Lemma byteToWord_wordToByte_eq :
  forall w, byteToWord (wordToByte w) = w.
Proof.
  Local Transparent Byte.repr.
  intros; shatter_word w.
  destruct x; destruct x0; destruct x1; destruct x2; destruct x3; destruct x4; destruct x5; destruct x6;
    reflexivity.
  Local Opaque Byte.repr.
Qed.

Lemma wordToByte_byteToWord_eq :
  forall b, wordToByte (byteToWord b) = b.
Proof.
  Local Transparent Byte.repr.
  destruct b.
  destruct intval0; simpl; intros; intuition eauto.
  - compute; apply Byte.mkint_eq; reflexivity.
  - repeat first [compute in intrange0; destruct intrange0; congruence
                 | destruct p as [p | p | ]; simpl
                 | compute; apply Byte.mkint_eq; reflexivity].
  - compute in intrange0; destruct p; destruct intrange0; congruence.
    Local Opaque Byte.repr.
Qed.

Lemma Vector_to_list_map {A B}
: forall n (v : Vector.t A n) (f : A -> B),
    Vector.to_list (Vector.map f v) = map f (Vector.to_list v).
Proof.
  induction v; simpl; intros; eauto.
  unfold Vector.to_list in *.
  rewrite IHv; reflexivity.
Qed.

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

Lemma CharStringToByteString_ByteStringToCharString_eq :
  forall bs, CharStringToByteString (ByteStringToCharString bs) = bs.
Proof.
  unfold CharStringToByteString, ByteStringToCharString; destruct bs; simpl;
    f_equal.
  rewrite Vector_to_list_map, Vector_to_list_of_list_eq.
  clear; induction byteString0; simpl; eauto.
  rewrite byteToWord_wordToByte_eq.
  rewrite IHbyteString0; reflexivity.
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

Lemma length_Vector_to_list {A B}
  : forall (f : A -> B) n (v : Vector.t A n),
    n = length (map f (Vector.to_list v)).
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

Lemma ByteStringToCharString_CharStringToByteString_eq :
  forall bs, ByteStringToCharString (CharStringToByteString bs) = bs.
Proof.
  unfold CharStringToByteString, ByteStringToCharString; destruct bs; simpl;
    eapply ByteString_f_equal; simpl.
  apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
  instantiate (1 := length_Vector_to_list byteToWord _ byteString0).
  clear; induction byteString0; simpl.
  - apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
  - unfold Vector.to_list in *; rewrite IHbyteString0; clear.
    erewrite eq_rect_Vector_cons; f_equal.
    apply wordToByte_byteToWord_eq.
    Grab Existential Variables.
    reflexivity.
Qed.

Lemma ByteString_enqueue_ByteString_ByteStringToCharString
  : forall bs bs',
    ByteString_enqueue_ByteString (ByteStringToCharString bs)
                                  (ByteStringToCharString bs')
    = ByteStringToCharString (Core.ByteString_enqueue_ByteString bs bs').
Proof.
Admitted.

Lemma length_ByteString_ByteStringToCharString_eq
  : forall bs,
    length_ByteString (ByteStringToCharString bs) =
    Core.length_ByteString bs.
Proof.
Admitted.

Lemma CharStringToByteString_ByteString_id_eq
  : CharStringToByteString ByteString_id = Core.ByteString_id.
Proof.
Admitted.

Instance ByteStringQueueTransformer : Transformer ByteString.
Proof.
  refine {| transform := ByteString_enqueue_ByteString;
            bin_measure := length_ByteString;
            transform_id := ByteString_id |}.
  - abstract (intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq b),
                      <- (ByteStringToCharString_CharStringToByteString_eq b'),
                      ByteString_enqueue_ByteString_ByteStringToCharString,
                      !length_ByteString_ByteStringToCharString_eq,
                      ByteString_enqueue_ByteString_measure;
              reflexivity).
  - abstract (intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq ByteString_id),
                      <- (ByteStringToCharString_CharStringToByteString_eq l),
                      ByteString_enqueue_ByteString_ByteStringToCharString,
                      CharStringToByteString_ByteString_id_eq,
                      ByteString_enqueue_ByteString_id_left; reflexivity).
  - abstract (intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq ByteString_id),
                      <- (ByteStringToCharString_CharStringToByteString_eq l),
                      ByteString_enqueue_ByteString_ByteStringToCharString,
                      CharStringToByteString_ByteString_id_eq,
                      ByteString_enqueue_ByteString_id_right; reflexivity).
  - abstract (intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq l),
                     <- (ByteStringToCharString_CharStringToByteString_eq m),
                     <- (ByteStringToCharString_CharStringToByteString_eq n),
                     !ByteString_enqueue_ByteString_ByteStringToCharString,
                     ByteString_enqueue_ByteString_assoc; reflexivity).
Defined.

Lemma ByteString_enqueue_ByteStringToCharString_eq
  : forall (b : bool) (b' : Core.ByteString),
    ByteString_enqueue b (ByteStringToCharString b') =
    ByteStringToCharString (Core.ByteString_enqueue b b').
Proof.
Admitted.

Lemma ByteString_enqueue_ByteStringToCharString_eq'
  : forall (b : bool) (b' : ByteString),
    Core.ByteString_enqueue b (CharStringToByteString b') =
    CharStringToByteString (ByteString_enqueue b b').
Proof.
Admitted.

Lemma ByteString_dequeue_ByteStringToCharString_eq
  : forall (b' : Core.ByteString),
    ByteString_dequeue (ByteStringToCharString b') =
    Ifopt (Core.ByteString_dequeue b')
    as bbs
         Then Some (fst bbs, ByteStringToCharString (snd bbs))
         Else None.
Proof.
Admitted.

Lemma ByteString_dequeue_ByteStringToCharString_eq'
  : forall (b' : ByteString),
    Core.ByteString_dequeue (CharStringToByteString b') =
    Ifopt (ByteString_dequeue b')
    as bbs
         Then Some (fst bbs, CharStringToByteString (snd bbs))
         Else None.
Proof.
Admitted.

Instance ByteString_QueueTransformerOpt
  : QueueTransformerOpt ByteStringQueueTransformer bool.
Proof.
refine {| B_measure f := 1;
          enqueue_opt := ByteString_enqueue;
          dequeue_opt := ByteString_dequeue |}.
  - abstract eauto.
  - abstract (simpl; intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq b'),
                             ByteString_enqueue_ByteStringToCharString_eq,
                             !length_ByteString_ByteStringToCharString_eq,
                             length_ByteString_enqueue';
              reflexivity).
  - abstract (simpl; intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq b) in *;
              rewrite ByteString_dequeue_ByteStringToCharString_eq in H;
              destruct (Core.ByteString_dequeue (CharStringToByteString b)) eqn : ?; simpl in *;
              try discriminate; injections;
              destruct p; apply ByteString_measure_dequeue_Some in Heqo;
              simpl in Heqo;
              rewrite length_ByteString_ByteStringToCharString_eq; simpl in *;
              rewrite <- Heqo;
              rewrite <- length_Vector_to_list, <- length_ByteString_ByteStringToCharString_eq,
              ByteStringToCharString_CharStringToByteString_eq; reflexivity).
  - simpl; intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq b),
                   <- (ByteStringToCharString_CharStringToByteString_eq b') in *;
    rewrite <- (ByteStringToCharString_CharStringToByteString_eq b'').
    rewrite ByteString_dequeue_ByteStringToCharString_eq in H;
    destruct (Core.ByteString_dequeue (CharStringToByteString b)) eqn : ?; simpl in *;
      try discriminate; destruct p; simpl in *.
    injection H; intros; subst.
    apply ByteString_dequeue_transform_opt with (b'' := CharStringToByteString b'') in Heqo;
          simpl in *.
    admit.
  - abstract (simpl; intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq b'),
                             <- (ByteStringToCharString_CharStringToByteString_eq b''),
                             !ByteString_enqueue_ByteString_ByteStringToCharString,
                             ByteString_enqueue_ByteStringToCharString_eq,
                             ByteString_enqueue_ByteString_enqueue_ByteString,
                             !ByteStringToCharString_CharStringToByteString_eq,
                             ByteString_enqueue_ByteStringToCharString_eq',
                             <- ByteString_enqueue_ByteString_ByteStringToCharString,
                             !ByteStringToCharString_CharStringToByteString_eq;
              reflexivity).
  - abstract (simpl; intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq ByteString_id),
                             ByteString_enqueue_ByteStringToCharString_eq,
                             ByteString_dequeue_ByteStringToCharString_eq;
              replace (CharStringToByteString ByteString_id)
              with Core.ByteString_id;
              [rewrite ByteString_dequeue_head_opt; reflexivity
              | unfold ByteString_id, Core.ByteString_id, CharStringToByteString; simpl;
                f_equal;
                apply le_uniqueness_proof]).
  - abstract reflexivity.
  - intros ? ? ? ?.
    simpl; intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq b),
                   <- (ByteStringToCharString_CharStringToByteString_eq b'),
                   !ByteString_dequeue_ByteStringToCharString_eq in *.
    destruct (Core.ByteString_dequeue (CharStringToByteString b)) eqn : ?;
      simpl in *; try discriminate.
    destruct (Core.ByteString_dequeue (CharStringToByteString b')) eqn : ?;
      simpl in *; try discriminate.
    destruct p; destruct p0.
    simpl in *; rewrite <- H in H0.
    rewrite (ByteString_dequeue_opt_inj (CharStringToByteString b) (CharStringToByteString b') Heqo).
    reflexivity.
    rewrite Heqo0; repeat f_equal.
    injection H0; eauto.
    assert (ByteStringToCharString b3 = ByteStringToCharString b1) by congruence.
    rewrite <- (CharStringToByteString_ByteStringToCharString_eq b3),
    <-  (CharStringToByteString_ByteStringToCharString_eq b1), H1.
    reflexivity.
Defined.

Definition build_aligned_ByteString
           {numBytes}
           (v : Vector.t byte numBytes)
  : ByteString.
  refine {| front := WO;
            byteString := v |}.
  abstract omega.
Defined.

Definition byteToInt32 (b : byte) : int.
  refine {| intval := Byte.intval b |}.
  pose proof (Byte.intrange b).
  abstract (intuition auto; etransitivity; [apply H1 | reflexivity]).
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

Lemma byteString_f_equal
  : forall bs bs'
           (padding_eq : padding bs' = padding bs)
           (numBytes_eq : numBytes bs' = numBytes bs),
    front bs = (@eq_rect nat (padding bs') (fun t => word t) (front bs') _ padding_eq)
    -> byteString bs = @eq_rect nat (numBytes bs') (Vector.t byte) (byteString bs') _ numBytes_eq
    -> bs = bs'.
Proof.
  destruct bs; destruct bs'; simpl; intros.
  subst.
  f_equal.
  apply Core.le_uniqueness_proof.
Qed.

Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Lemma vector_append_assoc {A} {n}
  : forall (v : Vector.t A n) {n'} (v' : Vector.t A n')
           {n''} (v'' : Vector.t A n''),
    append (append v v') v'' = cast (append v (append v' v'')) (Core.plus_assoc' n n' n'').
Proof.
  induction v; simpl.
  - induction v'; simpl.
    + induction v''; simpl.
      reflexivity.
      rewrite <- IHv''; eauto.
    + intros; rewrite <- IHv'.
      reflexivity.
  - intros; rewrite IHv; repeat f_equal.
    eapply Eqdep_dec.eq_proofs_unicity; intros;
      omega.
Qed.

Lemma build_aligned_ByteString_append
      {numBytes'}
  : forall (v' : Vector.t byte numBytes') {numBytes} (v : Vector.t byte numBytes),
    build_aligned_ByteString (Vector.append v v') = ByteString_enqueue_ByteString (build_aligned_ByteString v) (build_aligned_ByteString v').
Proof.
  simpl; intros; rewrite <- (ByteStringToCharString_CharStringToByteString_eq (build_aligned_ByteString v)),
                 <- (ByteStringToCharString_CharStringToByteString_eq (build_aligned_ByteString v')),
                 ByteString_enqueue_ByteString_ByteStringToCharString.
  unfold build_aligned_ByteString; simpl.
  unfold CharStringToByteString; simpl.
  erewrite <- massage_queue_into_ByteString.
  unfold ByteStringToCharString; simpl.
  assert (Datatypes.length
            (List.map byteToWord (to_list v) ++ List.map byteToWord (to_list v'))
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
    rewrite wordToByte_byteToWord_eq; eauto.
    eapply IHv'.
  -  simpl in H; injection H; intros.
     simpl; rewrite eq_rect_Vector_cons with (H' := H0); simpl.
     f_equal.
     rewrite wordToByte_byteToWord_eq; eauto.
     eapply IHv.
     Grab Existential Variables.
     reflexivity.
     omega.
Qed.

Lemma build_aligned_ByteString_cons
      {numBytes}
  : forall (v : Vector.t byte (S numBytes)),
    (build_aligned_ByteString v) = ByteString_enqueue_ByteString (build_aligned_ByteString (Vector.cons _ (Vector.hd v) _ (Vector.nil _))) (build_aligned_ByteString (Vector.tl v)).
Proof.
  intros; rewrite <- (build_aligned_ByteString_append (Vector.tl v)
                                                      (Vector.cons _ (Vector.hd v) _ (Vector.nil _))).
  pattern numBytes, v; apply VectorDef.caseS; simpl; intros; reflexivity.
Qed.

Require Import Fiat.BinEncoders.Env.Lib2.WordOpt.

Lemma aligned_decode_char_eq
      {numBytes}
  : forall (v : Vector.t byte (S numBytes)),
    WordOpt.decode_word' (transformerUnit := ByteString_QueueTransformerOpt) 8 (build_aligned_ByteString v)
    = Some (byteToWord (Vector.hd v), build_aligned_ByteString (Vector.tl v)).
Proof.
  simpl; intros.
  etransitivity.
  apply DecodeBindOpt_under_bind; intros; set_evars; rewrite !DecodeBindOpt_assoc.
  repeat (unfold H; apply DecodeBindOpt_under_bind; intros; set_evars; rewrite !DecodeBindOpt_assoc).
  unfold H5; higher_order_reflexivity.
  simpl.
  pattern numBytes, v; eapply Vector.caseS; intros; simpl; clear v numBytes.
  replace (build_aligned_ByteString t) with (ByteString_enqueue_ByteString ByteString_id (build_aligned_ByteString t)).
  rewrite <- (wordToByte_byteToWord_eq h).
  generalize (byteToWord h); intro; rewrite byteToWord_wordToByte_eq.
  shatter_word w.
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
  rewrite byteToWord_wordToByte_eq; simpl.
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

Fixpoint VectorByteToWord {numBytes} (v : t byte numBytes) : word (8 * numBytes) :=
  match numBytes return
        t byte numBytes
        -> word (8 * numBytes) with
  | 0 => fun _ => WO
  | S numBytes' => fun v => eq_rect _ word (Core.append_word (VectorByteToWord (Vector.tl v)) (byteToWord (Vector.hd v)))
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
                        (Some (eq_rect (S (m + n)) word (SW_word b w) (n + S m) (PeanoNat.Nat.add_comm (S m) n), b1))
                        (m + S n) H0)
             by (intros; rewrite H; reflexivity).
      rewrite Some_eq_rect_eq in H1.
      rewrite <- transport_pp in H1.
      erewrite Eqdep_dec.eq_proofs_unicity with (p1 := (plus_n_Sm m n));
        intros; try omega.
      rewrite <- H1.
      rewrite eq_rect_decode_word; reflexivity.
      assert (n + S m = m + S n) by omega.
      rewrite <- eq_rect_decode_word with (H := H0), H; simpl.
      destruct H0; reflexivity.
      assert (n + S m = m + S n) by omega.
      rewrite <- eq_rect_decode_word with (H := H0), H; simpl.
      destruct H0; reflexivity.
Qed.

Lemma aligned_decode_char_eq'
          {numBytes numBytes'}
  : forall (v : Vector.t byte (S numBytes' + numBytes)),
    WordOpt.decode_word' (transformerUnit := ByteString_QueueTransformerOpt) (8 * (S numBytes')) (build_aligned_ByteString v)
    = let (v', v'') := Vector_split (S numBytes') numBytes v in
      Some (VectorByteToWord v', build_aligned_ByteString v'').
Proof.
  induction numBytes'.
  - intros; rewrite aligned_decode_char_eq.
    unfold Vector_split; simpl.
    repeat f_equal; generalize (byteToWord (Vector.hd v)); intro; shatter_word w.
    fold Nat.add.
    apply Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
  - revert IHnumBytes'; generalize (S numBytes'); intros.
    match goal with
      |- ?k = _ =>
      replace k
      with (`(w, v') <-  Some (byteToWord (Vector.hd v), build_aligned_ByteString (Vector.tl v));
            `(w', v'') <- WordOpt.decode_word' (8 * n) v';
            Some (eq_rect _ word (Core.append_word w' w) _ (sym_eq (NPeano.Nat.mul_succ_r _ _)), v''))
    end.
    simpl.
    rewrite IHnumBytes'; simpl.
    destruct (Vector_split n numBytes (Vector.tl v)); simpl; repeat f_equal; clear.
    unfold DecodeBindOpt at 1; unfold If_Opt_Then_Else.
    assert (8 + 8 * n = 8 * S n) by omega.
    rewrite <- eq_rect_decode_word with (H := H).
    assert (8 * n + 8 = 8 + 8 * n) by omega.
    match goal with
      |- context [decode_word' ?m (build_aligned_ByteString ?b) ] =>
      replace (decode_word' m (build_aligned_ByteString b))
      with (`(w, v') <- Some (byteToWord (hd b), build_aligned_ByteString (tl b));
            `(w', v'') <- decode_word' (8 * n) v';
            Some (eq_rect _ word (append_word w' w) _ H0, v''))
    end.
    unfold DecodeBindOpt at 2; unfold If_Opt_Then_Else.
    destruct (decode_word' (8 * n) (build_aligned_ByteString (tl v))) as [ [? ?] | ]; try reflexivity.
    unfold DecodeBindOpt; unfold If_Opt_Then_Else.
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

Notation "x <- y ; z" := (Bind y%comp (fun x => z%comp))
                           (at level 81, right associativity,
                            format "'[v' x  <-  y ; '/' z ']'") : comp_scope.

Notation "'Let' a ':=' b 'in' k" := (LetIn b (fun a => k))
                                    (at level 81, right associativity,
                                     format "'[v' 'Let'  a  ':=' b  'in' '/' k ']'").

Lemma VectorByteToWord_cons :
  forall n v h H,
    VectorByteToWord (Vector.cons byte h n v)
    = eq_rect _ _ (Core.append_word (VectorByteToWord v) (byteToWord h)) _ H.
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

(* Variable magic : forall (n : nat), Fin.t (4 * n).

Lemma decode_list_decode_list'_eq
  : forall n m (b : Vector.t byte ((4 * n) + m)) cd,
    decode_list (decode_int Int.wordsize) n (build_aligned_ByteString b) cd
    = Some (fst (decode_list' n (fun p cd =>
                                   (ofbytes (Vector.nth b (Fin.L m (magic p)))
                                            (Vector.nth b (Fin.FS (Fin.L m (magic _ p))))
                                            (Vector.nth b p)
                                            (Vector.nth b p), cd)) cd),
            (build_aligned_ByteString b),
            snd (decode_list' n (fun p cd =>
                                   (ofbytes (Vector.nth b p)
                                            (Vector.nth b p)
                                            (Vector.nth b p)
                                            (Vector.nth b p), cd)) cd)).
Admitted. *)
