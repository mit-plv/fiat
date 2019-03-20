Require Import
        Coq.Arith.Peano_dec
        Coq.Logic.Eqdep_dec
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.BinLib.Core.

Require Import
        Bedrock.Word.

Lemma eq_rect_Vector_cons {A}
  : forall n m a v H H',
    eq_rect (S n) (Vector.t A) (Vector.cons A a n v) (S m) H =
    Vector.cons _ a _ (eq_rect n (Vector.t A) v _ H').
Proof.
  intros.
  destruct H'; simpl; symmetry;
    apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
Qed.

Module ByteBuffer.
  Definition t n := Vector.t char n.

  Definition nil := @Vector.nil char.
  Definition cons (c: char) {n} (b: t n): t (S n) := Vector.cons _ c n b.

  Definition hd {n} (b: t (S n)): char := Vector.hd b.
  Definition tl {n} (b: t (S n)): t n := Vector.tl b.

  Definition append {n1 n2} (b1: t n1) (b2: t n2): t (n1 + n2) :=
    Vector.append b1 b2.
  Definition fold_left {B: Type} (f: B -> char -> B) (b: B) {n} (v: t n): B :=
    Vector.fold_left f b v.
  Definition to_list {n} (b: t n): list char :=
    Vector.to_list b.
  Definition of_list (l: list char): t (List.length l) :=
    Vector.of_list l.
  Definition to_vector {n} (b: t n): Vector.t char n :=
    b.
  Definition of_vector {n} (v: Vector.t char n): t n :=
    v.

  Lemma to_list_of_list_eq
    : forall (v : list _),
      to_list (of_list v) = v.
  Proof.
    induction v; simpl.
    reflexivity.
    replace (a :: v) with (a :: to_list (of_list v)).
    reflexivity.
    rewrite IHv; reflexivity.
  Qed.

  Lemma to_list_length :
    forall n (v : t n),
      n = length (to_list v).
  Proof.
    induction v; simpl; eauto.
  Qed.

  Lemma t_ind :
    forall (P : forall n : nat, t n -> Prop),
      P 0 nil ->
      (forall (h : char) (n : nat) (v : t n), P n v -> P (S n) (cons h v)) ->
      forall (n : nat) (v : t n), P n v.
  Proof. intros. induction v; eauto. Qed.

  Lemma of_list_to_list :
    forall (n : nat) (b : t n),
      of_list (to_list b) =
      eq_rect n t b (length (to_list b))
              (to_list_length n b).
  Proof.
    induction b; simpl.
    - apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec.
    - unfold of_list, to_list, Vector.to_list in *.
      simpl; rewrite IHb; clear.
      unfold t; erewrite eq_rect_Vector_cons; f_equal.
  Qed.
End ByteBuffer.

Section ByteBufferFormat.
  Context {T : Type}.
  Context {monoid : Monoid T}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Context {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b))).

  Definition format_bytebuffer
             (b : { n : _ & ByteBuffer.t n })
             (ce : CacheFormat) : Comp (T * CacheFormat) :=
    format_Vector format_word (projT2 b) ce.

  Definition decode_bytebuffer (s : nat) (b : T) (cd : CacheDecode) : option ({ n :_ & ByteBuffer.t n } * T * CacheDecode) :=
    match decode_Vector (decode_word (sz := 8)) s b cd with
    | Some (v, t, cd) => Some (existT ByteBuffer.t _ v, t, cd)
    | None => None
    end.

  Theorem ByteBuffer_decode_correct
    :
      forall n,
        CorrectDecoder
          monoid
          (fun ls => projT1 ls = n)
          (fun ls => projT1 ls = n)
          eq
          format_bytebuffer (decode_bytebuffer n) P
          format_bytebuffer.
  Proof.
    unfold format_bytebuffer; split; intros.
    { eapply (fun H' => proj1 (Vector_decode_correct (fun _ => True) _ decode_word P H' _)) in H1; eauto.
      instantiate (1 := ext) in H1; destruct H1 as [? [? ?] ]; eexists _, _; split; eauto.
      split_and; unfold id in *; destruct s; unfold decode_bytebuffer;
        subst; rewrite H2; simpl in *; intuition eauto.
      intuition eauto.
      subst; eauto.
      apply Word_decode_correct; eauto.
    }
    { destruct v; simpl in *.
      unfold decode_bytebuffer in H1.
      destruct (decode_Vector decode_word n t env') as [ [ [? ?] ? ] | ] eqn: H';
        try discriminate; injection H1; intros; subst; clear H1.
      apply inj_pair2_eq_dec in H4; try decide equality; subst.
      eapply (fun H' H'' => proj2 (Vector_decode_correct (fun _ => True)
                                                         format_word decode_word P H' H'')) in H';
        try eassumption; destruct H'; destruct_ex; split_and; subst; intuition eauto.
      unfold id in *; subst; eexists _, _; simpl; intuition eauto.
      apply Word_decode_correct; eauto.
    }
  Defined.
End ByteBufferFormat.
