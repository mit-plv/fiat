Require Export Coq.Lists.List.
Require Import Fiat.BinEncoders.NoEnv.Specs
               Fiat.BinEncoders.NoEnv.Libraries.Sig
               Coq.omega.Omega.

Set Implicit Arguments.

Section FixList2Encoder.
  Variable (A : Type)
           (B : Type)
           (size : nat)
           (encode_A : A * B -> B)
           (predicate_A : A -> Prop)
           (decoder_A : decoder (fun bundle => predicate_A (fst bundle)) encode_A).

  Definition data_t := { xs : list A | length xs = size }.

  Definition FixList2_predicate (bundle : data_t * B) :=
    forall x, In x (proj1_sig (fst bundle)) -> predicate_A x.

  Fixpoint encode' (xs : list A) (ext : B) :=
    match xs with
      | nil => ext
      | x :: xs => encode_A (x, encode' xs ext)
    end.

  Definition FixList2_encode (bundle : data_t * B) := encode' (proj1_sig (fst bundle)) (snd bundle).

  Fixpoint decode' (len : nat) (b : B) : list A * B :=
    match len with
    | O => (nil, b)
    | S size' => let (_data, _bin) := @decode _ _ _ _ decoder_A b in
                 let (_rest, _bin') := decode' size' _bin in
                     (_data :: _rest, _bin')
    end.

  Definition FixList2_decode (b : B) : data_t * B.
    refine (exist _ (fst (decode' size b)) _, snd (decode' size b)).
    generalize dependent b; induction size; intuition eauto.
    simpl. destruct (decode b). specialize (IHn b0). destruct (decode' n b0). simpl. f_equal. eauto.
  Defined.

  Theorem FixList2_encode_decode_correct :
    encode_decode_correct FixList2_predicate FixList2_encode FixList2_decode.
  Proof.
    unfold encode_decode_correct, FixList2_predicate, FixList2_encode, FixList2_decode.
    intros [[data data_pf] ext] pred_pf.
    f_equal; try eapply sig_equivalence; simpl in *;
    generalize dependent data; induction size; intuition eauto; simpl in *;
    destruct data; inversion data_pf; eauto; simpl in *.
    - assert (forall x : A, In x data -> predicate_A x) by intuition.
      specialize (IHn data H0 H). rewrite (@decode_correct _ _ _ _ decoder_A); eauto.
      rewrite H0. destruct (decode' n (encode' data ext)). subst. eauto.
    - assert (forall x : A, In x data -> predicate_A x) by intuition.
      specialize (IHn data H0 H). rewrite (@decode_correct _ _ _ _ decoder_A); eauto.
      rewrite H0. destruct (decode' n (encode' data ext)). subst. eauto.
  Qed.
End FixList2Encoder.

Global Instance FixList2_decoder
       (A : Type)
       (B : Type)
       (size : nat)
       (predicate_A : A -> Prop)
       (encode_A : A * B -> B)
       (decoder_A : decoder (fun bundle => predicate_A (fst bundle)) encode_A)
  : decoder (FixList2_predicate predicate_A) (FixList2_encode (size:=size) encode_A) :=
  { decode := FixList2_decode size predicate_A decoder_A;
    decode_correct := @FixList2_encode_decode_correct _ _ _ _ _ _ }.

Arguments FixList2_predicate / _ _ _ _ _.
