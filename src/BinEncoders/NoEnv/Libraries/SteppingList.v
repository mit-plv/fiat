Require Export Coq.Lists.List.
Require Import Fiat.BinEncoders.NoEnv.Specs
               Fiat.BinEncoders.NoEnv.Libraries.BinCore
               Fiat.BinEncoders.NoEnv.Libraries.Sig
               Coq.omega.Omega.

Set Implicit Arguments.

Section SteppingListEncoder.
  Variable (A : Type)
           (B : Type)
           (halt : A)
           (halt_dec : forall a, {a = halt} + {a <> halt})

           (fuel : nat)
           (encode_A : A * B -> B)
           (predicate_A : A -> Prop)
           (decoder_A : decoder (fun bundle => predicate_A (fst bundle)) encode_A).

  Definition data_t fuel := { xs : list A | length xs <= fuel /\ forall x, In x xs -> x <> halt }.

  Definition SteppingList_predicate (bundle : data_t fuel * B) :=
    predicate_A halt /\ forall x, In x (proj1_sig (fst bundle)) -> predicate_A x.

  Fixpoint encode' (data : list A) (ext : B) :=
    match data with
      | nil => encode_A (halt, ext)
      | cons s data' => encode_A (s, encode' data' ext)
    end.

  Definition SteppingList_encode (bundle : data_t fuel * B) :=
    let (_a, _bin) := bundle
    in  encode' (proj1_sig _a) _bin.

  Fixpoint decode' (b : B) (f : nat) :=
    let (x, b') := @decode _ _ _ _ decoder_A b in
    if halt_dec x then
      (nil, b')
    else
      match f with
      | O => (nil, b') (* bogus *)
      | S f' => let (xs, b'') := decode' b' f'
                in  (x :: xs, b'')
      end.

  Definition SteppingList_decode (b : B) : data_t fuel * B.
    refine (exist _ (fst (decode' b fuel)) _, snd (decode' b fuel)).
    generalize dependent b; induction fuel.
    - intro. simpl. destruct (decode b). destruct (halt_dec a). subst.
      intuition eauto. intuition eauto.
    - intro b. simpl. split. destruct (decode b). destruct (halt_dec a). eapply le_0_n.
      specialize (IHn b0). destruct (decode' b0 n). simpl. eapply le_n_S. intuition eauto.
      intro x. destruct (decode b). destruct (halt_dec a). intuition.
      specialize (IHn b0). destruct (decode' b0 n). simpl. intuition eauto. subst. eauto.
  Defined.

  Theorem SteppingList_encode_decode_correct :
    encode_decode_correct SteppingList_predicate SteppingList_encode SteppingList_decode.
  Proof.
    unfold encode_decode_correct, SteppingList_predicate, SteppingList_encode, SteppingList_decode.
    intros [[data data_pf] ext] [halt_pf pred_pf]; simpl in *.
    generalize dependent fuel; generalize dependent data; clear fuel.
    induction data; intros pred_pf fuel data_pf.
    - f_equal;
      try eapply sig_equivalence; destruct fuel; simpl;
      rewrite (@decode_correct _ _ _ _ decoder_A); eauto; destruct (halt_dec halt); intuition.
    - simpl in *; destruct fuel as [ | fuel' ]; try omega; clear fuel.
      simpl. rewrite (@decode_correct _ _ _ _ decoder_A); eauto.
      destruct (halt_dec a). subst. specialize (proj2 data_pf halt). tauto.
      assert (forall x : A, In x data -> predicate_A x) by intuition.
      assert (length data <= fuel' /\ (forall x : A, In x data -> x <> halt)).
      split; [ eapply (le_S_n _ _ (proj1 data_pf)) | intros x pf; eapply data_pf; eauto ].
      specialize (IHdata H fuel' H0). inversion IHdata. clear IHdata.
      f_equal. eapply sig_equivalence.
      rewrite H3. destruct (decode' (encode' data ext) fuel'). simpl in *. rewrite H2. eauto.
      rewrite H3. destruct (decode' (encode' data ext) fuel'). simpl in *. eauto.
  Qed.
End SteppingListEncoder.

Global Instance SteppingList_decoder
       (A : Type)
       (halt : A)
       (halt_dec : forall a, {a = halt} + {a <> halt})
       (fuel : nat)
       (predicate_A : A -> Prop)
       (encode_A : A * bin_t -> bin_t)
       (decoder_A : decoder (fun bundle => predicate_A (fst bundle)) encode_A)
  : decoder (SteppingList_predicate predicate_A)
            (SteppingList_encode encode_A) :=
  { decode := SteppingList_decode halt_dec fuel predicate_A decoder_A;
    decode_correct := SteppingList_encode_decode_correct _ _ }.

Arguments SteppingList_predicate / _ _ _ _ _ _.