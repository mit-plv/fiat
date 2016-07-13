Require Import
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts.

Unset Implicit Arguments.
Section Word.
  Context {sz : nat}.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : QueueTransformerOpt transformer bool}.

  Fixpoint encode_word' (s : nat) (w : word s) (b' : B) : B :=
    match w with
    | WO => b'
    | WS b s' w' => encode_word' s' w' (enqueue_opt b b')
    end.

  Definition encode_word_Impl (w : word sz) (ce : CacheEncode) : B * CacheEncode := (encode_word' sz w transform_id, addE ce sz).

  Definition encode_word_Spec (w : word sz) (ce : CacheEncode) : Comp (B * CacheEncode) :=
    ret (encode_word' sz w transform_id, addE ce sz).

  Fixpoint decode_word' (s : nat) (b : B) : option (word s * B) :=
    match s with
    | O => Some (WO, b)
    | S s' =>
      `(c, b') <- dequeue_opt b;
      `(w, bx) <- decode_word' s' b';
       Some (WS c w, bx)
    end.

  Definition decode_word (b : B) (cd : CacheDecode) : option (word sz * B * CacheDecode) :=
    Ifopt decode_word' sz b as decoded Then Some (decoded, addD cd sz) Else None.

  Lemma dequeue_encode_word'_enqueue_opt' :
    forall n w w' b b' ext,
      dequeue_opt w' = Some (b, b')
      -> dequeue_opt (transform (encode_word' n w w') ext) =
           Some (b, (transform (encode_word' n w b') ext)).
  Proof.
    induction w; simpl; intros.
    - erewrite dequeue_transform_opt; eauto using dequeue_head_opt.
    - eapply IHw.
      rewrite <- (transform_id_right w'), enqueue_transform_opt.
      erewrite (dequeue_transform_opt _ (enqueue_opt b transform_id)); eauto.
      rewrite <- enqueue_transform_opt, transform_id_right; reflexivity.
  Qed.

  Corollary dequeue_encode_word'_enqueue_opt :
    forall n w b ext,
      dequeue_opt (transform (encode_word' n w (enqueue_opt b transform_id)) ext) =
      Some (b, (transform (encode_word' n w transform_id) ext)).
  Proof.
    intros; eapply dequeue_encode_word'_enqueue_opt'.
    eapply dequeue_head_opt.
  Qed.

  Theorem Word_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      encode_decode_correct_f cache transformer (fun _ => True)
                              (fun _ _ => True)
                              encode_word_Spec decode_word P.
  Proof.
    unfold encode_decode_correct_f, encode_word_Spec, decode_word; split.
    - intros env env' xenv w w' ext Eeq _ _ Penc.
      computes_to_inv; injections.
      generalize dependent sz.
      induction w; simpl in *.
      { eexists; split; eauto; try rewrite !transform_id_left;
        eauto using add_correct. }
      { destruct_ex; intuition.
        destruct (decode_word' n (transform (encode_word' n w transform_id) ext)) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate; injections.
        rewrite dequeue_encode_word'_enqueue_opt; simpl.
        eexists; split; eauto using add_correct.
        rewrite Heqo; simpl; f_equal.
      }
    - intros.
      destruct (decode_word' sz bin)
        as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
      injections.
      generalize dependent bin.
      induction data; simpl in *.
      { intros; computes_to_inv; intros; injection Heqo; clear Heqo;
        intros; subst.
        repeat eexists; eauto; try rewrite !transform_id_left;
        eauto using add_correct.
      }
      { intros; intuition.
        destruct (dequeue_opt bin) as [ [? ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_word' n b1) as [ [? ? ] | ] eqn: ? ;
          simpl in *; try discriminate.
        injection Heqo; intros; subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H2; subst.
        eapply IHdata in Heqo1.
        intuition; destruct_ex; intuition; subst.
        computes_to_inv; injections.
        eexists; eexists; repeat split.
        eapply dequeue_opt_inj; eauto.
        eapply dequeue_encode_word'_enqueue_opt.
        apply add_correct; eauto.
        eapply Peano_dec.eq_nat_dec.
      }
  Qed.

  Lemma decode_word'_le
    : forall (a : word sz) (b' b1 : B),
      decode_word' _ b1  = Some (a, b') -> le_B b' b1.
  Proof.
    induction a; simpl.
    - intros; injections; unfold le_B; omega.
    - intros; simpl.
      destruct (dequeue_opt b1) as [ [? ?] | ] eqn: ? ;
        subst; simpl in *; try discriminate.
      destruct (decode_word' n b2) as [ [? ?] | ] eqn: ? ;
        subst; simpl in *; try discriminate.
      injection H; intros; subst; unfold le_B in *.
      pose proof (IHa b' b2).
      rewrite Heqo0 in H0; simpl in *.
      apply Eqdep_dec.inj_pair2_eq_dec in H1; subst.
      pose proof (H0 (eq_refl _)).
      eapply measure_dequeue_Some in Heqo; subst.
      omega.
      eapply Peano_dec.eq_nat_dec.
  Qed.

  Lemma decode_word_le
    : forall (cd : CacheDecode) (a : word sz)
             (b' b1 : B) (cd' : CacheDecode),
      decode_word b1 cd = Some (a, b', cd') -> le_B b' b1.
  Proof.
    unfold decode_word.
    intros; destruct (decode_word' sz b1) as [ [? ?] | ] eqn: ? ;
      subst; simpl in *; try discriminate.
    injections.
    eapply decode_word'_le; eauto.
  Qed.

  Lemma decode_word'_lt
    : forall (a : word (S sz)) (b' b1 : B),
      decode_word' _ b1 = Some (a, b') -> lt_B b' b1.
  Proof.
    simpl; intros; injections; unfold lt_B.
    destruct (dequeue_opt b1) as [ [? ?] | ] eqn: ? ;
      subst; simpl in *; try discriminate.
    apply measure_dequeue_Some in Heqo; subst.
    destruct (decode_word' sz b0) as [ [? ?] | ] eqn: ? ;
        subst; simpl in *; try discriminate.
    eapply decode_word'_le in Heqo0; injections.
    rewrite Heqo.
    unfold le_B in *.
    pose proof (B_measure_gt_0 b).
    omega.
  Qed.

  Lemma decode_word_lt
    : forall (cd : CacheDecode) (a : word (S sz))
             (b' b1 : B) (cd' : CacheDecode),
      Ifopt decode_word' _ b' as decoded Then Some (decoded, addD cd (S sz)) Else None = Some (a, b1, cd') -> lt_B b1 b'.
  Proof.
    intros; destruct (decode_word' (S sz) b') as [ [? ?] | ] eqn: ? ;
    try eapply decode_word'_lt in Heqo;
      simpl in *; try (subst; discriminate).
    injections.
    unfold lt_B in *.
    omega.
  Qed.

  Definition encode_unused_word_Spec' (sz : nat) b
             (_ : unit) (ctx : CacheEncode) :=
    (w <- { w : word sz | True};
       ret (encode_word' sz w b, addE ctx sz))%comp.

  Definition encode_unused_word_Spec
             (sz : nat)
             (ctx : CacheEncode) :=
    encode_unused_word_Spec' sz transform_id tt ctx.

  Fixpoint transformer_get_word {B}
           {transformer : Transformer B}
           {transformer_opt : QueueTransformerOpt transformer bool}
           (sz : nat)
           (b : B)
    : option (word sz) :=
    match sz with
    | 0 => Some WO
    | S sz' =>
      match dequeue_opt b with
      | Some (v, b') =>
        match transformer_get_word sz' b' with
        | Some w => Some (WS v w)
        | _ => None
        end
      | _ => None
      end
    end.

  Fixpoint transformer_dequeue_word
         (sz : nat)
         (b : B)
  : option (word sz * B) :=
  match sz with
  | 0 => Some (WO, b)
  | S sz' =>
    match dequeue_opt b with
    | Some (v, b') =>
      match transformer_dequeue_word sz' b' with
      | Some (w', b'') => Some (WS v w', b'')
      | _ => None
      end
    | _ => None
    end
  end.

  Lemma transformer_dequeue_word_eq_decode_word' :
    forall (sz : nat)
           (b : B),
      transformer_dequeue_word sz b = decode_word' sz b.
  Proof.
    induction sz0; simpl; eauto.
  Qed.

  Lemma transformer_dequeue_encode_word'
        (sz' : nat)
    : forall (w : word sz') (ext : B),
      transformer_dequeue_word sz' (transform (encode_word' _ w transform_id ) ext) = Some (w, ext).
  Proof.
    induction sz'; simpl; intros.
    - rewrite (shatter_word w); eauto.
      unfold encode_word'; rewrite transform_id_left; reflexivity.
    - rewrite (shatter_word w); simpl.
      rewrite dequeue_encode_word'_enqueue_opt.
      rewrite IHsz'; eauto.
  Qed.

  Definition decode_unused_word' (s : nat) (b : B) : option (unit * B) :=
    Ifopt transformer_dequeue_word s b as b' Then Some (tt, snd b') Else None.

  Definition decode_unused_word (sz' : nat)
             (b : B) (cd : CacheDecode) : option (unit * B * CacheDecode) :=
    Ifopt decode_unused_word' sz' b as decoded Then Some (decoded, addD cd sz') Else None.

  Theorem unused_word_decode_correct sz'
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      encode_decode_correct_f cache transformer (fun _ => True)
                              (fun _ _ => True)
                              (encode_unused_word_Spec' sz' transform_id) (decode_unused_word sz') P.
  Proof.
    unfold encode_decode_correct_f, encode_unused_word_Spec', decode_unused_word; split.
    - intros env env' xenv w w' ext Eeq _ _ Penc.
      computes_to_inv; injections.
      unfold decode_unused_word'.
      rewrite transformer_dequeue_encode_word'; simpl.
      destruct w.
      eexists; split; eauto using add_correct.
    - intros.
      destruct (decode_unused_word' sz' bin)
        as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
      injections.
      destruct data.
      generalize dependent bin.
      induction sz'; simpl in *.
      { intros; computes_to_inv; intros; injection Heqo; clear Heqo;
        intros; subst.
        repeat eexists; eauto; try rewrite !transform_id_left;
        eauto using add_correct.
        instantiate (1 := WO); simpl.
        rewrite !transform_id_left; eauto.
      }
      { intros; intuition.
        unfold decode_unused_word' in Heqo.
        simpl in Heqo.
        destruct (dequeue_opt bin) as [ [? ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (transformer_dequeue_word sz' b0) as [ [? ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        injection Heqo; intros; subst.
        destruct (IHsz' b0).
        unfold decode_unused_word'; rewrite Heqo1; simpl; eauto.
        intuition; destruct_ex; intuition; subst.
        computes_to_inv; injections.
        eexists; eexists; repeat split.
        repeat computes_to_econstructor; eauto.
        instantiate (1 := WS b v); simpl.
        eapply dequeue_opt_inj; eauto.
        eapply dequeue_encode_word'_enqueue_opt.
        apply add_correct; eauto.
      }
  Qed.

End Word.

Arguments encode_unused_word_Spec {_ _ _ _ _} sz ctx _.

Lemma transformer_get_encode_word' {B}
      {transformer : Transformer B}
      {transformer_opt : QueueTransformerOpt transformer bool}
      (sz : nat)
  : forall (w : word sz) (ext : B),
    transformer_get_word sz (transform (encode_word' _ w transform_id) ext) = Some w.
Proof.
  induction sz; simpl; intros.
  - rewrite (shatter_word w); eauto.
  - rewrite (shatter_word w); simpl.
    rewrite dequeue_encode_word'_enqueue_opt.
    rewrite IHsz; eauto.
Qed.
