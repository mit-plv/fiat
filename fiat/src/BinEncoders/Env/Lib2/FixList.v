Require Import
        Fiat.BinEncoders.Env.Common.Specs.
Require Export
        Coq.Lists.List.

Notation "| ls |" := (Datatypes.length ls) (at level 200).

Section FixList.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {transformer : Transformer B}.

  Variable A_predicate : A -> Prop.
  Variable A_encode : A -> CacheEncode -> B * CacheEncode.
  Variable A_decode : B -> CacheDecode -> A * B * CacheDecode.
  Variable A_decode_pf : encode_decode_correct cache transformer A_predicate A_encode A_decode.

  Fixpoint encode_list (xs : list A) (ce : CacheEncode) : B * CacheEncode :=
    match xs with
    | nil => (transform_id, ce)
    | x :: xs' => let (b1, env1) := A_encode x ce in
                  let (b2, env2) := encode_list xs' env1 in
                      (transform b1 b2, env2)
    end.

  Fixpoint decode_list (s : nat) (b : B) (cd : CacheDecode) : list A * B * CacheDecode :=
    match s with
    | O => (nil, b, cd)
    | S s' => let (x1, e1) := A_decode b cd in
              let (x, b1) := x1 in
              let (x2, e2) := decode_list s' b1 e1 in
              let (xs, b2) := x2 in
              (x :: xs, b2, e2)
    end.

  Theorem FixList_decode_correct :
    forall sz,
      encode_decode_correct
        cache transformer
        (fun ls => |ls| = sz /\ forall x, In x ls -> A_predicate x)
        encode_list (decode_list sz).
  Proof.
    unfold encode_decode_correct.
    intros sz env env' xenv xenv' l l' bin' ext ext' Eeq Ppred Penc Pdec.
    generalize dependent sz. generalize dependent env. generalize dependent env'.
    generalize dependent xenv. generalize dependent xenv'. generalize dependent bin'.
    generalize dependent l'. generalize dependent ext'. induction l.
    { intros.
      inversion Penc; subst; clear Penc.
      rewrite transform_id_left in Pdec. simpl in *. destruct Ppred.
      subst. simpl in *. inversion Pdec. subst. intuition eauto. }
    { intros.
      destruct sz. inversion Ppred. inversion H.
      simpl in *. destruct Ppred.
      assert (A_predicate a) by eauto.
      destruct (A_encode a env) eqn: ?.
      destruct (encode_list l c) eqn: ?.
      inversion H; subst; clear H.
      inversion Penc; subst; clear Penc.
      rewrite <- transform_assoc in Pdec.
      destruct (A_decode (transform b (transform b0 ext)) env') as [[? ?] ?] eqn: ?.
      destruct (A_decode_pf _ _ _ _ _ _ _ _ _ Eeq H1 Heqp Heqp1) as [? [? ?]]. subst.
      destruct (decode_list (|l |) (transform b0 ext) c0) as [[? ?] ?] eqn: ?.
      specialize (IHl _ _ _ _ _ _ _ H Heqp0 _ (conj eq_refl (fun x h => H0 x (or_intror h))) Heqp2).
      inversion Pdec; subst; clear Pdec.
      intuition eauto. subst. eauto. }
  Qed.

  Definition encode_list_body := (fun (acc: B * CacheEncode) x =>
                                       let (bacc, env) := acc in
                                       let (b1, env1) := A_encode x env in
                                       (transform bacc b1, env1)).

  Lemma encode_list_body_characterization :
    forall xs base env,
      fold_left encode_list_body xs (base, env) =
      (let (b2, env2) := fold_left encode_list_body xs (transform_id, env) in
       (transform base b2, env2)).
  Proof.
    induction xs; simpl.
    + intros; rewrite transform_id_right; reflexivity.
    + intros; destruct (A_encode _ _).
      rewrite IHxs, transform_id_left, (IHxs b).
      destruct (fold_left _ _ _).
      rewrite transform_assoc; reflexivity.
  Qed.

  Lemma encode_list_as_foldl :
    forall xs env,
      encode_list xs env =
      fold_left encode_list_body xs (transform_id, env).
  Proof.
    induction xs; simpl.
    + reflexivity.
    + intros; destruct (A_encode _ _).
      rewrite IHxs, transform_id_left, (encode_list_body_characterization xs b c).
      destruct (fold_left _ _ _); reflexivity.
  Qed.


End FixList.
