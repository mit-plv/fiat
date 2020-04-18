Require Export
        Coq.Lists.List.
Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Sig.

Set Implicit Arguments.

Section IListEncoder.
  Variable size : nat.
  Variable A : Type.
  Variable bin : Type.
  Variable cache : Cache.
  Variable transformer : Transformer bin.
  Variable A_predicate : A -> Prop.
  Variable A_encode : A -> CacheEncode -> bin * CacheEncode.
  Variable A_decode : bin -> CacheDecode -> A * bin * CacheDecode.
  Variable A_decode_pf : encode_decode_correct cache transformer A_predicate A_encode A_decode.

  Definition IList := { xs : list A | length xs = size }.

  Definition IList_predicate (l : IList) :=
    forall x, In x (proj1_sig l) -> A_predicate x.

  Fixpoint IList_encode' (xs : list A) (env : CacheEncode) :=
    match xs with
    | nil => (transform_id, env)
    | x :: xs' => let (b1, env1) := A_encode x env in
                  let (b2, env2) := IList_encode' xs' env1 in
                      (transform b1 b2, env2)
    end.

  Definition IList_encode'_body := (fun (acc: bin * CacheEncode) x =>
                             let (bacc, env) := acc in
                             let (b1, env1) := A_encode x env in
                             (transform bacc b1, env1)).

  Lemma IList_encode'_body_characterization :
    forall xs base env,
      fold_left IList_encode'_body xs (base, env) =
      (let (b2, env2) := fold_left IList_encode'_body xs (transform_id, env) in
       (transform base b2, env2)).
  Proof.
    induction xs; simpl.
    + intros; rewrite transform_id_right; reflexivity.
    + intros; destruct (A_encode _ _).
      rewrite IHxs, transform_id_left, (IHxs b).
      destruct (fold_left _ _ _).
      rewrite transform_assoc; reflexivity.
  Qed.

  Lemma IList_encode'_as_foldl :
    forall xs env,
      IList_encode' xs env =
      fold_left IList_encode'_body xs (transform_id, env).
  Proof.
    induction xs; simpl.
    + reflexivity.
    + intros; destruct (A_encode _ _).
      rewrite IHxs, transform_id_left, (IList_encode'_body_characterization xs b c).
      destruct (fold_left _ _ _); reflexivity.
  Qed.

  Definition IList_encode (l : IList) := IList_encode' (proj1_sig l).

  Fixpoint IList_decode' (s : nat) (b : bin) (env' : CacheDecode) :=
    match s with
    | O => (nil, b, env')
    | S s' => let (x1, e1) := A_decode b env' in
              let (x, b1) := x1 in
              let (x2, e2) := IList_decode' s' b1 e1 in
              let (xs, b2) := x2 in
              (x :: xs, b2, e2)
    end.

  Fixpoint DoTimes {A} n f (state: A) :=
    match n with
    | 0 => state
    | S n => DoTimes n f (f state)
    end.

  Arguments DoTimes {A} n f state : simpl nomatch.

  Definition IList_decode'_body xs_b_env' :=
    match xs_b_env' with
    | (xs, b, env') =>
      match A_decode b env' with
      | (x, b1, e1) => (x :: xs, b1, e1)
      end
    end.

  Lemma IList_decode'_body_characterization :
    forall s b0 c base,
      DoTimes s IList_decode'_body (base, b0, c) =
      match DoTimes s IList_decode'_body (nil, b0, c) with
      | (xs, b, env') => (xs ++ base, b, env')
      end.
  Proof.
    induction s; simpl.
    + reflexivity.
    + intros; destruct (A_decode _ _) as ((? & ?) & ?).
      rewrite IHs, (IHs _ _ (_ :: _)).
      destruct (DoTimes _ _ _) as ((? & ?) & ?).
      rewrite <- app_assoc, <- app_comm_cons; reflexivity.
  Qed.

  Lemma IList_decode'_as_fold :
    forall s b env',
      IList_decode' s b env' =
      match DoTimes s IList_decode'_body (nil, b, env') with
      | (xs, b, env') => (List.rev xs, b, env')
      end.
  Proof.
    induction s; simpl.
    + reflexivity.
    + intros; destruct (A_decode _ _) as ((? & ?) & ?).
      rewrite IHs, IList_decode'_body_characterization, (IList_decode'_body_characterization _ _ _ (_ :: _)).
      destruct (DoTimes _ _ _) as ((? & ?) & ?).
      rewrite !rev_app_distr; reflexivity.
  Qed.

  Definition IList_decode (b : bin) (env' : CacheDecode) : IList * bin * CacheDecode.
    refine (let x:= IList_decode' size b env' in
                       (exist _ (fst (fst x)) _,
                       snd (fst x),
                       snd x)).
    abstract (
    generalize dependent b; generalize dependent env';
    induction size; intuition eauto; intuition simpl;
    destruct (A_decode b env') as [[? ?] ?]; specialize (IHn c b0);
    destruct (IList_decode' n b0 c); destruct p; simpl; eauto).
  Defined.

  Theorem IList_encode_correct :
    encode_decode_correct cache transformer IList_predicate IList_encode IList_decode.
  Proof.
    unfold encode_decode_correct, IList_predicate, IList_encode, IList_decode.
    intros env env' xenv xenv' [l l_pf] [l' l'_pf] bin' ext ext' Eeq Ppred Penc Pdec. simpl in *.
    inversion Penc; clear Penc; inversion Pdec; clear Pdec.
    rewrite <- (sig_equivalence _ (fun xs => length xs = size) l l' l_pf l'_pf).
    generalize dependent size; generalize dependent l';
      generalize dependent env; generalize dependent env';
      generalize dependent xenv; generalize dependent xenv';
      generalize dependent bin';
      induction l; simpl in *.

    intros; destruct l'; simpl in *; try congruence; subst; simpl; inversion H0; subst;
      rewrite transform_id_left; intuition.

    intros; destruct l'; simpl in *; subst; try congruence. simpl in *.
    inversion l'_pf; clear l'_pf.

    specialize (IHl (fun x pf => Ppred x (or_intror pf))).
    specialize (Ppred a (or_introl eq_refl)).
    destruct (A_encode a env) eqn: ?.
    destruct (A_decode (transform bin' ext) env') as [[? ?] ?] eqn: ?.
    destruct (IList_encode' l c) eqn: ?. inversion H0; subst; clear H0.
    rewrite <- transform_assoc in Heqp0.
    pose proof (A_decode_pf _ Eeq Ppred Heqp Heqp0); clear Eeq Ppred Heqp Heqp0.
    destruct H as [? [? ?] ]. subst.
    destruct (IList_decode' (length l) (transform b1 ext) c0) as [[? ?] ?] eqn: ?.
    simpl in *; inversion H1; subst; clear H1.
    specialize (IHl _ c1 _ _ _ H Heqp1 _ _ eq_refl H2).
    rewrite H2. rewrite Heqp in *. simpl in *. intuition. subst. eauto.
  Qed.
End IListEncoder.

Arguments IList_encode {_ _ _ _ _} _ _ _.
