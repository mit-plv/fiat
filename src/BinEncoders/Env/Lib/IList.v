Require Export
        Coq.Lists.List.
Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Sig.

Set Implicit Arguments.

Section IListEncoder.
  Variable size : nat.
  Variable A : Type.
  Variable cache : Cache.
  Variable transformer : Transformer.
  Variable A_predicate : A -> Prop.
  Variable A_encode : A -> CacheEncode -> bin * CacheEncode.
  Variable A_decoder : decoder cache transformer A_predicate A_encode.

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

  Definition IList_encode (l : IList) := IList_encode' (proj1_sig l).

  Fixpoint IList_decode' (s : nat) (b : bin) (env' : CacheDecode) :=
    match s with
    | O => (nil, b, env')
    | S s' => let (x1, e1) := decode b env' in
              let (x, b1) := x1 in
              let (x2, e2) := IList_decode' s' b1 e1 in
              let (xs, b2) := x2 in
              (x :: xs, b2, e2)
    end.

  Definition IList_decode (b : bin) (env' : CacheDecode) : IList * bin * CacheDecode.
    refine (let x:= IList_decode' size b env' in
                       (exist _ (fst (fst x)) _,
                       snd (fst x),
                       snd x)).
    abstract (
    generalize dependent b; generalize dependent env';
    induction size; intuition eauto; intuition simpl;
    destruct (decode b env') as [[? ?] ?]; specialize (IHn c b0);
    destruct (IList_decode' n b0 c); destruct p; simpl; eauto).
  Defined.

  Theorem IList_encode_correct :
    encode_decode_correct cache transformer IList_predicate IList_encode IList_decode.
  Proof.
    unfold encode_decode_correct, IList_predicate, IList_encode, IList_decode.
    intros env env' xenv xenv' [l l_pf] [l' l'_pf] bin ext ext' Eeq Ppred Penc Pdec. simpl in *.
    inversion Penc; clear Penc; inversion Pdec; clear Pdec.
    rewrite <- (sig_equivalence _ (fun xs => length xs = size) l l' l_pf l'_pf).
    generalize dependent size; generalize dependent l';
      generalize dependent env; generalize dependent env';
      generalize dependent xenv; generalize dependent xenv';
      generalize dependent bin;
      induction l; simpl in *.

    intros; destruct l'; simpl in *; try congruence; subst; simpl; inversion H0; subst;
      rewrite transform_id_left; intuition.

    intros; destruct l'; simpl in *; subst; try congruence. simpl in *.
    inversion l'_pf; clear l'_pf.

    specialize (IHl (fun x pf => Ppred x (or_intror pf))).
    specialize (Ppred a (or_introl eq_refl)).
    destruct (A_encode a env) eqn: ?.
    destruct (decode (transform bin ext) env') as [[? ?] ?] eqn: ?.
    destruct (IList_encode' l c) eqn: ?. inversion H0; subst; clear H0.
    rewrite <- transform_assoc in Heqp0.
    pose proof (decode_correct (decoder:=A_decoder) env env' _ _ Eeq Ppred Heqp Heqp0); clear Eeq Ppred Heqp Heqp0.
    destruct H as [? [? ?]]. subst.
    destruct (IList_decode' (length l) (transform b1 ext) c0) as [[? ?] ?] eqn: ?.
    simpl in *; inversion H1; subst; clear H1.
    specialize (IHl _ c1 _ _ _ H Heqp1 _ _ eq_refl H2).
    rewrite H2. rewrite Heqp in *. simpl in *. intuition. subst. eauto.
  Qed.
End IListEncoder.

Global Instance IList_decoder A size cache transformer
       (A_predicate : A -> Prop)
       (A_encode : A -> CacheEncode -> bin * CacheEncode)
       (A_decoder : decoder cache transformer A_predicate A_encode)
  : decoder cache transformer
            (IList_predicate A_predicate) (IList_encode cache transformer A_encode) :=
  { decode := @IList_decode size _  _ _ _ _ _;
    decode_correct := @IList_encode_correct _ _ _ _ _ _ _ }.
