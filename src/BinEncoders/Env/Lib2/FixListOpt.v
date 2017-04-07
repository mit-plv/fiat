Require Import
        Fiat.BinEncoders.Env.Common.Notations
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.ComposeOpt.
Require Export
        Coq.Lists.List.

Notation "| ls |" := (Datatypes.length ls) : binencoders_scope.

Section FixList.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {transformer : Transformer B}.

  Variable A_predicate : A -> Prop.
  Variable A_predicate_rest : A -> B -> Prop.
  Variable A_encode_Spec : A -> CacheEncode -> Comp (B * CacheEncode).
  Variable A_decode : B -> CacheDecode -> option (A * B * CacheDecode).
  Variable A_cache_inv : CacheDecode -> Prop.
  Variable A_decode_pf : encode_decode_correct_f cache transformer A_predicate A_predicate_rest A_encode_Spec A_decode A_cache_inv.

  (* Ben: Should we do this with a FixComp instead? *)
  Fixpoint encode_list_Spec (xs : list A) (ce : CacheEncode)
    : Comp (B * CacheEncode) :=
    match xs with
    | nil => ret (transform_id, ce)
    | x :: xs' => `(b1, env1) <- A_encode_Spec x ce;
                  `(b2, env2) <- encode_list_Spec xs' env1;
                  ret (transform b1 b2, env2)
    end%comp.

  Fixpoint encode_list_Impl
           (A_encode_Impl : A -> CacheEncode -> B * CacheEncode)
           (xs : list A) (ce : CacheEncode)
    : B * CacheEncode :=
    match xs with
    | nil => (transform_id, ce)
    | x :: xs' =>  let (b1, env1) := A_encode_Impl x ce in
                   let (b2, env2) := encode_list_Impl A_encode_Impl xs' env1 in
                   (transform b1 b2, env2)
    end%comp.

  Fixpoint decode_list (s : nat) (b : B) (cd : CacheDecode) : option (list A * B * CacheDecode) :=
    match s with
    | O => Some (nil, b, cd)
    | S s' => `(x, b1, e1) <- A_decode b cd;
              `(xs, b2, e2) <- decode_list s' b1 e1;
              Some (x :: xs, b2, e2)
    end.

  Fixpoint FixList_predicate_rest
           (As : list A)
           (b : B)
    : Prop :=
    match As with
    | nil => True
    | cons a As' =>
      (forall b' ce ce',
          computes_to (encode_list_Spec As' ce) (b', ce')
          -> A_predicate_rest a (transform b' b))
      /\ FixList_predicate_rest As' b
    end.

  Theorem FixList_decode_correct
    :
    forall sz ,
      encode_decode_correct_f
        cache transformer
        (fun ls => |ls| = sz /\ forall x, In x ls -> A_predicate x)
        FixList_predicate_rest
        encode_list_Spec (decode_list sz) A_cache_inv.
  Proof.
    split.
    {
      intros env env' xenv l l' ext ? Eeq Ppred Ppred_rest Penc.
      intuition; subst.
      revert H0.
      generalize dependent env. generalize dependent env'.
      generalize dependent xenv.
      generalize dependent l'. induction l.
      { intros.
        simpl in *; intuition; computes_to_inv;
          injections; simpl.
        rewrite transform_id_left; eexists; eauto. }
      { intros; simpl in *.
        assert (A_predicate a) by eauto.
        unfold Bind2 in Penc; computes_to_inv; subst.
        destruct v; destruct v0; simpl in *.
        injections.
        destruct (fun H' => proj1 A_decode_pf _ _ _ _ _ (transform b0 ext) env_OK Eeq H H' Penc) as [ ? [? [? xenv_OK] ] ].
        intuition; destruct_ex.
        eapply H1; eauto.
        setoid_rewrite <- transform_assoc; setoid_rewrite H1;
          simpl.
        destruct (IHl (proj2 Ppred_rest) b0 xenv x xenv_OK c); intuition eauto.
        setoid_rewrite H6; simpl.
        eexists; intuition.
      }
    }
    { induction sz; simpl; intros.
      - injections; simpl; repeat eexists; intuition eauto.
        symmetry; apply transform_id_left.
      - destruct (A_decode bin env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_list sz b c) as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate; injections.
        eapply (proj2 A_decode_pf) in Heqo; eauto;
          destruct Heqo; destruct_ex; intuition; subst;
            eapply IHsz in Heqo0; eauto; destruct Heqo0;
              destruct_ex; intuition; subst.
        simpl.
        eexists; eexists; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        rewrite transform_assoc; reflexivity.
        subst; eauto.
    }
  Qed.


  Definition encode_list_body
               (A_encode_Impl : A -> CacheEncode -> B * CacheEncode)
:= (fun (acc: B * CacheEncode) x =>
                                    let (bacc, env) := acc in
                                       let (b1, env1) := A_encode_Impl x env in
                                       (transform bacc b1, env1)).

  Lemma encode_list_body_characterization A_encode_Impl :
    forall xs base env,
      fold_left (encode_list_body A_encode_Impl) xs (base, env) =
      (let (b2, env2) := fold_left (encode_list_body A_encode_Impl) xs (transform_id, env) in
       (transform base b2, env2)).
  Proof.
    induction xs; simpl.
    + intros; rewrite transform_id_right; reflexivity.
    + intros; destruct (A_encode_Impl _ _).
      rewrite IHxs, transform_id_left, (IHxs b).
      destruct (fold_left _ _ _).
      rewrite transform_assoc; reflexivity.
  Qed.

  Lemma encode_list_as_foldl A_encode_Impl :
    forall xs env,
      encode_list_Impl A_encode_Impl xs env =
      fold_left (encode_list_body A_encode_Impl) xs (transform_id, env).
  Proof.
    induction xs; simpl.
    + reflexivity.
    + intros; destruct (A_encode_Impl _ _).
      rewrite IHxs, transform_id_left, (encode_list_body_characterization A_encode_Impl xs b c).
      destruct (fold_left _ _ _); reflexivity.
  Qed.

  Lemma measure_encode_length_Spec n :
    (forall (a : A) b ctx ctx',
        computes_to (A_encode_Spec a ctx) (b, ctx')
        -> bin_measure b = n)
    -> forall l b ctx ctx',
      computes_to (encode_list_Spec l ctx) (b, ctx') ->
      bin_measure b = n * (length l).
  Proof.
    induction l; simpl; intros.
    - computes_to_inv; injections.
      pose proof (transform_measure transform_id transform_id) as H';
        rewrite transform_id_left in H'.
      simpl bin_measure in H'; simpl transform_id in H'; omega.
    - unfold Bind2 in *; computes_to_inv; injections.
      destruct v; destruct v0; simpl in *.
      rewrite transform_measure.
      apply H in H0; rewrite H0.
      apply IHl in H0'; rewrite H0'.
      rewrite Mult.mult_succ_r.
      auto with arith.
  Qed.

End FixList.

Lemma FixedList_predicate_rest_True {A B}
      {cache : Cache}
      {transformer : Transformer B}
      (A_encode_Spec : A -> CacheEncode -> Comp (B * CacheEncode))
  : forall (l : list A) (b : B),
    FixList_predicate_rest (fun a b => True) A_encode_Spec l b.
Proof.
  induction l; simpl; eauto.
Qed.
