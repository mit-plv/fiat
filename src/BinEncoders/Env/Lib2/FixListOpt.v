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
  Variable A_encode_Spec : A -> CacheEncode -> Comp (B * CacheEncode).
  Variable A_encode_Impl : A -> CacheEncode -> B * CacheEncode.
  Variable A_decode : B -> CacheDecode -> option (A * B * CacheDecode).
  Variable A_decode_pf : encode_decode_correct_f cache transformer A_predicate A_encode_Spec A_decode.

  (* Ben: Should we do this with a FixComp instead? *)
  Fixpoint encode_list_Spec (xs : list A) (ce : CacheEncode)
    : Comp (B * CacheEncode) :=
    match xs with
    | nil => ret (transform_id, ce)
    | x :: xs' => `(b1, env1) <- A_encode_Spec x ce;
                    `(b2, env2) <- encode_list_Spec xs' env1;
                    ret (transform b1 b2, env2)
    end%comp.

  Fixpoint encode_list_Impl (xs : list A) (ce : CacheEncode)
    : B * CacheEncode :=
    match xs with
    | nil => (transform_id, ce)
    | x :: xs' =>  let (b1, env1) := A_encode_Impl x ce in
                   let (b2, env2) := encode_list_Impl xs' env1 in
                   (transform b1 b2, env2)
    end%comp.

  Fixpoint decode_list (s : nat) (b : B) (cd : CacheDecode) : option (list A * B * CacheDecode) :=
    match s with
    | O => Some (nil, b, cd)
    | S s' => `(x, b1, e1) <- A_decode b cd;
              `(xs, b2, e2) <- decode_list s' b1 e1;
              Some (x :: xs, b2, e2)
    end.

  Theorem FixList_decode_correct :
    forall sz,
      encode_decode_correct_f
        cache transformer
        (fun ls => |ls| = sz /\ forall x, In x ls -> A_predicate x)
        encode_list_Spec (decode_list sz).
  Proof.
    split.
    {
      intros env env' xenv l l' ext Eeq Ppred Penc.
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
        destruct (proj1 A_decode_pf _ _ _ _ _ (transform b0 ext) Eeq H Penc) as [ ? [? ?] ].
        setoid_rewrite <- transform_assoc; setoid_rewrite H1;
          simpl.
        destruct (IHl b0 xenv x c); intuition eauto.
        setoid_rewrite H4; simpl.
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
          destruct_ex; intuition; subst.
        eapply IHsz in Heqo0; eauto; destruct_ex; intuition; subst.
        simpl.
        eexists; eexists; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        rewrite transform_assoc; reflexivity.
        subst; eauto.
    }
  Qed.

  Definition encode_list_body := (fun (acc: B * CacheEncode) x =>
                                    let (bacc, env) := acc in
                                       let (b1, env1) := A_encode_Impl x env in
                                       (transform bacc b1, env1)).

  Lemma encode_list_body_characterization :
    forall xs base env,
      fold_left encode_list_body xs (base, env) =
      (let (b2, env2) := fold_left encode_list_body xs (transform_id, env) in
       (transform base b2, env2)).
  Proof.
    induction xs; simpl.
    + intros; rewrite transform_id_right; reflexivity.
    + intros; destruct (A_encode_Impl _ _).
      rewrite IHxs, transform_id_left, (IHxs b).
      destruct (fold_left _ _ _).
      rewrite transform_assoc; reflexivity.
  Qed.

  Lemma encode_list_as_foldl :
    forall xs env,
      encode_list_Impl xs env =
      fold_left encode_list_body xs (transform_id, env).
  Proof.
    induction xs; simpl.
    + reflexivity.
    + intros; destruct (A_encode_Impl _ _).
      rewrite IHxs, transform_id_left, (encode_list_body_characterization xs b c).
      destruct (fold_left _ _ _); reflexivity.
  Qed.
End FixList.
