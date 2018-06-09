Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt.

Require Export
        Coq.Lists.List.

Notation "| ls |" := (Datatypes.length ls) (at level 200).

Section FixList.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {monoid : Monoid B}.

  Variable A_predicate : A -> Prop.
  Variable A_format : A -> CacheFormat -> B * CacheFormat.
  Variable A_decode : B -> CacheDecode -> A * B * CacheDecode.
  Variable A_decode_pf : format_decode_correct monoid A_predicate A_format A_decode.

  Fixpoint format_list (xs : list A) (ce : CacheFormat) : B * CacheFormat :=
    match xs with
    | nil => (mempty, ce)
    | x :: xs' => let (b1, env1) := A_format x ce in
                  let (b2, env2) := format_list xs' env1 in
                      (mappend b1 b2, env2)
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
      format_decode_correct
        monoid
        (fun ls => |ls| = sz /\ forall x, In x ls -> A_predicate x)
        format_list (decode_list sz).
  Proof.
    unfold format_decode_correct.
    intros sz env env' xenv xenv' l l' bin' ext ext' Eeq Ppred Penc Pdec.
    generalize dependent sz. generalize dependent env. generalize dependent env'.
    generalize dependent xenv. generalize dependent xenv'. generalize dependent bin'.
    generalize dependent l'. generalize dependent ext'. induction l.
    { intros.
      inversion Penc; subst; clear Penc.
      rewrite mempty_left in Pdec. simpl in *. destruct Ppred.
      subst. simpl in *. inversion Pdec. subst. intuition eauto. }
    { intros.
      destruct sz. inversion Ppred. inversion H.
      simpl in *. destruct Ppred.
      assert (A_predicate a) by eauto.
      destruct (A_format a env) eqn: ?.
      destruct (format_list l c) eqn: ?.
      inversion H; subst; clear H.
      inversion Penc; subst; clear Penc.
      rewrite <- mappend_assoc in Pdec.
      destruct (A_decode (mappend b (mappend b0 ext)) env') as [[? ?] ?] eqn: ?.
      destruct (A_decode_pf _ _ _ _ _ _ _ _ _ Eeq H1 Heqp Heqp1) as [? [? ?]]. subst.
      destruct (decode_list (|l |) (mappend b0 ext) c0) as [[? ?] ?] eqn: ?.
      specialize (IHl _ _ _ _ _ _ _ H Heqp0 _ (conj eq_refl (fun x h => H0 x (or_intror h))) Heqp2).
      inversion Pdec; subst; clear Pdec.
      intuition eauto. subst. eauto. }
  Qed.

  Definition format_list_body := (fun (acc: B * CacheFormat) x =>
                                       let (bacc, env) := acc in
                                       let (b1, env1) := A_format x env in
                                       (mappend bacc b1, env1)).

  Lemma format_list_body_characterization :
    forall xs base env,
      fold_left format_list_body xs (base, env) =
      (let (b2, env2) := fold_left format_list_body xs (mempty, env) in
       (mappend base b2, env2)).
  Proof.
    induction xs; simpl.
    + intros; rewrite mempty_right; reflexivity.
    + intros; destruct (A_format _ _).
      rewrite IHxs, mempty_left, (IHxs b).
      destruct (fold_left _ _ _).
      rewrite mappend_assoc; reflexivity.
  Qed.

  Lemma format_list_as_foldl :
    forall xs env,
      format_list xs env =
      fold_left format_list_body xs (mempty, env).
  Proof.
    induction xs; simpl.
    + reflexivity.
    + intros; destruct (A_format _ _).
      rewrite IHxs, mempty_left, (format_list_body_characterization xs b c).
      destruct (fold_left _ _ _); reflexivity.
  Qed.

End FixList.
