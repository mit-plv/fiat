Require Export
        Coq.Lists.List
        Coq.FSets.FMapInterface.
Require Import
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Sig.

Set Implicit Arguments.

Inductive CacheBranch :=
| Yes
| No.

Section SteppingListCacheEncoder.
  Variable A : Type.
  Variable B : Type.
  Variable bin : Type.
  Variable fuel : nat.

  Variable cache : Cache.
  Variable cacheAdd : CacheAdd cache (list A * B).
  Variable cacheGet : CacheGet cache (list A) B.
  Variable cachePeek : CachePeek cache B.

  Variable transformer : Transformer bin.

  Variable A_halt : A.
  Variable A_halt_dec : forall a, {a = A_halt} + {~ a = A_halt}.
  Variable A_predicate : A -> Prop.
  Variable A_encode : A -> CacheEncode -> bin * CacheEncode.
  Variable A_decode : bin -> CacheDecode -> A * bin * CacheDecode.
  Variable A_decode_pf : encode_decode_correct cache transformer A_predicate A_encode A_decode.

  Variable B_predicate : B -> Prop.
  Variable B_encode : B -> CacheEncode -> bin * CacheEncode.
  Variable B_decode : bin -> CacheDecode -> B * bin * CacheDecode.
  Variable B_decode_pf : encode_decode_correct cache transformer B_predicate B_encode B_decode.

  Variable C_predicate : CacheBranch -> Prop.
  Variable C_encode : CacheBranch -> CacheEncode -> bin * CacheEncode.
  Variable C_decode : bin -> CacheDecode -> CacheBranch * bin * CacheDecode.
  Variable C_decode_pf : encode_decode_correct cache transformer C_predicate C_encode C_decode.

  Definition SteppingList := { xs : list A | length xs <= fuel /\
                                             forall x, In x xs -> ~ x = A_halt }.

  Definition SteppingList_predicate (l : SteppingList) :=
    A_predicate A_halt /\
    (forall x, In x (proj1_sig l) -> A_predicate x) /\
    (forall x, B_predicate x) /\
    (forall x, C_predicate x).

  (*Fixpoint SteppingList_encode' (l : list A) (ce : CacheEncode) : bin * CacheEncode :=
    match l with
    | nil => let (b1, e1) := C_encode No ce in
             let (b2, e2) := A_encode A_halt e1 in
                 (transform b1 b2, e2)
    | cons x l' =>
      match getE ce l with
      | Some position => let (b1, e1) := C_encode Yes ce in
                         let (b2, e2) := B_encode position e1 in
                         (transform b1 b2, e2)
      | None => let (b1, e1) := C_encode No ce in
                let (b2, e2) := A_encode x e1 in
                let (b3, e3) := SteppingList_encode' l' e2 in
                    (transform (transform b1 b2) b3, addE e3 (l, peekE ce))
      end
    end.

  Definition SteppingList_encode (l : SteppingList) (ce : CacheEncode) : bin * CacheEncode :=
    SteppingList_encode' (proj1_sig l) ce.

  Require Import Coq.Arith.Compare_dec.

  Definition SteppingList_ok (f : nat) (xs : list A) : {   length xs <= f /\ forall x, In x xs -> ~ x = A_halt} +
                                                       {~ (length xs <= f /\ forall x, In x xs -> ~ x = A_halt)}.
    destruct (le_dec (length xs) f); [ | intuition ].
    remember (length xs <= f) as T; clear HeqT.
    induction xs; [ left; intuition | simpl in * ].
    destruct IHxs.
    { destruct (A_halt_dec a).
      right. intro. destruct H. specialize (H0 _ (or_introl eq_refl)). tauto.
      left. split. tauto. intros. destruct a0. specialize (H1 x). destruct H. subst. tauto. tauto. }
    { right. intro. apply n. destruct H. split. tauto. intros. apply H0. tauto. }
  Defined.

  Fixpoint SteppingList_decode' (f : nat) (b : bin) (cd : CacheDecode) : list A * bin * CacheDecode :=
    let (x1, e1) := C_decode b cd in
    let (br, b1) := x1 in
    match br with
    | Yes => let (x2, e2) := B_decode b1 e1 in
             let (ps, b2) := x2 in
             match getD cd ps with
             | Some l =>
               if SteppingList_ok f l
               then (l, b2, e2)
               else (nil, b, cd) (* bogus *)
             | None => (nil, b, cd) (* bogus *)
             end
    | No => let (x2, e2) := A_decode b1 e1 in
            let (a, b2) := x2 in
            if A_halt_dec a then
              (nil, b2, e2)
            else
              match f with
              | O => (nil, b, cd) (* bogus *)
              | S f' => let (x3, e3) := SteppingList_decode' f' b2 e2 in
                        let (l, b3) := x3 in
                        (a :: l, b3, addD e3 (a :: l, peekD cd))
              end
    end.

  Lemma SteppingList_ok_pf (f : nat) (b : bin) (cd : CacheDecode)
    : length (fst (fst (SteppingList_decode' f b cd))) <= f /\
      (forall x : A, In x (fst (fst (SteppingList_decode' f b cd))) -> x <> A_halt).
  Proof.
    generalize dependent b. generalize dependent cd.
    induction f; intros; simpl.
    { destruct (C_decode b cd) as [ [? ?] ?]. destruct c.
      destruct (B_decode b0 c0) as [ [? ?] ?]. destruct (getD cd b1).
      destruct (SteppingList_ok 0 l). simpl. tauto.
      intuition. intuition.
      destruct (A_decode b0 c0) as [ [? ?] ?]. destruct (A_halt_dec a).
      intuition. intuition. }
    { destruct (C_decode b cd) as [ [? ?] ?]. destruct c.
      destruct (B_decode b0 c0) as [ [? ?] ?]. destruct (getD cd b1).
      destruct (SteppingList_ok (S f) l).
      intuition. intuition. intuition.
      destruct (A_decode b0 c0) as [ [? ?] ?].
      specialize (IHf c b1).
      destruct (SteppingList_decode' f b1 c) as [ [? ?] ?].
      destruct (A_halt_dec a).
      intuition. simpl in *. intuition.
      subst. eauto. subst. eauto. }
  Qed.

  Definition SteppingList_decode (b : bin) (cd : CacheDecode) : SteppingList * bin * CacheDecode.
    refine (let x := SteppingList_decode' fuel b cd in
            (exist _ (fst (fst x)) _,
             snd (fst x),
             snd x)).
    apply SteppingList_ok_pf.
  Defined.

  Theorem SteppingList_encode_correct :
    encode_decode_correct cache transformer SteppingList_predicate SteppingList_encode SteppingList_decode.
  Proof.
    unfold encode_decode_correct.
    intros env env' xenv xenv' [l l_pf] [l' l'_pf] bin' ext ext' Eeq Ppred Penc Pdec.
    unfold SteppingList_predicate, SteppingList_encode, SteppingList_decode in *; simpl in *.
    inversion Pdec; subst; clear Pdec.
    rewrite <- sig_equivalence with (P:=fun xs : list A => length xs <= fuel /\ (forall x : A, In x xs -> x <> A_halt)).
    destruct Ppred as [? [? [? ?] ] ].

    generalize dependent fuel; clear fuel.
    generalize dependent env; generalize dependent env';
      generalize dependent xenv; generalize dependent bin'.
    induction l; intros; simpl in *.
    { destruct (C_encode No env) eqn: ?.
      destruct (A_encode A_halt c) eqn: ?.
      inversion Penc; subst; clear Penc. rewrite <- !transform_assoc.
      destruct (C_decode (transform b (transform b0 ext)) env') as [ [? ?] ?] eqn: ?.
      pose proof (C_decode_pf _ Eeq (H2 _) Heqp Heqp1) as [? [? ?] ]. subst.
      destruct fuel eqn: ?; simpl; rewrite !Heqp1; clear Heqp1.
      destruct (A_decode (transform b0 ext) c1) as [ [? ?] ?] eqn: ?.
      pose proof (A_decode_pf _ H3 H Heqp0 Heqp1) as [? [? ?] ].
      rewrite <- H5. destruct (A_halt_dec A_halt). intuition. congruence.
      destruct (A_decode (transform b0 ext) c1) as [ [? ?] ?] eqn: ?.
      pose proof (A_decode_pf _ H3 H Heqp0 Heqp1) as [? [? ?] ].
      rewrite <- H5. destruct (A_halt_dec A_halt). intuition. congruence. }
    { destruct fuel as [| fuel']. exfalso. intuition.
      destruct (getE env (a :: l)) eqn: ?.
      destruct (C_encode Yes env) eqn: ?.
      destruct (B_encode b c) eqn: ?.
      inversion Penc; subst; clear Penc. rewrite <- !transform_assoc.
      destruct (C_decode (transform b0 (transform b1 ext)) env') as [ [? ?] ?] eqn: ?.
      pose proof (C_decode_pf _ Eeq (H2 _) Heqp Heqp1) as [? [? ?] ]. subst.
      simpl. rewrite !Heqp1. clear Heqp1.
      destruct (B_decode (transform b1 ext) c1) as [ [? ?] ?] eqn: ?.
      pose proof (B_decode_pf _ H3 (H1 _) Heqp0 Heqp1) as [? [? ?] ]. subst.
      rewrite get_correct in Heqo; eauto. rewrite !Heqo.
      destruct (SteppingList_ok (S fuel') (a :: l)); try tauto.
      destruct (C_encode No env) eqn: ?.
      destruct (A_encode a c) eqn: ?.
      destruct (SteppingList_encode' l c0) eqn: ?.
      inversion Penc; subst; clear Penc. rewrite <- !transform_assoc.
      destruct (C_decode (transform b (transform b0 (transform b1 ext))) env') as [ [? ?] ?] eqn: ?.
      pose proof (C_decode_pf _ Eeq (H2 _) Heqp Heqp2) as [? [? ?] ]. subst.
      simpl. rewrite !Heqp2. clear Heqp2.
      destruct (A_decode (transform b0 (transform b1 ext)) c3) as [ [? ?] ?] eqn: ?.
      pose proof (A_decode_pf _ H3 (H0 a (or_introl eq_refl)) Heqp0 Heqp2) as [? [? ?] ]. subst.
      destruct (A_halt_dec a0). exfalso. subst. destruct l_pf. specialize (H6 A_halt (or_introl eq_refl)). congruence.
      assert (forall x : A, In x l -> A_predicate x) by intuition. specialize (IHl H5). clear H5.
      assert (length l <= fuel' /\ (forall x : A, In x l -> x <> A_halt)). split. apply le_S_n. intuition.
      intros. destruct l_pf. apply H7. intuition.
      assert (length (fst (fst (SteppingList_decode' fuel' (transform b1 ext) c2))) <= fuel' /\
        (forall x : A, In x (fst (fst (SteppingList_decode' fuel' (transform b1 ext) c2))) -> x <> A_halt)) by apply SteppingList_ok_pf.
      specialize (IHl _ _ _ _ H4 Heqp1 fuel'  H5 H6).
      destruct (SteppingList_decode' fuel' (transform b1 ext) c2) as [ [? ?] ?].
      simpl in IHl. simpl. intuition. subst. erewrite peek_correct. eapply add_correct. eauto. eauto. subst. eauto. }
  Qed. *)
End SteppingListCacheEncoder.

(*Arguments SteppingList_encode {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _. *)
