Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Coq.Arith.Peano_dec
        Coq.Logic.Eqdep_dec.

Import Vectors.VectorDef.VectorNotations.
Require Export
        Coq.Lists.List.

Section Vector.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {transformer : Transformer B}.

  Variable A_predicate : A -> Prop.
  Variable A_predicate_rest : A -> B -> Prop.
  Variable A_encode_Spec : A -> CacheEncode -> Comp (B * CacheEncode).
  Variable A_decode : B -> CacheDecode -> option (A * B * CacheDecode).
  Variable A_cache_inv : CacheDecode -> Prop.
  Variable A_decode_pf
    : encode_decode_correct_f cache transformer A_predicate
                              A_predicate_rest
                              A_encode_Spec A_decode A_cache_inv.

  Fixpoint encode_Vector_Spec {n} (xs : Vector.t A n) (ce : CacheEncode)
    : Comp (B * CacheEncode) :=
    match xs with
    | Vector.nil => ret (transform_id, ce)
    | Vector.cons x _ xs' => `(b1, env1) <- A_encode_Spec x ce;
                    `(b2, env2) <- encode_Vector_Spec xs' env1;
                    ret (transform b1 b2, env2)
    end%comp.

  Fixpoint encode_Vector_Impl
           (A_encode_Impl : A -> CacheEncode -> B * CacheEncode)
           {n} (xs : Vector.t A n) (ce : CacheEncode)
    : B * CacheEncode :=
    match xs with
    | Vector.nil => (transform_id, ce)
    | Vector.cons x _ xs' =>
      let (b1, env1) := A_encode_Impl x ce in
      let (b2, env2) := encode_Vector_Impl A_encode_Impl xs' env1 in
      (transform b1 b2, env2)
    end%comp.

  Fixpoint decode_Vector (n : nat) (b : B) (cd : CacheDecode)
    : option (Vector.t A n * B * CacheDecode) :=
    match n with
    | O => Some (Vector.nil _, b, cd)
    | S s' => `(x, b1, e1) <- A_decode b cd;
              `(xs, b2, e2) <- decode_Vector s' b1 e1;
              Some (Vector.cons _ x _ xs, b2, e2)
    end.

(*  Lemma Vector_encode_preserves_rest_predicate
    : forall (sz : nat)
             (l : Vector.t A sz)
             (ext : B)
             (env xenv : CacheEncode) (l' : B) a a',
      encode_Vector_Spec l env ↝ (l', xenv) ->
      (forall x : A, Vector.In x l -> A_predicate x) ->
      A_predicate_rest a ext ->
      A_predicate_rest a' (transform l' ext).
  Proof.
    induction l.
    - simpl in *; intuition; computes_to_inv;
        injections; simpl; rewrite transform_id_left; eauto.
    - intros; simpl in *.
      unfold Bind2 in H; computes_to_inv; subst.
      destruct v; destruct v0; simpl in *.
      injections.
      rewrite <- transform_assoc.
      eapply A_predicate_rest_inv; eauto.
      eapply H0; econstructor.
      eapply (IHl _ _ _ _ _ H' (fun x H'' => H0 x (Vector.In_cons_tl _ _ _ H''))); intuition eauto.
  Qed. *)

  Fixpoint Vector_predicate_rest
           n
           (As : Vector.t A n)
           (b : B)
    : Prop :=
    match As with
    | Vector.nil => True
    | Vector.cons a _ As' =>
      (forall b' ce ce',
          computes_to (encode_Vector_Spec As' ce) (b', ce')
          -> A_predicate_rest a (transform b' b))
      /\ Vector_predicate_rest _ As' b
    end.

  Theorem Vector_decode_correct
    :
    forall sz,
      encode_decode_correct_f
        cache transformer
        (fun ls => forall x, Vector.In x ls -> A_predicate x)
        (Vector_predicate_rest sz)
        encode_Vector_Spec (decode_Vector sz) A_cache_inv.
  Proof.
    split.
    {
      intros env env' xenv l l' ext env_OK Eeq Ppred Ppred_rest Penc.
      generalize dependent env. generalize dependent env'.
      generalize dependent xenv.
      generalize dependent l'. induction l.
      { intros.
        simpl in *; intuition; computes_to_inv;
          injections; simpl; rewrite transform_id_left; eauto.
      }
      { intros; simpl in *.
        assert (A_predicate h) by (eapply Ppred; econstructor).
        unfold Bind2 in Penc; computes_to_inv; subst.
        destruct v; destruct v0; simpl in *.
        injections.
        destruct (fun H' => proj1 A_decode_pf _ _ _ _ _ (transform b0 ext) env_OK Eeq H H' Penc) as [ ? [? [? xenv_OK] ] ].
        intuition; destruct_ex.
        eapply H0; eauto.
        setoid_rewrite <- transform_assoc; setoid_rewrite H0;
          simpl.
        destruct (fun H' => IHl (fun x H => Ppred x (Vector.In_cons_tl _ _ _ H)) H' b0 xenv x xenv_OK c); intuition eauto.
        setoid_rewrite H5; simpl.
        eexists; intuition.
      }
    }
    { induction sz; simpl; intros.
      - injections; simpl; repeat eexists; intuition eauto.
        symmetry; apply transform_id_left.
        inversion H1.
      - destruct (A_decode bin env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_Vector sz b c) as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate; injections.
        eapply (proj2 A_decode_pf) in Heqo; eauto;
          destruct Heqo as [? [? ?] ]; destruct_ex; intuition; subst;
            eapply IHsz in Heqo0; eauto; destruct Heqo0 as [? [? ?] ];
              destruct_ex; intuition; subst.
        simpl.
        eexists; eexists; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        rewrite transform_assoc; reflexivity.
        inversion H5; subst; eauto.
        apply inj_pair2_eq_dec in H13; subst; eauto using eq_nat_dec.
    }
  Qed.

End Vector.

Lemma Vector_predicate_rest_True {A B}
      {cache : Cache}
      {transformer : Transformer B}
      (A_encode_Spec : A -> CacheEncode -> Comp (B * CacheEncode))
  : forall {n} (v : Vector.t A n) (b : B),
    Vector_predicate_rest (fun a b => True) A_encode_Spec n v b.
Proof.
  induction v; simpl; eauto.
Qed.
