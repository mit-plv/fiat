Require Import
        Fiat.Narcissus.Common.Specs
        Coq.Arith.Peano_dec
        Coq.Logic.Eqdep_dec.

Import Vectors.VectorDef.VectorNotations.
Require Export
        Coq.Lists.List.

Section Vector.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {monoid : Monoid B}.

  Variable A_predicate : A -> Prop.
  Variable format_A : A -> CacheFormat -> Comp (B * CacheFormat).
  Variable A_decode : B -> CacheDecode -> option (A * B * CacheDecode).
  Variable A_cache_inv : CacheDecode -> Prop.
  Variable A_decode_pf
    : CorrectDecoder monoid
                     A_predicate
                     A_predicate
                     eq
                     format_A A_decode A_cache_inv
                     format_A.

  Fixpoint format_Vector {n} (xs : Vector.t A n) (ce : CacheFormat)
    : Comp (B * CacheFormat) :=
    match xs with
    | Vector.nil => ret (mempty, ce)
    | Vector.cons x _ xs' => `(b1, env1) <- format_A x ce;
                    `(b2, env2) <- format_Vector xs' env1;
                    ret (mappend b1 b2, env2)
    end%comp.

  Fixpoint format_Vector_Impl
           (A_format_Impl : A -> CacheFormat -> B * CacheFormat)
           {n} (xs : Vector.t A n) (ce : CacheFormat)
    : B * CacheFormat :=
    match xs with
    | Vector.nil => (mempty, ce)
    | Vector.cons x _ xs' =>
      let (b1, env1) := A_format_Impl x ce in
      let (b2, env2) := format_Vector_Impl A_format_Impl xs' env1 in
      (mappend b1 b2, env2)
    end%comp.

  Fixpoint decode_Vector (n : nat) (b : B) (cd : CacheDecode)
    : option (Vector.t A n * B * CacheDecode) :=
    match n with
    | O => Some (Vector.nil _, b, cd)
    | S s' => `(x, b1, e1) <- A_decode b cd;
              `(xs, b2, e2) <- decode_Vector s' b1 e1;
              Some (Vector.cons _ x _ xs, b2, e2)
    end.

  Theorem Vector_decode_correct
    :
    forall sz,
      CorrectDecoder
        monoid
        (fun ls => forall x, Vector.In x ls -> A_predicate x)
        (fun ls => forall x, Vector.In x ls -> A_predicate x)
        eq
        format_Vector (decode_Vector sz) A_cache_inv format_Vector.
  Proof.
    split.
    {
      intros env env' xenv l l' ext env_OK Eeq Ppred Penc.
      generalize dependent env. generalize dependent env'.
      generalize dependent xenv.
      generalize dependent l'. induction l.
      { intros.
        simpl in *.
        simpl in *; intuition; computes_to_inv;
          injections; simpl; rewrite mempty_left; eauto.
        eexists _, _; intuition eauto.
        computes_to_econstructor.
      }
      { intros; simpl in *.
        assert (A_predicate h) by (eapply Ppred; econstructor).
        unfold Bind2 in Penc; computes_to_inv; subst.
        destruct v; destruct v0; simpl in *.
        injections.
        destruct (proj1 A_decode_pf _ _ _ _ _ (mappend b0 ext) env_OK Eeq H Penc) as [ ? [? [? xenv_OK] ] ].
        setoid_rewrite <- mappend_assoc; setoid_rewrite H0;
          simpl.
        split_and; subst.
        destruct (IHl (fun x H => Ppred x (Vector.In_cons_tl _ _ _ H)) b0 xenv _  H5 c) as [? [? ?] ];
          intuition eauto.
        setoid_rewrite H4; simpl.
        eexists _, _; intuition; try congruence.
        simpl; unfold Bind2; eauto.
      }
    }
    { induction sz; simpl; intros.
      - injections; simpl; split; eauto; repeat eexists;
          simpl; intuition eauto.
        symmetry; apply mempty_left.
        inversion H1.
      - destruct (A_decode t env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_Vector sz b c) as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate; injections.
        eapply (proj2 A_decode_pf) in Heqo; eauto;
          destruct Heqo as [? [? ?] ]; destruct_ex; intuition; subst;
            eapply IHsz in Heqo0; eauto; destruct Heqo0 as [? [? ?] ];
              destruct_ex; intuition; subst.
        simpl.
        eexists _, _; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        rewrite mappend_assoc; reflexivity.
        inversion H5; subst; eauto.
        apply inj_pair2_eq_dec in H13; subst; eauto using eq_nat_dec.
    }
  Qed.

End Vector.
