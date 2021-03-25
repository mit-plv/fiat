Require Import
        Coq.ZArith.ZArith
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Formats.Base.FixFormat.

Require Export
        Coq.Lists.List.

Notation "| ls |" := (Datatypes.length ls) : format_scope.

Section FixList.
  Context {A : Type}.
  Context {T : Type}.
  Context {cache : Cache}.
  Context {monoid : Monoid T}.

  Variable A_predicate : A -> Prop.
  Variable format_A : A -> CacheFormat -> Comp (T * CacheFormat).
  Variable A_decode : T -> CacheDecode -> option (A * T * CacheDecode).
  Variable A_cache_inv : CacheDecode -> Prop.
  Variable A_decode_pf : CorrectDecoder monoid A_predicate A_predicate
                                        eq format_A A_decode A_cache_inv
                                        format_A.

  Open Scope vector_scope.

  (* Could do this with a FixComp instead? *)
  Fixpoint format_list (xs : list A) (ce : CacheFormat)
    : Comp (T * CacheFormat) :=
    match xs with
    | nil => ret (mempty, ce)
    | x :: xs' => `(b1, env1) <- format_A x ce;
                  `(b2, env2) <- format_list xs' env1;
                  ret (mappend b1 b2, env2)
    end%comp.

  Fixpoint encode_list
           (encode_A : A -> CacheFormat -> T * CacheFormat)
           (xs : list A) (ce : CacheFormat)
    : T * CacheFormat :=
    match xs with
    | nil => (mempty, ce)
    | x :: xs' =>  let (b1, env1) := encode_A x ce in
                   let (b2, env2) := encode_list encode_A xs' env1 in
                   (mappend b1 b2, env2)
    end%comp.

  Fixpoint decode_list (s : nat) (b : T) (cd : CacheDecode) : option (list A * T * CacheDecode) :=
    match s with
    | O => Some (nil, b, cd)
    | S s' => `(x, b1, e1) <- A_decode b cd;
              `(xs, b2, e2) <- decode_list s' b1 e1;
              Some (x :: xs, b2, e2)
    end.

  Theorem FixList_decode_correct
    :
    forall sz ,
      CorrectDecoder
         monoid
         (fun ls => |ls| = sz /\ forall x, In x ls -> A_predicate x)
         (fun ls => |ls| = sz /\ forall x, In x ls -> A_predicate x)
         eq
         format_list (decode_list sz) A_cache_inv
         format_list.
  Proof.
    split.
    {
      intros env env' xenv l l' ext ? Eeq Ppred Penc.
      intuition; subst.
      revert H0.
      generalize dependent env. generalize dependent env'.
      generalize dependent xenv.
      generalize dependent l'. induction l.
      { intros.
        simpl in *; intuition; computes_to_inv;
          injections; simpl.
        rewrite mempty_left; eexists _, _; intuition eauto.
        simpl; computes_to_econstructor.
      }
      { intros; simpl in *.
        assert (A_predicate a) by eauto.
        unfold Bind2 in Penc; computes_to_inv; subst.
        destruct v; destruct v0; simpl in *.
        injections.
        destruct (proj1 A_decode_pf _ _ _ _ _ (mappend t0 ext) env_OK Eeq H Penc) as [ ? [? [? xenv_OK] ] ].
        intuition; destruct_ex.
        setoid_rewrite <- mappend_assoc; setoid_rewrite H1;
          simpl; subst.
        destruct (IHl t0 xenv _ H6 c) as [? [? ?] ];
          intuition eauto; subst.
        setoid_rewrite H5; simpl.
        eexists _, _; intuition.
        simpl; unfold Bind2; eauto.
      }
    }
    { induction sz; simpl; intros.
      - injections; simpl; repeat eexists; simpl; intuition eauto.
        symmetry; apply mempty_left.
      - destruct (A_decode t env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_list sz t0 c) as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate; injections.
        eapply (proj2 A_decode_pf) in Heqo; eauto;
          destruct Heqo; destruct_ex; intuition; subst;
            eapply IHsz in Heqo0; eauto; destruct Heqo0;
              destruct_ex; intuition; subst.
        simpl.
        eexists _, _; simpl; unfold id; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        simpl. rewrite mappend_assoc; reflexivity.
        subst; eauto.
    }
  Qed.

  Definition format_list_body
               (A_format_Impl : A -> CacheFormat -> T * CacheFormat)
:= (fun (acc: T * CacheFormat) x =>
                                    let (bacc, env) := acc in
                                       let (b1, env1) := A_format_Impl x env in
                                       (mappend bacc b1, env1)).

  Import Fiat.Computation.FixComp.LeastFixedPointFun.

  Definition format_list' : FormatM (store := cache) (list A) T :=
    LeastFixedPoint
      (fDom := [list A; CacheFormat])
      (fun format_list' xs =>
         match xs with
         | nil => fun env => ret (mempty, env)
         | x :: xs' =>
           format_A x ThenC format_list' xs'
         end).

  Lemma format_list_body_characterization A_format_Impl :
    forall xs base env,
      fold_left (format_list_body A_format_Impl) xs (base, env) =
      (let (b2, env2) := fold_left (format_list_body A_format_Impl) xs (mempty, env) in
       (mappend base b2, env2)).
  Proof.
    induction xs; simpl.
    + intros; rewrite mempty_right; reflexivity.
    + intros; destruct (A_format_Impl _ _).
      rewrite IHxs, mempty_left, (IHxs t).
      destruct (fold_left _ _ _).
      rewrite mappend_assoc; reflexivity.
  Qed.

  Lemma format_list_as_foldl encode_A :
    forall xs env,
      encode_list encode_A xs env =
      fold_left (format_list_body encode_A) xs (mempty, env).
  Proof.
    induction xs; simpl.
    + reflexivity.
    + intros; destruct (encode_A _ _).
      rewrite IHxs, mempty_left, (format_list_body_characterization encode_A xs t c).
      destruct (fold_left _ _ _); reflexivity.
  Qed.

  Lemma measure_format_length_Spec n :
    (forall (a : A) b ctx ctx',
        computes_to (format_A a ctx) (b, ctx')
        -> bin_measure b = n)
    -> forall l b ctx ctx',
      computes_to (format_list l ctx) (b, ctx') ->
      bin_measure b = n * (length l).
  Proof.
    induction l; simpl; intros.
    - computes_to_inv; injections.
      pose proof (mappend_measure mempty mempty) as H';
        rewrite mempty_left in H'.
      simpl bin_measure in H'; simpl mempty in H'; omega.
    - unfold Bind2 in *; computes_to_inv; injections.
      destruct v; destruct v0; simpl in *.
      rewrite mappend_measure.
      apply H in H0; rewrite H0.
      apply IHl in H0'; rewrite H0'.
      rewrite Mult.mult_succ_r.
      auto with arith.
  Qed.

End FixList.
