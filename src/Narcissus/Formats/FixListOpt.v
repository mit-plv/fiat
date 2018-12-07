Require Import
        Coq.omega.Omega
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.BaseFormats.
Require Export
        Coq.Lists.List.

Notation "| ls |" := (Datatypes.length ls) : format_scope.

Section FixList.
  Context {A : Type}.
  Context {T : Type}.
  Context {cache : Cache}.
  Context {monoid : Monoid T}.

  Variable A_predicate : A -> Prop.
  Variable A_predicate_rest : A -> T -> Prop.
  Variable format_A : A -> CacheFormat -> Comp (T * CacheFormat).
  Variable A_decode : T -> CacheDecode -> option (A * T * CacheDecode).
  Variable A_cache_inv : CacheDecode -> Prop.
  Variable A_decode_pf : CorrectDecoder monoid A_predicate A_predicate_rest format_A A_decode A_cache_inv.

  Open Scope vector_scope.

  (* Definition format_list'
    : FormatM (list A) T :=
    Fix_Format
      (fun rec : FormatM (list A) T =>
         Union_Format [(fun (_ : unit) s => s = nil) <$> StrictTerminal_Format;
                         (fun as' s => s = cons (fst as') (snd as')) <$> Projection_Format fst format_A
                                                                     ++ Projection_Format snd rec]%format).

  Fixpoint FixList_predicate_rest
           (As : list A)
           (b : T)
    : Prop :=
    match As with
    | nil => True
    | cons a As' =>
      (forall b' ce ce',
          computes_to (format_list' As' ce) (b', ce')
          -> A_predicate_rest a (mappend b' b))
      /\ FixList_predicate_rest As' b
    end.

  Theorem FixList_decode_correct sz
    : {decode_list : _ &
                     CorrectDecoder_simpl
                       (Restrict_Format (fun ls => |ls| = sz /\ forall x, In x ls -> A_predicate x)
                                        format_list')
                       (decode_list sz)}.
  Proof.
  Abort. *)

  (* Ten: Should we do this with a FixComp instead? *)
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

  Fixpoint FixList_predicate_rest
           (As : list A)
           (b : T)
    : Prop :=
    match As with
    | nil => True
    | cons a As' =>
      (forall b' ce ce',
          computes_to (format_list As' ce) (b', ce')
          -> A_predicate_rest a (mappend b' b))
      /\ FixList_predicate_rest As' b
    end.

  Theorem FixList_decode_correct'
    :
    forall sz ,
      CorrectDecoder
         monoid
        (fun ls => |ls| = sz /\ forall x, In x ls -> A_predicate x)
        FixList_predicate_rest
        format_list (decode_list sz) A_cache_inv.
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
        rewrite mempty_left; eexists; eauto. }
      { intros; simpl in *.
        assert (A_predicate a) by eauto.
        unfold Bind2 in Penc; computes_to_inv; subst.
        destruct v; destruct v0; simpl in *.
        injections.
        destruct (fun H' => proj1 A_decode_pf _ _ _ _ _ (mappend t0 ext) env_OK Eeq H H' Penc) as [ ? [? [? xenv_OK] ] ].
        intuition; destruct_ex.
        eapply H1; eauto.
        setoid_rewrite <- mappend_assoc; setoid_rewrite H1;
          simpl.
        destruct (IHl (proj2 Ppred_rest) t0 xenv x xenv_OK c); intuition eauto.
        setoid_rewrite H6; simpl.
        eexists; intuition.
      }
    }
    { induction sz; simpl; intros.
      - injections; simpl; repeat eexists; intuition eauto.
        symmetry; apply mempty_left.
      - destruct (A_decode bin env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_list sz t c) as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate; injections.
        eapply (proj2 A_decode_pf) in Heqo; eauto;
          destruct Heqo; destruct_ex; intuition; subst;
            eapply IHsz in Heqo0; eauto; destruct Heqo0;
              destruct_ex; intuition; subst.
        simpl.
        eexists; eexists; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        rewrite mappend_assoc; reflexivity.
        subst; eauto.
    }
  Qed.

  Theorem FixList_decode_correct
          (A_decode_pf' : CorrectDecoder monoid A_predicate (fun _ _ => True) format_A A_decode A_cache_inv)
    :
    forall sz ,
      CorrectDecoder
         monoid
         (fun ls => |ls| = sz /\ forall x, In x ls -> A_predicate x)
         (fun _ _ => True)
        format_list (decode_list sz) A_cache_inv.
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
        rewrite mempty_left; eexists; eauto. }
      { intros; simpl in *.
        assert (A_predicate a) by eauto.
        unfold Bind2 in Penc; computes_to_inv; subst.
        destruct v; destruct v0; simpl in *.
        injections.
        destruct (fun H' => proj1 A_decode_pf' _ _ _ _ _ (mappend t0 ext) env_OK Eeq H H' Penc) as [ ? [? [? xenv_OK] ] ].
        intuition; destruct_ex.

        setoid_rewrite <- mappend_assoc; setoid_rewrite H1;
          simpl.
        destruct (IHl t0 xenv x xenv_OK c); intuition eauto.
        setoid_rewrite H4; simpl.
        eexists; intuition.
      }
    }
    { induction sz; simpl; intros.
      - injections; simpl; repeat eexists; intuition eauto.
        symmetry; apply mempty_left.
      - destruct (A_decode bin env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_list sz t c) as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate; injections.
        eapply (proj2 A_decode_pf') in Heqo; eauto;
          destruct Heqo; destruct_ex; intuition; subst;
            eapply IHsz in Heqo0; eauto; destruct Heqo0;
              destruct_ex; intuition; subst.
        simpl.
        eexists; eexists; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        rewrite mappend_assoc; reflexivity.
        subst; eauto.
    }
  Qed.

  Definition format_list_body
               (A_format_Impl : A -> CacheFormat -> T * CacheFormat)
:= (fun (acc: T * CacheFormat) x =>
                                    let (bacc, env) := acc in
                                       let (b1, env1) := A_format_Impl x env in
                                       (mappend bacc b1, env1)).

  Require Import Fiat.Narcissus.Formats.Base.FixFormat.
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

Lemma FixedList_predicate_rest_True {A T}
      {cache : Cache}
      {monoid : Monoid T}
      (format_A : A -> CacheFormat -> Comp (T * CacheFormat))
  : forall (l : list A) (b : T),
    FixList_predicate_rest (fun a b => True) format_A l b.
Proof.
  induction l; simpl; eauto.
Qed.
