Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Stores.EmptyStore.

Require Import Fiat.Computation.FixComp.
Import Fiat.Computation.FixComp.LeastFixedPointFun.

Lemma fix_format_P
      {A B}
      (monoid : Monoid B)
      {cache : Cache}
      (format_body : funType [A * B; CacheFormat]%type (B * CacheFormat) ->
                     funType [A * B; CacheFormat]%type (B * CacheFormat))
      (Inv Inv' : funType [A * B; CacheFormat]%type (B * CacheFormat))
      (Z : B -> Prop)
      (format_body_OK : Frame.monotonic_function format_body)
      (format_body_correct :
         forall data env binxenv, Inv data env binxenv -> Inv' data env binxenv)
      (format_body_correct' :
         forall data env binxenv,
           format_body Inv data env binxenv
           -> Inv data env binxenv)
      (decode_body_correct : forall x : B, (forall y : B, lt_B y x -> Z y) -> Z x)
  : (forall data env binxenv,
        LeastFixedPoint format_body data env binxenv ->
        Inv' data env binxenv)
    /\ (forall bin, Z bin).
Proof.
  split; intros.
  { destruct binxenv as [bin xenv].
    eapply (LeastFixedPoint_ind format_body Inv (fun a b cd => _ a b (fst cd) (snd cd))) in H; simpl.
    apply unfold_computes in H; simpl in H.
    pattern data, env, bin, xenv.
    eapply H; simpl; unfold refine; intros.
    unfold refine; setoid_rewrite unfold_computes; intros.
    eapply format_body_correct'; eauto.
    simpl; unfold refine. setoid_rewrite unfold_computes; intros ? ? ? ?.
    eapply format_body_correct; destruct v; simpl in *; eauto.
    intros; eapply (unroll_LeastFixedPoint' format_body_OK); eauto.
  }
  { eapply (well_founded_ind well_founded_lt_b).
    intros; eauto.
  }
Qed.

Definition CorrectDecoder_simpl'
           {A B}
           {cache: Cache}
           (format : FormatM A B)
           (decode : B -> CacheDecode -> option (A * CacheDecode))
           (bin : B):=
    (forall env env' xenv data,
        Equiv env env' ->
        computes_to (format data env) (bin, xenv) ->
        exists xenv',
          decode bin env' = Some (data, xenv') /\ Equiv xenv xenv')
    /\ (forall env env' xenv' data,
        Equiv env env'
        -> decode bin env' = Some (data, xenv')
        -> exists xenv,
            computes_to (format data env) (bin, xenv) /\ Equiv xenv xenv').

Lemma CorrectDecoder_simpl'_equiv
           {A B}
           {cache: Cache}
           (format : FormatM A B)
           (decode : B -> CacheDecode -> option (A * CacheDecode))
  : (forall b, CorrectDecoder_simpl' format decode b) <->
    CorrectDecoder_simpl format decode.
Proof.
  unfold CorrectDecoder_simpl, CorrectDecoder_simpl'; intuition.
  eapply H; eauto.
  eapply H; eauto.
  eapply H0; eauto.
  eapply H1; eauto.
Qed.

Fixpoint FueledFix' {A B C}
         (f : (B -> C -> option A) -> B -> C -> option A)
         (n : nat)
  : B -> C -> option A :=
  match n with
  | S n' => f (FueledFix' f n')
  | _ => fun _ _ => None
  end.

Definition FueledFix {A B C}
           {monoid : Monoid B}
           (f : (B -> C -> option A) -> B -> C -> option A)
  := fun b => FueledFix' f (S (bin_measure b)) b.

(*Lemma fix_format_correct_simpl''
      {A B}
      {cache : Cache}
      {monoid : Monoid B}
      (format_body : funType [A; CacheFormat]%type (B * CacheFormat) ->
                     funType [A; CacheFormat]%type (B * CacheFormat))
      (decode_body : (B ->  CacheDecode -> option (A * CacheDecode)) ->
                     B -> CacheDecode -> option (A * CacheDecode))
      (format_body_OK : Frame.monotonic_function format_body)
      (decode_body_correct :
         forall (format : funType [A; CacheFormat]%type (B * CacheFormat)) decode,
           (CorrectDecoder_simpl' format decode bin')
           -> CorrectDecoder_simpl' (format_body format) (decode_body decode) bin)
  : CorrectDecoder_simpl (LeastFixedPoint format_body)
                         (FueledFix decode_body).
Proof.
  unfold CorrectDecoder_simpl.
  assert (forall n bin, bin_measure bin < n ->
          (forall (env : CacheFormat) (env' : CacheDecode) (xenv : CacheFormat) (data : A),
    Equiv env env' ->
    LeastFixedPoint format_body data env ↝ (bin, xenv) ->
    exists xenv' : CacheDecode, FueledFix' decode_body n bin env' = Some (data, xenv') /\ Equiv xenv xenv') /\
   (forall (env : CacheFormat) (env' xenv' : CacheDecode) (data : A),
    Equiv env env' ->
    FueledFix' decode_body n bin env' = Some (data, xenv') ->
    exists xenv : CacheFormat, LeastFixedPoint format_body data env ↝ (bin, xenv) /\ Equiv xenv xenv'));
  try (intuition eauto; eapply H; eauto).
  intros ? ?.
  specialize (decode_body_correct bin); revert bin decode_body_correct.
  induction n.
  intros; inversion H.
  intros; pose proof (fun a b c d e f g => proj1  (decode_body_correct a b c) d e f g);
    pose proof (fun a b c d e f g => proj2 (decode_body_correct a b c) d e f g).
  clear decode_body_correct.
  split.
  intros.
  eapply (unroll_LeastFixedPoint format_body_OK) in H3; eauto.
  simpl; eapply H0; try eauto.
  intros.
  eapply
  split.
  intros; eapply IHn; eauto.
  admit.
  intros.
  simpl in H3; eapply H0 in H3; eauto.
  destruct_ex; eexists; intuition eauto.
  eapply (unroll_LeastFixedPoint' format_body_OK); eauto.
  admit.

  destruct H3.
  eexists.

  intros; eapply H; eauto.
  admit.

  eapply (proj1 IHn).
  split.


  eapply (well_founded_ind well_founded_lt_b); intros.
  split; intros.
  -  rewrite Init.Wf.Fix_eq by eassumption.
     eapply decode_body_correct; eauto.
     eapply (unroll_LeastFixedPoint format_body_OK); eauto.
  - rewrite Init.Wf.Fix_eq in H1 by eassumption.
    eapply decode_body_correct in H1; eauto.
    destruct_ex; eexists; intuition eauto.
    eapply (unroll_LeastFixedPoint' format_body_OK); eauto.
Qed. *)
