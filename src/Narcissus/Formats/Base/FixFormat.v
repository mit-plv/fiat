Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.Base.FMapFormat.

Require Import Fiat.Computation.FixComp.
Import Fiat.Computation.FixComp.LeastFixedPointFun.

Section FixFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {cache : Cache}. (* State Type *)

  Definition Fix_Format
             (format_body : FormatM S T -> FormatM S T)
    := LeastFixedPoint (fDom := [S; CacheFormat]%type)
                       (fCod := T * CacheFormat) format_body.

  sxFixpoint FueledFix' {A B C}
           (f : (B -> C -> option A) -> B -> C -> option A)
           (n : nat)
    : B -> C -> option A :=
    match n with
    | Datatypes.S n' => f (FueledFix' f n')
    | _ => fun _ _ => None
    end.

  Definition Fix_Decode
             (decode_body : DecodeM S T -> DecodeM S T)
    : nat -> DecodeM S T :=
    FueledFix' decode_body.

  Lemma CorrectDecoder_Fix
        {monoid : Monoid T}
        (format_body : FormatM S T -> FormatM S T)
        (decode_body : DecodeM S T -> DecodeM S T)
    : forall (sz : nat),
      (forall s env tenv', computes_to (Fix_Format format_body s env) tenv'
                          -> bin_measure (fst tenv') > 0)
      -> (forall (sz' : nat),
          sz' < sz ->
          CorrectDecoder_simpl (fun s env tenv' => computes_to (Fix_Format format_body s env) tenv'
                                                   /\ bin_measure (fst tenv') <= sz') (Fix_Decode decode_body sz'))
      -> CorrectDecoder_simpl (Fix_Format format_body) (Fix_Decode decode_body sz).
  Proof.
    intros.
    unfold Fix_Decode; simpl.
    induction sz.
    simpl; intros.


  Lemma fix_format_correct_simpl''
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
Qed.
