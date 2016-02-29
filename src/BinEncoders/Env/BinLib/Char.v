Require Export Coq.Strings.Ascii.
Require Import Coq.omega.Omega
               Fiat.BinEncoders.Env.Common.Specs
               Fiat.BinEncoders.Env.BinLib.Core
               Fiat.BinEncoders.Env.Common.Sig
               Fiat.BinEncoders.Env.BinLib.FixInt.

Set Implicit Arguments.

Section CharBinEncoder.
  Variable E E' : Type.
  Variable Eequiv : E -> E' -> Prop.

  Definition FixInt_of_ascii (c : ascii) : {n : N | (n < exp2 8)%N}.
    refine (exist _ (N_of_ascii c) _).
    unfold exp2; unfold exp2'.
    induction c.
    repeat (match goal with
              | B : bool |- _ => destruct B
            end); simpl; unfold Nlt; auto.
  Defined.

  Definition Char_encode (c : ascii) (e : bctx E) : bin * bctx E :=
    FixInt_encode (size:=8) (FixInt_of_ascii c) e.

  Definition Char_decode (b : bin) (e : bctx E') : ascii * bin * bctx E' :=
    let (x, e) := FixInt_decode 8 b e in
    let (n, b) := x in
        (ascii_of_N (proj1_sig n), b, e).

  Theorem Char_encode_correct :
    forall predicate, encode_decode_correct (bctx_equiv Eequiv) btransformer predicate Char_encode Char_decode.
  Proof.
    intros pred env env' xenv xenv' c c' bin ext ext' Peq Ppred Penc Pdec.
    pose proof (@FixInt_encode_correct 8 E E' Eequiv (fun x => pred (ascii_of_N (proj1_sig x)))
                   env env' xenv xenv' (FixInt_of_ascii c) (FixInt_of_ascii c') bin ext ext'
                   Peq) as H.
    simpl in *. rewrite ascii_N_embedding in H.
    specialize (H Ppred Penc). clear Ppred Penc.
    inversion Peq; clear Peq; subst.
    unfold Char_decode in Pdec.
    destruct (FixInt_decode 8 (app bin ext) env') as [[? ?] ?] eqn: eq.
    inversion Pdec; clear Pdec; subst.
    assert (s = FixInt_of_ascii (ascii_of_N (proj1_sig s))).
    destruct s; eapply sig_equivalence; rewrite N_ascii_embedding; eauto.
    rewrite <- H2 in H. specialize (H eq_refl). intuition. subst.
    destruct (FixInt_of_ascii c) eqn: eq2. simpl. inversion eq2.
    rewrite ascii_N_embedding. eauto.
  Qed.
End CharBinEncoder.

Global Instance Char_decoder E E' ctxequiv predicate
  : decoder (bctx_equiv ctxequiv) btransformer predicate (@Char_encode E) :=
  { decode := @Char_decode E';
    decode_correct := @Char_encode_correct _ _ _ _ }.
