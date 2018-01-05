Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Formats.StringOpt.

Require Import
        Coq.NArith.NArith
        Recdef.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

(* Start Example Derivation. *)

Section Coordinate_Decoder.

Definition Coordinate :=
  @Tuple <"Time" :: N,
          "Latitude" :: Z * N,
          "Longitude" :: Z * N >.

Function N_to_string' (n : N) {wf N.lt n}: string :=
  match n with
  | N0 => EmptyString
  | _ => String.append (N_to_string' (BinNatDef.N.div n 10))%N (String (Ascii.ascii_of_N (48 + BinNatDef.N.modulo n 10))%N EmptyString)
end.
intros; apply N.div_lt; reflexivity.
apply N.lt_wf_0.
Defined.

Definition N_to_string (n : N) :=
  match n with
  | N0 => "0"
  | _ => N_to_string' n
  end.

Goal (N_to_string 10 ="10")%N%string.
  unfold N_to_string;
  repeat first [reflexivity
               | rewrite N_to_string'_equation; simpl].
Qed.

Goal (N_to_string 1030 ="1030")%N%string.
  unfold N_to_string;
  repeat first [reflexivity
               | rewrite N_to_string'_equation; simpl].
Qed.

Fixpoint string_to_N (s : string) : N :=
  match s with
  | EmptyString => 0
  | String c s' => ((Ascii.N_of_ascii c - 48) * 10^(N.of_nat (String.length s'))) + (string_to_N s')
  end%N.

Goal (10 = string_to_N "10")%N%string.
  reflexivity.
Qed.

Goal (1030 = string_to_N "1030")%N%string.
  reflexivity.
Qed.

Goal (0 = string_to_N "0")%N%string.
  reflexivity.
Qed.

Lemma string_length_append :
  forall s s', (String.length (s ++ s') = String.length s + String.length s')%nat.
Proof.
  induction s; simpl; intros; eauto.
Qed.

Lemma N_of_nat_distr :
  forall n n' : nat, (N.of_nat (n + n') = N.of_nat n + N.of_nat n')%N.
Proof.
  induction n; intros; eauto.
  simpl plus.
  rewrite !Nat2N.inj_succ, IHn, N.add_succ_l; reflexivity.
Qed.

Lemma string_to_N_append : forall s s',
    (string_to_N (s ++ s') = (string_to_N s * 10^(N.of_nat (String.length s'))) +
                             (string_to_N s'))%N.
Proof.
  induction s; simpl; intros; eauto.
  rewrite IHs.
  rewrite !N.add_assoc, string_length_append,
  N_of_nat_distr, N.pow_add_r, N.mul_add_distr_r, N.mul_assoc.
  reflexivity.
Qed.

Lemma N_to_string_inv
  : forall n, string_to_N (N_to_string n) = n.
Proof.
  destruct n; simpl.
  - reflexivity.
  - pattern (N.pos p), (N_to_string' (N.pos p)).
    apply N_to_string'_ind; intros; eauto.
    subst.
    rewrite string_to_N_append.
    rewrite H.
    simpl String.length; simpl N.of_nat.
    unfold string_to_N.
    rewrite Ascii.N_ascii_embedding.
    rewrite (N.div_mod' _x 10) at 3.
    simpl N.of_nat.
    replace (10 ^ 1)%N with 10%N by reflexivity.
    rewrite N.mul_comm.
    f_equal.
    generalize (_x mod 10)%N; intro.
    rewrite (Nplus_comm 48), (N.add_sub n), N.mul_1_r, N.add_0_r; reflexivity.
    eapply (N.add_lt_mono_l _ 208 48).
    etransitivity.
    eapply N.mod_bound_pos.
    eapply N.le_0_l.
    reflexivity.
    reflexivity.
Qed.

Definition string_to_Z (s : string) : Z :=
  match s with
  | String "-" s' => BinInt.Z.mul (BinInt.Z.of_N (string_to_N s')) (-1)
  | _ => BinInt.Z.of_N (string_to_N s)
  end.

Definition Z_to_string (z : Z) : string :=
  match z with
  | Zneg _ => String "-" (N_to_string (BinIntDef.Z.abs_N z))
  | _ => (N_to_string (BinIntDef.Z.abs_N z))
  end.

Lemma Z_to_string_inv
  : forall z, string_to_Z (Z_to_string z) = z.
Proof.
  destruct z eqn: ?; simpl.
  - reflexivity.
  - unfold string_to_Z.
    destruct (N_to_string' (N.pos p)) eqn: ?.
Admitted.

Definition Coordinate_format
           (coords : Coordinate) :=
          format_string_with_term_char " " (N_to_string (coords!"Time"))
    ThenC format_string_with_term_char "." (Z_to_string (fst coords!"Latitude"))
    ThenC format_string_with_term_char " " (N_to_string (snd coords!"Latitude"))
    ThenC format_string_with_term_char "." (Z_to_string (fst coords!"Longitude"))
    ThenC format_string_with_term_char " " (N_to_string (snd coords!"Longitude"))
    DoneC.

Definition Coordinate_decoder
  : CorrectDecoderFor (fun _ => True) Coordinate_format.
Proof.
  start_synthesizing_decoder.
  normalize_compose monoid.
  decode_step idtac.
  intros; eapply String_decode_with_term_char_correct.
  decode_step idtac.
  admit.
  decode_step idtac.
  decode_step idtac.
  intros; eapply String_decode_with_term_char_correct.
  decode_step idtac.
  admit.
  decode_step idtac.
  decode_step idtac.
  intros; eapply String_decode_with_term_char_correct.
  decode_step idtac.
  admit.
  decode_step idtac.
  decode_step idtac.
  intros; eapply String_decode_with_term_char_correct.
  decode_step idtac.
  admit.
  decode_step idtac.
  decode_step idtac.
  intros; eapply String_decode_with_term_char_correct.
  decode_step idtac.
  admit.
  decode_step idtac.
  simpl; intros **; eapply CorrectDecoderinish.
  unfold Domain, GetAttribute, GetAttributeRaw in *; simpl in *;
    (let a' := fresh in
     intros a'; repeat destruct a' as [? a']; unfold Domain, GetAttribute, GetAttributeRaw in *; simpl in *; intros **; intuition;
     repeat
       match goal with
       | H:_ = _
         |- _ => first
                   [ apply decompose_pair_eq in H; (let H1 := fresh in
                                                    let H2 := fresh in
                                                    destruct H as [H1 H2]; simpl in H1; simpl in H2)
                   | rewrite H in * ]
       end).
  destruct prim_fst0, prim_fst1; simpl in *.
  apply (f_equal string_to_N) in H7.
  apply (f_equal string_to_N) in H9.
  apply (f_equal string_to_N) in H11.
  apply (f_equal string_to_Z) in H8.
  apply (f_equal string_to_Z) in H10.
  rewrite N_to_string_inv, Z_to_string_inv in *.
  subst.
  reflexivity.
  unfold GetAttribute, GetAttributeRaw; simpl.
  Print Ltac build_fully_determined_type.
  decide_data_invariant.
  apply (@decides_True' _ proj).
  setoid_rewrite <- BoolFacts.string_dec_bool_true_iff;
    split; intro H5; apply H5.
  setoid_rewrite <- BoolFacts.string_dec_bool_true_iff;
    split; intro H5; apply H5.
  setoid_rewrite <- BoolFacts.string_dec_bool_true_iff;
    split; intro H5; apply H5.
  setoid_rewrite <- BoolFacts.string_dec_bool_true_iff;
    split; intro H5; apply H5.
  setoid_rewrite <- BoolFacts.string_dec_bool_true_iff;
    split; intro H5; apply H5.
  synthesize_cache_invariant.
  repeat optimize_decoder_impl.

Defined.

Definition Coordinate_decoder_impl :=
  Eval simpl in (fst (proj1_sig Coordinate_decoder)).

End Coordinate_Decoder.

Print Coordinate_decoder_impl.
