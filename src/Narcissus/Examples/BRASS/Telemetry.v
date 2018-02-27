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
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BinLib.AlignedString
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Common.Tactics.HintDbExtra
        Fiat.Common.Tactics.TransparentAbstract
        Fiat.Common.Tactics.CacheStringConstant.

Require Import
        Coq.Arith.PeanoNat
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
          "Latitude" :: Z * (nat * N),
          "Longitude" :: Z * (nat * N) >.

Function N_to_string' (n : N) {wf N.lt n}: string :=
  match n with
  | N0 => EmptyString
  | _ => String.append (N_to_string' (BinNatDef.N.div n 10))%N (String (Ascii.ascii_of_N (48 + BinNatDef.N.modulo n 10))%N EmptyString)
end.
intros; apply N.div_lt; reflexivity.
apply N.lt_wf_0.
Defined.


Print AlignedByteString.length_ByteString.

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

Definition string_to_Nnat (s : string) : nat * N :=
  (String.length s, string_to_N s).

Fixpoint replicate (n : nat) (s : string) : string :=
  match n with
  | O => ""
  | S x => s ++ replicate x s
  end.

Lemma replicate_length : forall n s,
  String.length (replicate n s) = n * String.length s.
Proof.
  intros.
  induction n; simpl; auto.
  now rewrite string_length_append, IHn.
Qed.

Definition Nnat_to_string (z : nat * N) : string :=
  let s := N_to_string (snd z) in
  (if (String.length s <? fst z)%nat
   then replicate (fst z - String.length s) "0" ++ s
   else s).

Lemma replicated_zeroes : forall n, string_to_N (replicate n "0") = 0%N.
Proof. induction n; simpl; auto. Qed.

Lemma distribute_if : forall A B (f : A -> B) (b : bool) (t e : A),
  f (if b then t else e) = if b then f t else f e.
Proof.
  now destruct b.
Qed.

(*
Lemma Nnat_to_string_inv
  : forall nn, (fst nn > String.length (N_to_string (snd nn)))%nat
      -> string_to_Nnat (Nnat_to_string nn) = nn.
Proof.
  Import Omega.
  unfold Nnat_to_string, string_to_Nnat; intros.
  destruct nn; simpl.
  f_equal.
    rewrite distribute_if.
    rewrite string_length_append.
    rewrite replicate_length.
    rewrite Nat.mul_1_r.
    remember (String.length (N_to_string n0)) as l.
    destruct (l <? n) eqn:?.
      apply Nat.ltb_lt in Heqb.
      omega.
    apply Nat.ltb_ge in Heqb.
    simpl in H.
    omega.
  rewrite distribute_if.
  rewrite string_to_N_append.
  rewrite N_to_string_inv.
  destruct (String.length (N_to_string n0) <? n) eqn:?; auto.
  simpl in H.
  apply Nat.ltb_lt in Heqb.
  now rewrite replicated_zeroes.
Qed.
*)

Lemma Nnat_to_string_inv
  : forall nn, string_to_Nnat (Nnat_to_string nn) = nn.
Proof.
  Import Omega.
  unfold Nnat_to_string, string_to_Nnat; intros.
  destruct nn; simpl.
  f_equal.
    rewrite distribute_if.
    rewrite string_length_append.
    rewrite replicate_length.
    rewrite Nat.mul_1_r.
    remember (String.length (N_to_string n0)) as l.
    destruct (l <? n) eqn:?.
      apply Nat.ltb_lt in Heqb.
      omega.
    apply Nat.ltb_ge in Heqb.
    admit.
  rewrite distribute_if.
  rewrite string_to_N_append.
  rewrite N_to_string_inv.
  destruct (String.length (N_to_string n0) <? n) eqn:?; auto.
  apply Nat.ltb_lt in Heqb.
  now rewrite replicated_zeroes.
Admitted.

(*
Lemma string_to_Nnat_inv
  : forall s, (String.length s > 0)%nat
      -> Nnat_to_string (string_to_Nnat s) = s.
Proof.
  unfold Nnat_to_string, string_to_Nnat; intros.
  induction s; simpl in *; auto.
    inversion H.
Abort.
*)

Lemma string_to_Nnat_inv
  : forall s, Nnat_to_string (string_to_Nnat s) = s.
Proof.
  unfold Nnat_to_string, string_to_Nnat; intros.
  induction s; simpl in *; auto.
Abort.

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

Lemma no_space_in_N_to_string
  : forall (n : N) (s1 s2 : string),
    N_to_string n <> (s1 ++ String " " s2)%string.
Proof.
Admitted.

Lemma no_space_in_Nnat_to_string
  : forall (nn : nat * N) (s1 s2 : string),
    Nnat_to_string nn <> (s1 ++ String " " s2)%string.
Proof.
Admitted.

Lemma no_dot_in_Z_to_string
  : forall (z : Z) (s1 s2 : string),
    Z_to_string z <> (s1 ++ String "." s2)%string.
Proof.
Admitted.

Definition newline := Ascii.Ascii false true false true false false false false.

Lemma no_newline_in_N_to_string
  : forall (n : N) (s1 s2 : string),
    N_to_string n <> (s1 ++ String newline s2)%string.
Proof.
Admitted.

Lemma no_newline_in_Nnat_to_string
  : forall (n : nat * N) (s1 s2 : string),
    Nnat_to_string n <> (s1 ++ String newline s2)%string.
Proof.
Admitted.

Set Printing All.

Eval compute in "0".
(*  Npos (xO (xO (xO (xO (xI xH))))) *)
(* Npos (xI (xO (xO (xO (xI xH))))) *)
(*  Npos (xI (xO (xO (xI (xI xH))))) *)
060 && 071

Fixpoint stringIsNumber (s : string) : bool :=
  match s with
  | EmptyString => True
  | String a s' =>
  end.

Lemma  N_to_string (string_to_N proj) = proj)

Definition Coordinate_format
           (coords : Coordinate) :=
          format_string_with_term_char " " (N_to_string (coords!"Time"))
    ThenC format_string_with_term_char "." (Z_to_string (fst coords!"Latitude"))
    ThenC format_string_with_term_char " " (Nnat_to_string (snd coords!"Latitude"))
    ThenC format_string_with_term_char "." (Z_to_string (fst coords!"Longitude"))
    ThenC format_string_with_term_char newline (Nnat_to_string (snd coords!"Longitude"))
    DoneC.

Definition Coordinate_decoder
  : CorrectDecoderFor (fun _ => True) Coordinate_format.
Proof.
  start_synthesizing_decoder.
  - normalize_compose monoid.
    decode_step idtac.
    + intros; eapply String_decode_with_term_char_correct.
      decode_step idtac.
    + intros; simpl; eapply no_space_in_N_to_string.
    + decode_step idtac.
    + decode_step idtac.
      * intros; eapply String_decode_with_term_char_correct.
        decode_step idtac.
      * intros; simpl; eapply no_dot_in_Z_to_string.
      * decode_step idtac.
      * decode_step idtac.
        ** intros; eapply String_decode_with_term_char_correct.
           decode_step idtac.
        ** intros. simpl.
           intros; simpl; eapply no_space_in_Nnat_to_string.
        ** decode_step idtac.
        ** decode_step idtac.
           *** intros; eapply String_decode_with_term_char_correct.
               decode_step idtac.
           *** intros; simpl; eapply no_dot_in_Z_to_string.
           *** decode_step idtac.
           *** decode_step idtac.
               **** intros; eapply String_decode_with_term_char_correct.
                    decode_step idtac.
               **** intros; simpl; eapply no_newline_in_Nnat_to_string.
               **** decode_step idtac.
               **** simpl; intros **; eapply CorrectDecoderinish.
    ***** {
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
      apply (f_equal string_to_Nnat) in H7.
      apply (f_equal string_to_Nnat) in H9.
      apply (f_equal string_to_N) in H11.
      apply (f_equal string_to_Z) in H8.
      apply (f_equal string_to_Z) in H10.
      rewrite Nnat_to_string_inv, N_to_string_inv, Z_to_string_inv in *.
      subst; reflexivity.
    }
    ***** {
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
    }
  - synthesize_cache_invariant.
  - repeat optimize_decoder_impl.
Defined.

Definition Coordinate_decoder_impl :=
  Eval simpl in (fst (proj1_sig Coordinate_decoder)).

Ltac rewrite_DecodeOpt2_fmap :=
  set_refine_evar;
  progress rewrite ?BindOpt_map, ?DecodeOpt2_fmap_if,
  ?DecodeOpt2_fmap_if_bool;
  subst_refine_evar.

Definition ByteAligned_Coordinate_decoder_impl'
           n
  : {impl : _ & forall (v : Vector.t _ n),
         (Coordinate_decoder_impl (build_aligned_ByteString v) ()) =
         impl v ()}.
Proof.
  unfold Coordinate_decoder_impl.
  eexists _; intros.
  etransitivity.
  set_refine_evar; simpl.
  rewrite optimize_align_decode_string_w_term_char; eauto.
  rewrite (If_Opt_Then_Else_DecodeBindOpt (cache := EmptyStore.test_cache)); simpl.
  eapply optimize_under_if_opt; simpl; intros.
  rewrite optimize_align_decode_string_w_term_char; eauto.
  rewrite (If_Opt_Then_Else_DecodeBindOpt (cache := EmptyStore.test_cache)); simpl.
  eapply optimize_under_if_opt; simpl; intros.
  rewrite optimize_align_decode_string_w_term_char; eauto.
  rewrite (If_Opt_Then_Else_DecodeBindOpt (cache := EmptyStore.test_cache)); simpl.
  eapply optimize_under_if_opt; simpl; intros.
  rewrite optimize_align_decode_string_w_term_char; eauto.
  rewrite (If_Opt_Then_Else_DecodeBindOpt (cache := EmptyStore.test_cache)); simpl.
  eapply optimize_under_if_opt; simpl; intros.
  rewrite optimize_align_decode_string_w_term_char; eauto.
  rewrite (If_Opt_Then_Else_DecodeBindOpt (cache := EmptyStore.test_cache)); simpl.
  eapply optimize_under_if_opt; simpl; intros.
  (* Could simplify the nested ifs here. *)
  higher_order_reflexivity.
  higher_order_reflexivity.
  higher_order_reflexivity.
  higher_order_reflexivity.
  higher_order_reflexivity.
  higher_order_reflexivity.
  simpl.
  higher_order_reflexivity.
Defined.

Definition aligned_Coordinate_decoder_impl n v :=
  Eval simpl in (projT1 (ByteAligned_Coordinate_decoder_impl' n) v ()).


Lemma format_string_with_term_char_length_gt_0
  : forall c s v,
    format_string_with_term_char c s () ↝ v
    -> lt 0 (AlignedByteString.length_ByteString (fst v)).
Proof.
  induction s; unfold format_string_with_term_char;
    simpl; unfold Bind2; intros;
      computes_to_inv; subst; simpl.
  - unfold AsciiOpt.format_ascii in *.
    unfold WordOpt.format_word in *; computes_to_inv; subst;
      simpl.
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq (WordOpt.encode_word' _ _ _)).
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq AlignedByteString.ByteString_id).
    rewrite BoundedByteStringToByteString_ByteString_id_eq.
    rewrite ByteString_enqueue_ByteString_ByteStringToBoundedByteString.
    rewrite length_ByteString_ByteStringToBoundedByteString_eq.
    rewrite ByteString_enqueue_ByteString_measure.
    simpl; generalize (NToWord 8 (Ascii.N_of_ascii c)).
    intros; shatter_word w; simpl.
    Omega.omega.
  - unfold AsciiOpt.format_ascii in *.
    unfold WordOpt.format_word in *; computes_to_inv; subst;
      simpl.
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq (WordOpt.encode_word' _ _ _)).
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq (fst v1)).
    rewrite ByteString_enqueue_ByteString_ByteStringToBoundedByteString.
    rewrite length_ByteString_ByteStringToBoundedByteString_eq.
    rewrite ByteString_enqueue_ByteString_measure.
    simpl; generalize (NToWord 8 (Ascii.N_of_ascii a)).
    intros; shatter_word w; simpl.
    Omega.omega.
Qed.

Lemma AlignedByteString_length_ByteString_enqueue
  : forall bs bs',
  AlignedByteString.length_ByteString
    (AlignedByteString.ByteString_enqueue_ByteString bs bs')
  =   AlignedByteString.length_ByteString bs
      +   AlignedByteString.length_ByteString bs'.
Proof.
  intros.
  rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq bs).
  rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq bs').
  rewrite !length_ByteString_ByteStringToBoundedByteString_eq.
  rewrite ByteString_enqueue_ByteString_ByteStringToBoundedByteString.
  rewrite length_ByteString_ByteStringToBoundedByteString_eq.
  rewrite ByteString_enqueue_ByteString_measure.
  reflexivity.
Qed.

Lemma Coordinate_decoder_impl_wf : forall s u x s' u',
    Coordinate_decoder_impl s u = Some ((x, s'), u')
    -> lt (AlignedByteString.length_ByteString s')
          (AlignedByteString.length_ByteString s).
Proof.
  intros.
  (* Use the -> direction of decoder correctness to infer that
     s = Coordinate_format x ++ s'*)
  let H' := fresh in
  let H'' := fresh in
  pose proof (proj2_sig Coordinate_decoder) as [? H'];
    pose proof (proj2 (proj1 H' (proj2 H'))) as H'';
    eapply (H'' ()) in H; clear H'' H'; simpl; eauto;
      repeat (intuition; destruct_ex); subst.
  (* Simplify with the definition of ByteString length. *)
  let H := eval simpl in mappend_measure in
      rewrite H.
  (* Use the format to show that an encoded coordinate produces a
   nonempty bytestring. *)
  unfold Coordinate_format, compose, Bind2 in H1.
  computes_to_inv; injections; simpl in *.
  apply format_string_with_term_char_length_gt_0 in H1.
  rewrite !AlignedByteString_length_ByteString_enqueue.
  simpl in *; Omega.omega.
Qed.

Lemma aligned_Coordinate_decoder_impl_wf
  : forall n (s : t char n) x
           s' u',
    aligned_Coordinate_decoder_impl n s = Some ((x, s'), u')
    -> lt (AlignedByteString.length_ByteString s')
          (AlignedByteString.length_ByteString (build_aligned_ByteString s)).
Proof.
  intros.
  (* Use the -> direction of decoder correctness to infer that
     s = Coordinate_format x ++ s'*)
  unfold aligned_Coordinate_decoder_impl in H;
    let H' := eval simpl in (projT2 (ByteAligned_Coordinate_decoder_impl' n) s) in
        rewrite <- H' in H.
  apply Coordinate_decoder_impl_wf in H.
  eauto.
Qed.

Definition inputString :=
  Eval compute in
  (StringToBytes
  ("0542999 -42.4539680 76.4585433"
     ++ String.String newline String.EmptyString))%string.

Example foo :
  aligned_Coordinate_decoder_impl _ inputString =
  aligned_Coordinate_decoder_impl _ inputString.
unfold aligned_Coordinate_decoder_impl.
Time vm_compute.

Eval vm_compute in (N_to_string' 542999).
destruct (string_dec (N_to_string' 4585433)
         (String (Ascii.ascii_of_pos 52)
            (String (Ascii.ascii_of_pos 53)
               (String (Ascii.ascii_of_pos 56)
                  (String (Ascii.ascii_of_pos 53)
                     (String (Ascii.ascii_of_pos 52) (String (Ascii.ascii_of_pos 51) (String (Ascii.ascii_of_pos 51) "")))))))) eqn:?.
simpl in e.
compute in Heqs.
find_if_inside.
simpl.
simpl.
compute.

End Coordinate_Decoder.

Print Coordinate_decoder_impl.
Print aligned_Coordinate_decoder_impl.
