Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.NoCache
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

Opaque pow2. (* Don't want to be evaluating this. *)
Opaque natToWord. (* Or this. *)

Ltac apply_compose :=
  intros;
  match goal with
    H : cache_inv_Property ?P ?P_inv |- _ =>
    first [eapply (compose_encode_correct_no_dep _ H); clear H
          | eapply (compose_encode_correct H); clear H
          | eapply (composeIf_encode_correct H); clear H;
            [ |
              | solve [intros; intuition (eauto with bin_split_hints) ]
              | solve [intros; intuition (eauto with bin_split_hints) ] ]
          ]
  end.

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac shelve_inv :=
  let H' := fresh in
  let data := fresh in
  intros data H';
  repeat destruct H';
  match goal with
  | H : ?P data |- ?P_inv' =>
    is_evar P;
    let P_inv' := (eval pattern data in P_inv') in
    let P_inv := match P_inv' with ?P_inv data => P_inv end in
    let new_P_T := type of P in
    makeEvar new_P_T
             ltac:(fun new_P =>
                     unify P (fun data => new_P data /\ P_inv data)); apply (Logic.proj2 H)
  end.

Ltac solve_data_inv data_inv_hints :=
  first [ simpl; intros; exact I
        | solve [intuition eauto using data_inv_hints]
        | shelve_inv ].

Definition transformer : Transformer ByteString := ByteStringQueueTransformer.

(* Start Example Derivation. *)

Definition EthernetHeader :=
  @Tuple <"Destination" :: Vector.t char 6,
  "Source" :: Vector.t char 6,
  "Type" :: EnumType ["ARP"; "IP"; "RARP"]>.

Definition EtherTypeCodes : Vector.t (word 16) 3 :=
  [WO~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0;
   WO~0~0~0~0~1~0~0~0~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~1~0~0~0~0~0~1~1~0~1~0~1
  ].

Definition encode_EthernetHeader_Spec n' (eth : EthernetHeader) :=
          encode_Vector_Spec encode_word_Spec eth!"Destination"
    ThenC (encode_Vector_Spec encode_word_Spec eth!"Source")
    ThenC Either
          encode_nat_Spec 16 n'
          ThenC encode_word_Spec (WO~0~1~0~1~0~1~0~1)
          ThenC encode_word_Spec (WO~0~1~0~1~0~1~0~1)
          ThenC encode_word_Spec (WO~1~1~0~0~0~0~0~0)
          ThenC encode_word_Spec (wzero 24)
          ThenC encode_enum_Spec EtherTypeCodes eth!"Type"
          DoneC
       Or encode_enum_Spec EtherTypeCodes eth!"Type"
          DoneC.

Definition ethernet_Header_OK (e : EthernetHeader) := True.

Definition v1042_test (b : ByteString) : bool :=
  match transformer_get_word 16 b with
  | Some w => if wlt_dec w (natToWord 16 1501) then true else false
  | _ => false
  end.

Lemma v1042_OKT
  : forall n (data : EthernetHeader) (bin : ByteString) (env xenv : CacheEncode) (ext : ByteString),
    lt n 1501 ->
   (encode_nat_Spec 16 n
    ThenC encode_word_Spec WO~0~1~0~1~0~1~0~1
    ThenC encode_word_Spec WO~0~1~0~1~0~1~0~1
    ThenC encode_word_Spec WO~1~1~0~0~0~0~0~0
    ThenC encode_word_Spec (wzero 24) ThenC encode_enum_Spec EtherTypeCodes data!"Type" DoneC) env
   ↝ (bin, xenv) -> v1042_test (transform bin ext) = true.
Proof.
  intros.
  unfold compose at 1 in H0; unfold Bind2 in H0;
    computes_to_inv; destruct v; destruct v0; simpl in *;
        injections.
  unfold encode_nat_Spec, encode_word_Spec in H0; computes_to_inv.
  pose proof (f_equal fst H0) as H'; simpl in H'; rewrite <- H'.
  pose proof transform_assoc as H''; simpl in H''; rewrite <- H''.
  unfold v1042_test.
  pose transformer_get_encode_word' as H'''; rewrite H'''; find_if_inside; eauto.
  destruct n0.
  eapply natToWord_wlt; eauto; try reflexivity.
  etransitivity.
  unfold BinNat.N.lt; rewrite <- Nnat.Nat2N.inj_compare.
  eapply Compare_dec.nat_compare_lt; eassumption.
  reflexivity.
Qed.

Hint Resolve v1042_OKT : bin_split_hints.

Lemma v1042_OKE
  : forall (data : EthernetHeader) (bin : ByteString) (env xenv : CacheEncode) (ext : ByteString),
    (encode_enum_Spec EtherTypeCodes data!"Type" DoneC) env ↝ (bin, xenv)
    -> v1042_test (transform bin ext) = false.
Proof.
  intros; unfold compose at 1 in H; unfold Bind2 in H;
    computes_to_inv; destruct v; destruct v0; simpl in *;
      injections.
  unfold encode_enum_Spec, encode_word_Spec in H; computes_to_inv.
  pose proof (f_equal fst H) as H'; unfold fst in H'; rewrite <- H'.
  pose proof transform_assoc as H''; simpl in H''; rewrite <- H''.
  unfold v1042_test.
  pose transformer_get_encode_word' as H'''; rewrite H'''; find_if_inside; eauto.
  revert w; clear.
  match goal with
    |- context [Vector.nth (m := ?n) ?w ?idx] => remember idx; clear
  end.
  Local Transparent natToWord.
  eapply forall_Vector_P; repeat econstructor;
    unfold wlt; compute; intros; discriminate.
Qed.

Hint Resolve v1042_OKE : bin_split_hints.

Lemma valid_packet_len_OK_good_Len
    : forall packet_len,
    lt packet_len 1501 -> lt packet_len (pow2 16).
  Proof.
    intros.
    etransitivity; eauto.
    rewrite <- (wordToNat_natToWord_idempotent 16 1501).
    eapply wordToNat_bound.
    simpl; eapply BinNat.N.ltb_lt; reflexivity.
Qed.

Ltac start_synthesizing_decoder :=
  (* Unfold encoder specification and the data and packet invariants *)
  repeat
    match goal with
      |- appcontext [encode_decode_correct_f _ _ ?dataInv ?restInv ?encodeSpec] =>
      first [unfold dataInv
            | unfold restInv
            | unfold encodeSpec ]
    | |- appcontext [encode_decode_correct_f _ _ ?dataInv ?restInv (?encodeSpec _)] =>
      first [unfold dataInv
            | unfold restInv
            | unfold encodeSpec ]
    end;
  
  (* Memoize any string constants *)
  pose_string_hyps;
  (* Initialize the various goals with evars *)
  eexists (_, _), _; split; simpl.

Ltac decode_step :=
  match goal with
  | |- _ => apply_compose
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_Vector_Spec _) _ _] =>
    intros; eapply Vector_decode_correct
  | H : cache_inv_Property _ _
    |- appcontext [encode_decode_correct_f _ _ _ _ encode_word_Spec _ _] =>
    intros; revert H; eapply Word_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ encode_word_Spec _ _] =>
    eapply Word_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_nat_Spec _) _ _] =>
    eapply Nat_decode_correct
  | |- appcontext [encode_decode_correct_f _ _ _ _ (encode_enum_Spec _) _ _] =>
    eapply Enum_decode_correct
  | |- NoDupVector _ => Discharge_NoDupVector
  | |- context[Vector_predicate_rest (fun _ _ => True) _ _ _ _] =>
    intros; apply Vector_predicate_rest_True
  | _ => solve [solve_data_inv valid_packet_len_OK_good_Len]
  end.

Definition EthernetHeader_decoder
  : { decodePlusCacheInv |
      forall packet_len,
        lt packet_len 1501
        -> exists P_inv,
          (cache_inv_Property (snd decodePlusCacheInv) P_inv
           -> encode_decode_correct_f _ transformer ethernet_Header_OK (fun _ b => b = ByteString_id)
                                      (encode_EthernetHeader_Spec packet_len)
                                      (fst decodePlusCacheInv packet_len) (snd decodePlusCacheInv))
          /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
Proof.
  start_synthesizing_decoder.
  repeat decode_step.
  simpl; intros;
    eapply encode_decode_correct_finish.
  destruct a' as [? [? [? [ ] ] ] ] ;
  unfold GetAttribute, GetAttributeRaw in *;
    simpl in *; intros; intuition.
  subst.
  reflexivity.
  unfold GetAttribute, GetAttributeRaw in *;
    simpl in *; intros; intuition.
  repeat
    first [eapply decides_and
          | eapply decides_assumption; eassumption
          | apply decides_eq_refl
          | eapply decides_dec_eq; auto using Peano_dec.eq_nat_dec, weq ].
  repeat decode_step.
  simpl; intros;
    eapply encode_decode_correct_finish.
  destruct a' as [? [? [? [ ] ] ] ] ;
  unfold GetAttribute, GetAttributeRaw in *;
    simpl in *; intros; intuition.
  subst.
  reflexivity.
  unfold GetAttribute, GetAttributeRaw in *;
    simpl in *; intros; intuition.
  repeat
    first [eapply decides_and
          | eapply decides_assumption; eassumption
          | apply decides_eq_refl
          | eapply decides_dec_eq; auto using Peano_dec.eq_nat_dec, weq ].
  repeat (instantiate (1 := fun _ => True)).
  unfold cache_inv_Property; intuition.
  Grab Existential Variables.
  exact (@weq _).
  exact (@weq _).
  exact (@weq _).
  exact (@weq _).
  exact Peano_dec.eq_nat_dec.
Defined.

Definition frame_decoder := Eval simpl in proj1_sig EthernetHeader_decoder.
Print frame_decoder.
