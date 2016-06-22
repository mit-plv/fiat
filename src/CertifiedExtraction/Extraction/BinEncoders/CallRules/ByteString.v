Require Export
        Fiat.CertifiedExtraction.Extraction.Extraction.

Require Import
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Basics
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Wrappers
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Map8.

Require Import
        Coq.Program.Program
        Coq.Lists.List.

Unset Implicit Arguments.

Definition FixedCapacityAppend {c} (l1 l2: BytableListOfBools c) : BytableListOfBools c.
  exists (List.app (projT1 l1) (projT1 l2)).
  exists ((proj1_sig (projT2 l1)) + (proj1_sig (projT2 l2))).
  abstract (rewrite app_length, Mult.mult_plus_distr_l;
            repeat f_equal; apply (proj2_sig (projT2 l1)) || apply (proj2_sig (projT2 l2))).
Defined.

Definition FixedCapacityAppendOne {c} (l1: BytableListOfBools c) (x: BitArray 8) : BytableListOfBools c.
  refine (FixedCapacityAppend l1 _).
  eexists (proj1_sig x).
  eexists 1; exact (proj2_sig x).
Defined.

Lemma Write8_side_condition_helper {A B}:
  forall n f a (s: list A),
    15 + Datatypes.length s <= 8 * n ->
    List.length (map8 (B := B) f a s) + 1 <= n.
Proof.
  intros.
  rewrite NPeano.Nat.mul_le_mono_pos_l, Mult.mult_plus_distr_l, Mult.mult_1_r.
  etransitivity; [ apply Plus.plus_le_compat_r, map8_length_top | ].
  omega. omega.
Qed.

Hint Resolve Write8_side_condition_helper : call_helpers_db.

Lemma map8_BoolsToB_Array8 :
  forall pad (n: BitArray 8),
    map8 BoolsToB pad (` n) = (FixListBoolToWord n) :: nil.
Proof.
  destruct n as (n & p).
  repeat (destruct n; simpl in p; inversion p; []);
    simpl; rewrite (UipNat.UIP_refl _ p); reflexivity.
Qed.

Ltac injections :=
  match goal with
  | [ H: existT _ _ _ = existT _ _ _ |- _ ] => apply UipNat.inj_pair2 in H
  end.

Lemma CompileCallWrite8_helper:
  forall (n : BitArray 8) (c : W) (stream : BytableListOfBools c),
    forall x, x = FixListBoolToWord n ->
    map8 BoolsToB false (projT1 stream) ++ (x :: nil) =
    map8 BoolsToB false (projT1 stream ++ (` n)).
Proof.
  destruct stream as (? & ? & ?); simpl; intros.
  subst; rewrite map8append, map8_BoolsToB_Array8; eauto.
Qed.

Lemma CompileCallWrite8_base (c: W):
  let wr := @WrapListBoolIntoListByte c in
  forall (vtmp varg vstream : string) (stream : BytableListOfBools c) (tenv: Telescope ADTValue)
    (n : BitArray 8) ext env
    fWrite8,
    vtmp <> vstream ->
    vtmp ∉ ext ->
    vstream ∉ ext ->
    Lifted_not_mapsto_adt ext tenv vtmp ->
    Lifted_MapsTo ext tenv varg (wrap (FacadeWrapper := WrapListBool8) n) ->
    Lifted_MapsTo ext tenv vstream (wrap stream) ->
    GLabelMap.MapsTo fWrite8 (Axiomatic BytesADTSpec.Push) env ->
    16 + Datatypes.length (projT1 stream) <= 8 * Word.wordToNat c ->
    {{ tenv }}
      (Call vtmp fWrite8 [vstream; varg])
    {{ [[ `vtmp ->> Word.wzero 32 as _ ]]
        :: [[ `vstream ->> FixedCapacityAppendOne stream n as _]]
        :: (DropName vstream (DropName vtmp tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  facade_eauto.
  facade_eauto.
  facade_eauto.
  Transparent Word.natToWord.
  simpl in *;
    match goal with
    | [ H: Some _ = Some _ |- _ ] => inversion H (* subst is broken *)
    end; repeat injections; repeat f_equal; try congruence.
  apply CompileCallWrite8_helper; simpl in *; eauto || congruence.
  repeat apply DropName_remove; congruence.
Qed.

Lemma CompileCallWrite8 (c: W):
  let wr := @WrapListBoolIntoListByte c in
  forall (vtmp varg vstream : string) (stream : BytableListOfBools c) (tenv tenv' tenv'': Telescope ADTValue)
    (n : BitArray 8) (w: W) ext env pNext pArg
    fWrite8,
    PreconditionSet tenv' ext [[[vtmp; vstream; varg]]] ->
    GLabelMap.MapsTo fWrite8 (Axiomatic BytesADTSpec.Push) env ->
    16 + Datatypes.length (projT1 stream) <= 8 * Word.wordToNat c ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      pArg
    {{ [[ ` vstream ->> stream as _]]::[[ ` varg ->> n as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> FixedCapacityAppendOne stream n as _]]::tenv' }}
      pNext
    {{ [[ ` vstream ->> FixedCapacityAppendOne stream n as _]]::tenv'' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      Seq pArg (Seq (Call vtmp fWrite8 [vstream; varg]) pNext)
    {{ [[ ` vstream ->> FixedCapacityAppendOne stream n as _]]::tenv'' }} ∪ {{ ext }} // env.
Proof.
  hoare.
  hoare.
  hoare.
  PreconditionSet_t;
    apply ProgOk_Remove_Skip_R; hoare;
    [ apply generalized CompileCallWrite8_base | ];
    repeat match goal with
           | _ => progress intros
           | _ => apply ProgOk_Chomp_Some
           | _ => apply CompileDeallocW_discretely
           | _ => apply CompileDeallocSCA_discretely
           | _ => progress (compile_do_side_conditions || Lifted_t)
           end; apply CompileSkip.
Qed.

Lemma CompileCallWrite8_EncodeAndPad (c: W):
  forall (vtmp varg vstream : string) (stream : BytableListOfBools c) (tenv tenv' tenv'': Telescope ADTValue)
    (n : BoundedN 8) ext env
    pArg pNext fWrite8,
    PreconditionSet tenv' ext [[[vtmp; vstream; varg]]] ->
    16 + Datatypes.length (projT1 stream) <= 8 * Word.wordToNat c ->
    GLabelMap.MapsTo fWrite8 (Axiomatic BytesADTSpec.Push) env ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      pArg
    {{ [[ ` vstream ->> stream as _]]::[[ ` varg ->> n as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> FixedCapacityAppendOne stream (EncodeAndPad n) as _]]::tenv' }}
      pNext
    {{ [[ ` vstream ->> FixedCapacityAppendOne stream (EncodeAndPad n) as _]]::tenv'' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      Seq pArg (Seq (Call vtmp fWrite8 [vstream; varg]) pNext)
    {{ [[ ` vstream ->> FixedCapacityAppendOne stream (EncodeAndPad n) as _]]::tenv'' }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? ? H ?.
  setoid_rewrite (TelEq_same_wrap _ _ (WrapN8_WrapListBool8 _)) in H.
  eapply CompileCallWrite8; eauto.
Qed.

(* FIXME *)

Lemma CompileCallWrite16:
  forall (vtmp varg vstream : string) (stream : list bool) (tenv tenv' tenv'': Telescope ADTValue)
    (n : BitArray 16) ext env
    pArg pNext fWrite16,
    Lifted_not_mapsto_adt ext tenv vtmp ->
    GLabelMap.find fWrite16 env = Some (Axiomatic BytesADTSpec.Push) ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      pArg
    {{ [[ ` vstream ->> stream as _]]::[[ ` varg ->> n as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream ++ ` n as _]]::tenv' }}
      pNext
    {{ [[ ` vstream ->> stream ++ ` n as _]]::tenv'' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      Seq pArg (Seq (Call vtmp fWrite16 [vstream; varg]) pNext)
    {{ [[ ` vstream ->> stream ++ ` n as _]]::tenv'' }} ∪ {{ ext }} // env.
Proof.
  hoare.
  hoare.
  hoare.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).

  wipe.
  LiftPropertyToTelescope_t.

Admitted.

Lemma CompileCallWrite16_EncodeAndPad:
  forall (vtmp varg vstream : string) (stream : list bool) (tenv tenv' tenv'': Telescope ADTValue)
    (n : BoundedN 16) ext env
    pArg pNext fWrite16,
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      pArg
    {{ [[ ` vstream ->> stream as _]]::[[ ` varg ->> n as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream ++ ` (EncodeAndPad n) as _]]::tenv' }}
      pNext
    {{ [[ ` vstream ->> stream ++ ` (EncodeAndPad n) as _]]::tenv'' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      Seq pArg (Seq (Call vtmp fWrite16 [vstream; varg]) pNext)
    {{ [[ ` vstream ->> stream ++ ` (EncodeAndPad n) as _]]::tenv'' }} ∪ {{ ext }} // env.
Proof.
  intros * H ?.
  setoid_rewrite (TelEq_same_wrap _ _ (WrapN16_WrapListBool16 _)) in H.
  eapply CompileCallWrite16; eauto.
Qed.

Ltac _compile_CallWrite :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let post' := (eval simpl in post) in
            lazymatch post' with
            | Cons _ (ret (_ ++ ` ?arg)) _ =>
              let vtmp := gensym "tmp" in
              let varg := gensym "arg" in
              match arg with
              | EncodeAndPad _ => first [ eapply (CompileCallWrite8_EncodeAndPad vtmp varg) |
                                         eapply (CompileCallWrite16_EncodeAndPad vtmp varg) ]
              | _ => first [ eapply (CompileCallWrite8 vtmp varg) |
                            eapply (CompileCallWrite16 vtmp varg) ]
              end
            end).
