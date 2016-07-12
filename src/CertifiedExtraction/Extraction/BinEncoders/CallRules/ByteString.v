Require Export
        Fiat.CertifiedExtraction.Extraction.Extraction.

Require Import
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Basics
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Wrappers
        Fiat.CertifiedExtraction.Extraction.BinEncoders.Properties.

Require Import
        Coq.Program.Program
        Coq.Lists.List.

Unset Implicit Arguments.

Lemma CompileCallAllocString {real_capacity}:
  forall (vcapacity vstream : string) (tenv tenv' : Telescope ADTValue)
    ext (env : GLabelMap.t (FuncSpec ADTValue)) capacity,
    let Wrp := WrapInstance (H := (@WrapListByte real_capacity)) in
    forall pNext pArg fAllocString,
      vcapacity <> vstream ->
      vstream ∉ ext ->
      NotInTelescope vstream tenv ->
      IL.goodSize (2 + Word.wordToNat capacity * 4) ->
      real_capacity = Word.wmult capacity (Word.natToWord 32 4) ->
      GLabelMap.MapsTo fAllocString (Axiomatic BytesADTSpec.New) env ->
      {{ [[ NTSome (H := Wrp) vstream ->> nil as _]]::tenv }}
        pNext
      {{ [[ NTSome (H := Wrp) vstream ->> nil as _]]::tenv' }} ∪ {{ ext }} // env ->
      {{ tenv }}
        pArg
      {{ [[ ` vcapacity ->> capacity as _ ]] :: tenv }} ∪ {{ ext }} // env ->
      {{ tenv }}
        Seq (Seq pArg (Call vstream fAllocString [vcapacity])) pNext
      {{ [[ NTSome (H := Wrp) vstream ->> nil as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare; hoare.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  facade_eauto.
  facade_eauto.
  congruence.
  facade_eauto.
  facade_eauto.
Qed.

Ltac _compile_CallAllocString :=
  may_alloc_head;
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocString vtmp).

Lemma IL_BtoW_BtoW :
  forall b: byte,
    IL.BtoW b = BtoW b.
Proof.
  intros; shatter_word b.
  reflexivity.
Qed.

Lemma CompileCallWrite8_base capacity :
  let Wrp := WrapInstance (H := @WrapListByte capacity) in
  forall (vtmp varg vstream : string) (stream : list byte)
    (n : byte) fWrite8 tenv ext env,
    (List.length stream + 1 <= wordToNat capacity)%nat ->
    GLabelMap.MapsTo fWrite8 (Axiomatic BytesADTSpec.Push) env ->
    Lifted_MapsTo ext tenv vstream (wrap (FacadeWrapper := Wrp) stream) ->
    Lifted_MapsTo ext tenv varg (wrap n) ->
    vtmp <> vstream ->
    vtmp ∉ ext ->
    vstream ∉ ext ->
    Lifted_not_mapsto_adt ext tenv vtmp ->
    {{ tenv }}
      Call vtmp fWrite8 (vstream :: varg :: nil)
    {{ [[ `vtmp ->> (Word.natToWord 32 0) as _ ]]
        :: [[ NTSome (H := Wrp) vstream ->> stream ++ n :: nil as _ ]] ::
        DropName vstream (DropName vtmp tenv) }} ∪ {{ ext }} // env.
Proof.
  intros.
  repeat match goal with
         | _ => progress (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t)
         | [  |- context[IL.BtoW ?x] ] => rewrite (IL_BtoW_BtoW x)
         | [ H: context[IL.BtoW ?x] |- _ ] => rewrite (IL_BtoW_BtoW x) in H
         | [ H: BtoW _ = BtoW _ |- _ ] => learn (BtoW_inj _ _ H); subst
         end.
  facade_eauto.
  facade_eauto.
  repeat apply DropName_remove; facade_eauto.
Qed.

Lemma CompileCallWrite8 capacity :
  let Wrp := WrapInstance (H := @WrapListByte capacity) in
  forall (vtmp varg vstream : string) (stream : list byte)
    (tenv tenv' tenv'': Telescope ADTValue)
    (n : byte) ext env
    pArg pNext fWrite8,
    (List.length stream + 1 <= wordToNat capacity)%nat ->
    PreconditionSet tenv' ext [[[vtmp; vstream; varg]]] ->
    GLabelMap.MapsTo fWrite8 (Axiomatic BytesADTSpec.Push) env ->
    {{ [[ NTSome (H := Wrp) vstream ->> stream as _]]::tenv }}
      pArg
    {{ [[ NTSome (H := Wrp) vstream ->> stream as _]]::[[ ` varg ->> n as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ [[ NTSome (H := Wrp) vstream ->> stream ++ n :: nil as _]]::tenv' }}
      pNext
    {{ [[ NTSome (H := Wrp) vstream ->> stream ++ n :: nil as _]]::tenv'' }} ∪ {{ ext }} // env ->
    {{ [[ NTSome (H := Wrp) vstream ->> stream as _]]::tenv }}
      Seq pArg (Seq (Call vtmp fWrite8 [vstream; varg]) pNext)
    {{ [[ NTSome (H := Wrp) vstream ->> stream ++ n :: nil as _]]::tenv'' }} ∪ {{ ext }} // env.
Proof.
  hoare; hoare; hoare.

  PreconditionSet_t;
    apply ProgOk_Remove_Skip_R; hoare;
      [ apply generalized CompileCallWrite8_base | ];
      repeat repeat match goal with
                    | _ => progress intros
                    | _ => apply ProgOk_Chomp_Some
                    | _ => apply CompileDeallocSCA_discretely
                    | _ => progress (compile_do_side_conditions || Lifted_t)
                    end; (assumption || apply CompileSkip).
Qed.

Ltac _compile_CallWrite :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let post' := (eval simpl in post) in
            lazymatch post' with
            | Cons _ (ret (_ ++ ?arg :: nil)) _ =>
              let vtmp := gensym "tmp" in
              let varg := gensym "arg" in
              eapply (CompileCallWrite8 _ vtmp varg)
            end).

