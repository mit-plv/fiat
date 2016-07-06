Require Import Benchmarks.MicroEncodersSetup.

(* FIXME why isn't the require export in MicroEncodersSetup working? *)
Require Export
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.BinEncoders.Env.Automation.SolverOpt
        Fiat.BinEncoders.Env.BinLib.Bool
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.BinLib.Enum
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.Common.ComposeCheckSum
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Lib.FixList
        Fiat.BinEncoders.Env.Lib.IList
        Fiat.BinEncoders.Env.Lib2.Bool
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.NoCache
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.IPChecksum.

Notation "x 'ThenC' y" := (compose _ x y).
Notation "x 'DoneC'"   := (x ThenC fun e => (transform_id, e)).

Open Scope list_scope.

Hint Rewrite EncodeBoundedNat8_simplify :  f2f_binencoders_autorewrite_db.
Hint Rewrite ByteString_transformer_eq_app : f2f_binencoders_autorewrite_db.
Hint Resolve WrapByte_BoundedNat8ToByte_WrapNat8_compat : compile_do_side_conditions_db.

Ltac _compile_SameWrap :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | [[ ?k ->> BoundedNat8ToByte ?w as _ ]] :: ?tail =>
              rewrite (TelEq_same_wrap (BoundedNat8ToByte w) w)
            end).

Ltac _compile_decide_padding_0 :=
  repeat first [ reflexivity |
                 apply ByteString_transform_padding_0 |
                 eapply EncodeBoundedNat8_padding_0 ].

(* FIXME remove coercions? *)
Transparent nat_as_word.

Ltac _compile_decide_AllocString_size :=
  unfold nat_as_word;
  match goal with
  | [  |- natToWord ?sz ?z = ?x ^* natToWord ?sz ?y ] =>
    let zz := (eval compute in (NPeano.div z y)) in
    unify x (natToWord sz zz); reflexivity
  end.

Ltac _compile_decide_write8_side_condition :=
  repeat lazymatch goal with
         | [ H := _ |- _ ] => unfold H in *; clear H
         | [  |- context[List.length (byteString (?x))] ] =>
           match x with
           | transform_id => change (length (byteString transform_id)) with 0
           | fst (EncodeBoundedNat _ _) => rewrite EncodeBoundedNat8_length
           | transform _ _ => rewrite ByteString_transform_length by _compile_decide_padding_0
           end
         | _ => omega
         end.

Ltac _compile_encode_do_side_conditions :=
  match goal with
  | [  |- _ = _ ^* _ ] => _compile_decide_AllocString_size
  | [  |- padding _ = 0 ] => _compile_decide_padding_0
  | [  |- (List.length (byteString (?x)) + 1 <= _)%nat ] => _compile_decide_write8_side_condition
  end.

Ltac compile_encoder_step ::=
   (* try _encode_show_progress; *)
   match goal with
   | _ => _encode_start_compiling
   | _ => _encode_cleanup
   | _ => _compile_encode_do_side_conditions
   | _ => _encode_prepare_cache
   | _ => _encode_FixInt
   | _ => _encode_IList_compile
   | _ => _compile_CallWrite
   | _ => _compile_Read
   | _ => _compile_SameWrap
   (* | _ => _compile_ReadConstantN *)
   (* | _ => _compile_CallAdd16 *)
   | _ => _compile_CallListLength
   | _ => _compile_CallAllocString
   (* | _ => _compile_CallAllocOffset *)
   | _ => _compile_compose
   | _ => _compile_step
   end.


Record FourWords :=
  { w0 : BoundedNat 8;
    w1 : BoundedNat 8;
    w2 : BoundedNat 8;
    w3 : BoundedNat 8 }.

Definition FourWords_encode (t : FourWords) :=
byteString
  (fst ( ((EncodeBoundedNat t.(w0)
   ThenC EncodeBoundedNat t.(w1)
   ThenC EncodeBoundedNat t.(w2)
   ThenC EncodeBoundedNat t.(w3)
  DoneC) ()))) : list byte.

Definition FourWordsAsCollectionOfVariables
  {av} vw0 vw1 vw2 vw3 t
  : Telescope av :=
  [[ vw0 ->> t.(w0) as _ ]] ::
  [[ vw1 ->> t.(w1) as _ ]] ::
  [[ vw2 ->> t.(w2) as _ ]] ::
  [[ vw3 ->> t.(w3) as _ ]] :: Nil.

Hint Unfold FourWords_encode : f2f_binencoders_autorewrite_db.
Hint Unfold FourWordsAsCollectionOfVariables : f2f_binencoders_autorewrite_db.

Example FourWords_compile :
  let wrapper := @WrapListByte (natToWord _ 512) in
  ParametricExtraction
    #vars      fourWords
    #program   ret (FourWords_encode fourWords)
    #arguments (FourWordsAsCollectionOfVariables
                  (NTSome "w0") (NTSome "w1") (NTSome "w2") (NTSome "w3") fourWords)
    #env       MicroEncoders_Env.
Proof.
  Time compile_encoder_t.
  repeat (apply CompileDeallocSCA_discretely; try compile_encoder_t).
Defined.

Eval lazy in (extract_facade FourWords_compile).

Print Assumptions FourWords_compile.

Definition BoundedListLength {A size} (ls : BoundedList A (pow2 size)) : BoundedNat size :=
  exist _ (length (` ls)) (proj2_sig ls).

Lemma map_inj {A B}:
  forall (f: A -> B),
    (forall x y, f x = f y -> x = y) ->
    (forall x y, (map f) x = (map f) y -> x = y).
Proof.
  induction x; destruct y; simpl; intros HH; try congruence.
  inversion' HH; f_equal; eauto.
Qed.

Instance WrapList {A B} {Wrp: FacadeWrapper A B} : FacadeWrapper (list A) (list B).
Proof.
  refine {| wrap x := map wrap x |}.
  abstract (eauto using map_inj, wrap_inj).
Defined.

Lemma WrapBoundedList_inj_1:
  forall (B : Type) (size : nat) (v v' : BoundedList B size), ` v = ` v' -> v = v'.
Proof.
  intros.
  apply exist_irrel'.
  - intros; apply lt_uniqueness_proof.
  - eassumption.
Qed.

Lemma WrapBoundedList_inj {A B : Type} {size : nat} {Wrp : FacadeWrapper A (list B)}:
  forall (v v' : BoundedList B size),
    wrap (` v) = wrap (` v') ->
    v = v'.
Proof.
  intros * H; apply wrap_inj, WrapBoundedList_inj_1 in H; assumption.
Qed.

Lemma WrapTransitive {A A' A''}
      {WrpVal: FacadeWrapper A A'}
      {WrpList: FacadeWrapper A' A''}
  : FacadeWrapper A A''.
Proof.
  refine {| wrap a'' := wrap (wrap a'');
            wrap_inj := _ |}.
  abstract (intros * H; repeat apply wrap_inj in H; assumption).
Defined.

Instance WrapBoundedList {A B size} {Wrp: FacadeWrapper A (list B)} : FacadeWrapper A (BoundedList B size) :=
  {| wrap bl := wrap (`bl);
     wrap_inj := WrapBoundedList_inj |}.

Typeclasses eauto := 10.

Instance WrapWordList : FacadeWrapper ADTValue (list W).
Proof.
  refine {| wrap tl := WordList tl;
            wrap_inj := _ |}; abstract (inversion 1; reflexivity).
Defined.

Instance WrapBoundedListOfBoundedNat {sl} : FacadeWrapper (Value ADTValue) (BoundedList (BoundedNat 8) sl).
Proof.
  eapply @WrapTransitive.
  - apply @WrapInstance.
    apply @WrapWordList.
  - apply @WrapBoundedList.
    apply @WrapList.
    apply @WrapNatIntoW8.
Defined.

Eval compute in WrapBoundedListOfBoundedNat.

Record MixedRecord :=
  { f1 : byte;
    f2 : BoundedNat 8;
    f3 : BoundedList (BoundedNat 8) (pow2 8) }.

Definition MixedRecord_encode (mr: MixedRecord) :=
  byteString
    (fst (((encode_word_Impl WO~0~0~1~0~1~0~1~0)
     ThenC (encode_word_Impl mr.(f1))
     ThenC (EncodeBoundedNat mr.(f2))
     ThenC (EncodeBoundedNat (BoundedListLength mr.(f3)))
     ThenC (encode_list_Impl EncodeBoundedNat (projT1 mr.(f3)))) tt)) : list byte.

Definition MixedRecordAsCollectionOfVariables
  {av} vf1 vf2 vf3 ll : Telescope av :=
  [[ vf1 ->> ll.(f1) as _ ]] ::
  [[ vf2 ->> ll.(f2) as _ ]] ::
  [[ vf3 ->> ll.(f3) as _ ]] :: Nil.

Hint Unfold MixedRecord_encode : f2f_binencoders_autorewrite_db.
Hint Unfold MixedRecordAsCollectionOfVariables : f2f_binencoders_autorewrite_db.

Example MixedRecord_compile :
  let wrapper := @WrapListByte (natToWord _ 512) in
  ParametricExtraction
    #vars      mixedRecord
    #program   ret (MixedRecord_encode mixedRecord)
    #arguments (MixedRecordAsCollectionOfVariables
                  (NTSome "f1") (NTSome "f2") (NTSome "f3") mixedRecord)
    #env       MicroEncoders_Env.
Proof.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  2:compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.

  Lemma encode_byte_simplify : (* {cache} {cacheAddNat : CacheAdd cache nat} : *)
    forall (w: byte), (* (c: @CacheEncode cache), *)
      encode_word_Impl w tt =
      ({| padding := 0; front := WO; paddingOK := Lt.lt_0_Sn 7; byteString := w :: nil |}, addE tt 8).
  Proof.
    unfold encode_word_Impl; intros.
    rewrite encode_char'; reflexivity.
  Qed.

  rewrite encode_byte_simplify.

  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  Focus 3.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.

  Lemma CompileConstant_SCA:
    forall {av A} {Wr: FacadeWrapper (Value av) A}
      name env (w: A) ext (tenv: Telescope av),
      name ∉ ext ->
      NotInTelescope name tenv ->
      (forall a : A, is_adt (wrap a) = false) ->
      {{ tenv }}
        (Assign name (Const (match wrap w with SCA w => w | _ => W0 end)))
      {{ [[`name ->> w as _]]::tenv }} ∪ {{ ext }} // env.
  Proof.
    intros * ? ? not_adt;
      destruct (not_adt_is_sca not_adt) as (skol & Heq).
    rewrite (Heq w) in *.
    rewrite (TelEq_same_wrap _ (skol w)) by eauto.
    apply CompileConstant; assumption.
  Qed.

  apply CompileConstant_SCA.
  (* compile_constant value *)
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.

  rewrite encode_byte_simplify.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.

  (* Add to properties *)
  Lemma encode_word8_Impl_length :
    forall (w: byte),
      List.length (byteString (fst (encode_word_Impl w tt))) = 1.
  Proof.
    unfold encode_word_Impl; intros; rewrite encode_char'; reflexivity.
  Qed.

  Ltac _compile_decide_write8_side_condition ::=
    repeat lazymatch goal with
           | [ H := _ |- _ ] => unfold H in *; clear H
           | [  |- context[List.length (byteString (?x))] ] =>
             match x with
             | transform_id => change (length (byteString transform_id)) with 0
             | fst (EncodeBoundedNat _ _) => rewrite EncodeBoundedNat8_length
             | fst (encode_word_Impl _ _) => rewrite encode_word8_Impl_length
             | transform _ _ => rewrite ByteString_transform_length by _compile_decide_padding_0
             | _ => fail 3 "Unrecognized form" x
             end
           | _ => omega
           end.

  Opaque encode_word_Impl.
  compile_encoder_step.
  compile_encoder_step.

  Focus 3.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  2: solve [compile_encoder_t].
  2: solve [compile_encoder_t].
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.

  Transparent encode_word_Impl.
  Lemma encode_word8_Impl_padding_0 : (* {cache} {cacheAddNat : CacheAdd cache nat} : *)
    forall (w: byte), (* (c: @CacheEncode cache), *)
      padding (fst (encode_word_Impl w tt)) = 0.
  Proof.
    unfold encode_word_Impl; intros; rewrite encode_char'; reflexivity.
  Qed.
  Opaque encode_word_Impl.

  Ltac _compile_decide_padding_0 ::=
  repeat first [ reflexivity |
                 apply ByteString_transform_padding_0 |
                 eapply encode_word8_Impl_padding_0 |
                 eapply EncodeBoundedNat8_padding_0 ].

  compile_encoder_step.

  Focus 3.

  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.

  compile_encoder_step.
  compile_encoder_step.
  2: solve [compile_encoder_t].
  2: solve [compile_encoder_t].
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.

  Focus 3.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  2:compile_encoder_t.

Lemma CompileCallListSCALength {A}:
  forall {WrpList: FacadeWrapper (Value ADTValue) (BoundedList A (pow2 8))}
    (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (lst : BoundedList A (pow2 8))
    fLength tenv',
    PreconditionSet tenv' ext [[[vlst;varg]]] ->
    (exists sk: _ -> list W,
        (forall ls: BoundedList A (pow2 8),
            wrap ls = ADT (WordList (sk ls))) /\
        (forall ls: BoundedList A (pow2 8),
            List.length (sk ls) = List.length (`ls))) ->
    GLabelMap.MapsTo fLength (Axiomatic WordListADTSpec.Length) env ->
    TelEq ext tenv ([[`vlst ->> lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *)
    {{ tenv }}
      Call varg fLength [vlst]
    {{ [[ ` varg ->> BoundedListLength lst as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros * ? ? (? & wrap_eq & length_eq) ? Heq; setoid_rewrite Heq; PreconditionSet_t;
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || rewrite wrap_eq in *).
  facade_eauto.
  facade_eauto.
  repeat match goal with
         | [ H: ?a = ?a |- _ ] => clear dependent H
         | [ H: ADT (WordList (_ _)) = ADT _ |- _ ] => inversion' H
         end; rewrite length_eq; reflexivity.
  facade_eauto.
  rewrite remove_remove_comm by assumption; facade_eauto.
Qed.

Lemma CompileCallListBoundedNatLength:
  forall (vlst varg : string) (tenv : Telescope ADTValue) (ext : StringMap.t (Value ADTValue))
    env (lst : BoundedList (BoundedNat 8) (pow2 8))
    fLength tenv',
    PreconditionSet tenv' ext [[[vlst;varg]]] ->
    GLabelMap.MapsTo fLength (Axiomatic WordListADTSpec.Length) env ->
    TelEq ext tenv ([[`vlst ->> lst as _]]::tenv') -> (* Experiment to require a-posteriori reordering of variables *)
    {{ tenv }}
      Call varg fLength [vlst]
    {{ [[ ` varg ->> BoundedListLength lst as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  eapply CompileCallListSCALength; eauto.
  eexists; split.
  - reflexivity.
  - setoid_rewrite map_length; reflexivity.
Qed.


Ltac _compile_CallListLength ::=
  match_ProgOk
    ltac:(fun _ _ post _ _ =>
            match post with
            | [[ _ ->> BoundedListLength ?lst as _]] :: _ =>
              let vlst := find_name_in_precondition lst in
              (* FIXME use this instead of explicit continuations in every lemma *)
              compile_do_use_transitivity_to_handle_head_separately;
              [ eapply (CompileCallListBoundedNatLength vlst) | ]
            end).

  compile_encoder_step.
  3: compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  compile_encoder_step.
  2:compile_encoder_step.
  2:compile_encoder_step.



Record BitArrayAndList :=
  { f1 : BitArray 8;
    f2 : { l : list {n : N | (n < exp2 8)%N} | List.length l < exp2_nat 8} } .

Definition BitArrayAndList_encode (t : BitArrayAndList) :=
  fst ((IList.IList_encode Bool.Bool_encode (f1 t)
   Then FixInt_encode (FixList_getlength (f2 t))
   Then FixList_encode FixInt_encode (f2 t)
   Then (fun e => (nil, e))) tt).

Require Import Coq.Program.Program.

Definition BitArrayAndListAsCollectionOfVariables
  {av} vf1 vf2 ll
  : Telescope av :=
  [[ vf1 ->> ll.(f1) as _ ]] ::
  [[ vf2 ->> `ll.(f2) as _ ]] :: Nil.

Hint Unfold BitArrayAndList_encode : f2f_binencoders_autorewrite_db.
Hint Unfold BitArrayAndListAsCollectionOfVariables : f2f_binencoders_autorewrite_db.
Hint Rewrite (@IList_encode'_body_simpl empty_cache) : f2f_binencoders_autorewrite_db.

Example BitArrayAndList_compile :
  ParametricExtraction
    #vars      bitArrayAndList
    #program   ret (BitArrayAndList_encode bitArrayAndList)
    #arguments (BitArrayAndListAsCollectionOfVariables
                  (NTSome "f1") (NTSome "f2") bitArrayAndList)
    #env       MicroEncoders_Env.
Proof.
  compile_encoder_t.
  repeat (apply CompileDeallocSCA_discretely; try compile_encoder_t).  (* TODO automate *)
  repeat (apply CompileDeallocSCA_discretely; try compile_encoder_t).
  Grab Existential Variables.
  repeat constructor.
  repeat constructor.
  repeat constructor.
Defined.

Eval lazy in (extract_facade BitArrayAndList_compile).

