Require Import Benchmarks.MicroEncodersSetup.


Require Import Fiat.BinEncoders.Env.Common.Compose.

Record FourWords :=
  { w0 : BoundedNat 8;
    w1 : BoundedNat 8;
    w2 : BoundedNat 8;
    w3 : BoundedNat 8 }.

Notation "x 'ThenC' y" := (compose _ x y).
Notation "x 'DoneC'"   := (x ThenC fun e => (transform_id, e)).

Definition ListOfNat_encode (ls : BoundedList (BoundedNat 8) 256) :=
  fst (((encode_word_Impl WO~0~0~1~0~1~0~1~0) ThenC
        (encode_nat_Impl 8 (length (projT1 ls))) ThenC
        (encode_list_Impl (fun n : BoundedNat _ => encode_nat_Impl 8 (projT1 n)) (projT1 ls))) tt).
Section Nat.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  Definition EncodeBoundedNat {k} (n : BoundedNat k) (ce : CacheEncode) : B * CacheEncode :=
    (* NToWord + N.of_nat needed for performance (otherwise apply doesn't terminate) *)
    encode_word_Impl (@NToWord k (N.of_nat (`n))) ce.
End Nat.

Definition FourWords_encode (t : FourWords) :=
byteString
  (fst ( ((EncodeBoundedNat t.(w0)
   ThenC EncodeBoundedNat t.(w1)
   ThenC EncodeBoundedNat t.(w2)
   ThenC EncodeBoundedNat t.(w3)
  DoneC) ()))) : list byte.

(* Open Scope binencoders_scope. *)

Definition FourWordsAsCollectionOfVariables
  {av} vw0 vw1 vw2 vw3 t
  : Telescope av :=
  [[ vw0 ->> t.(w0) as _ ]] ::
  [[ vw1 ->> t.(w1) as _ ]] ::
  [[ vw2 ->> t.(w2) as _ ]] ::
  [[ vw3 ->> t.(w3) as _ ]] :: Nil.

Hint Unfold FourWords_encode : f2f_binencoders_autorewrite_db.
Hint Unfold FourWordsAsCollectionOfVariables : f2f_binencoders_autorewrite_db.

Lemma CompileCallAllocString {real_capacity}: (* FIXME replace existing with this *)
  forall (vcapacity vstream : string) (tenv tenv' : Telescope ADTValue)
    ext (env : GLabelMap.t (FuncSpec ADTValue)) capacity,
    let wrapper := WrapInstance (H := (@WrapListByte real_capacity)) in
    forall pNext pArg fAllocString,
      vcapacity <> vstream ->
      vstream ∉ ext ->
      NotInTelescope vstream tenv ->
      IL.goodSize (2 + Word.wordToNat capacity * 4) ->
      real_capacity = Word.wmult capacity (Word.natToWord 32 4) ->
      GLabelMap.MapsTo fAllocString (Axiomatic BytesADTSpec.New) env ->
      {{ [[ ` vstream ->> nil as _]]::tenv }}
        pNext
      {{ [[ ` vstream ->> nil as _]]::tenv' }} ∪ {{ ext }} // env ->
      {{ tenv }}
        pArg
      {{ [[ ` vcapacity ->> capacity as _ ]] :: tenv }} ∪ {{ ext }} // env ->
      {{ tenv }}
        Seq (Seq pArg (Call vstream fAllocString [vcapacity])) pNext
      {{ [[ ` vstream ->> nil as _]]::tenv' }} ∪ {{ ext }} // env.
Proof.
Admitted.

Lemma encode_char' :
  forall w, encode_word' 8 w =
       {| front := WO;
          paddingOK := Lt.lt_0_Sn _;
          byteString := w :: nil |}.
Proof.
  intros; change 8 with (8+0); rewrite encode_char.
  shatter_word w; simpl; rewrite ByteString_transform_id_right.
  reflexivity.
Qed.

Definition BoundedNat8ToByte (w: BoundedNat 8) :=
  natToWord 8 (`w).

Lemma EncodeBoundedNat8_simplify : (* {cache} {cacheAddNat : CacheAdd cache nat} : *)
  forall (w: BoundedNat 8), (* (c: @CacheEncode cache), *)
    EncodeBoundedNat w tt =
    ({| padding := 0; front := WO; paddingOK := Lt.lt_0_Sn 7; byteString := (BoundedNat8ToByte w :: nil) |}, addE tt 8).
Proof.
  unfold EncodeBoundedNat, encode_word_Impl; intros.
  rewrite encode_char', NToWord_of_nat.
  reflexivity.
Qed.

Lemma zext_inj {sz} {sz'} :
  forall (w w' : word sz),
    (zext w sz') = (zext w' sz') ->
    w = w'.
Proof.
  unfold zext; intros * H.
  apply (f_equal (@Word.split1 _ _)) in H.
  rewrite !split1_combine in H.
  assumption.
Qed.

Definition BtoW (b: B) : W :=
  (zext b 24).

Lemma BtoW_inj :
  forall (v v' : byte),
    BtoW v = BtoW v' ->
    v = v'.
Proof.
  intros; eapply zext_inj; apply H.
Qed.

Lemma WrapByte_inj {av} :
  forall (v v' : byte),
    SCA av (BtoW v) = SCA av (BtoW v') -> v = v'.
Proof.
  inversion 1; eauto using BtoW_inj.
Qed.

Instance WrapByte {av} : FacadeWrapper (Value av) byte :=
  {| wrap b := SCA _ (BtoW b);
     wrap_inj := WrapByte_inj |}.

Ltac facade_cleanup_call ::=
     match goal with
     | _ => progress cbv beta iota delta [add_remove_many] in *
     | _ => progress cbv beta iota delta [sel] in *
     | [ H: Axiomatic ?s = Axiomatic ?s' |- _ ] => inversion H; subst; clear dependent H
     | [ H: PreCond ?f _ |- _ ] => let hd := head_constant f in unfold hd in H; cbv beta iota delta [PreCond] in H
     | [ H: PostCond ?f _ _ |- _ ] => let hd := head_constant f in unfold hd in H; cbv beta iota delta [PostCond] in H
     | [  |- PreCond ?f _ ] => let hd := head_constant f in unfold hd; cbv beta iota delta [PreCond]
     | [  |- PostCond ?f _ _ ] => let hd := head_constant f in unfold hd; cbv beta iota delta [PostCond]
     | [ H: WeakEq ?lhs _ |- _ ] => progress learn_all_WeakEq_remove H lhs
     | [ |- context[ListFacts4.mapM] ] => progress simpl ListFacts4.mapM
     | [ H: context[ListFacts4.mapM] |- _ ] => progress simpl ListFacts4.mapM in H
     | [ H: List.combine ?a ?b = _, H': List.length ?a = List.length ?b |- _ ] => learn (combine_inv a b H' H)
     | [ |-  context[List.split (cons _ _)] ] => simpl
     | [ H: context[List.split (cons _ _)] |- _ ] => may_touch H; simpl in H
     | [ H: List.cons _ _ = List.cons _ _ |- _ ] =>
       (* Not using inversion: it sometimes loops *)
       let heads_eq := fresh in
       destruct (List_cons_inj H) as (heads_eq & ?);
       pose proof heads_eq;    (* Make a copy for cases where inversion goes berzerk *)
       inversion heads_eq; try subst; clear dependent H
     | _ => GLabelMapUtils.normalize
     | _ => solve [GLabelMapUtils.decide_mapsto_maybe_instantiate]
     | [  |- exists _, _ ] => eexists
     end.

Open Scope list_scope.

Lemma CompileCallWrite8_base capacity :
  let wrapper := @WrapListByte capacity in
  forall (vtmp varg vstream : string) (stream : list byte)
    (n : byte) fWrite8 tenv ext env,
    (List.length stream + 1 <= wordToNat capacity)%nat ->
    GLabelMap.MapsTo fWrite8 (Axiomatic BytesADTSpec.Push) env ->
    Lifted_MapsTo ext tenv vstream (wrap stream) ->
    Lifted_MapsTo ext tenv varg (wrap n) ->
    vtmp <> vstream ->
    vtmp ∉ ext ->
    vstream ∉ ext ->
    Lifted_not_mapsto_adt ext tenv vtmp ->
    (* Lifted_not_mapsto_adt ext tenv vtmp -> *)
    (* varg <> vstream -> *)
    (* vtmp <> vstream -> *)
    (* vtmp <> varg -> *)
    (* vtmp ∉ ext -> *)
    (* vstream ∉ ext -> *)
    {{ tenv }}
      Call vtmp fWrite8 (vstream :: varg :: nil)
    {{ [[ `vtmp ->> W0 as _ ]]
        :: [[ `vstream ->> stream ++ n :: nil as _ ]] ::
        DropName vstream (DropName vtmp tenv) }} ∪ {{ ext }} // env.
Proof.
  intros.
  repeat match goal with
         | _ => progress (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t)
         | [  |- context[IL.BtoW] ] => replace IL.BtoW with BtoW by (clear; admit)
         | [ H: context[IL.BtoW] |- _ ] => replace IL.BtoW with BtoW in H by (clear; admit)
         | [ H: BtoW _ = BtoW _ |- _ ] => learn (BtoW_inj _ _ H); subst
         end.
  facade_eauto.
  facade_eauto.
  repeat apply DropName_remove; facade_eauto.
Qed.

Lemma CompileCallWrite8 capacity :
  let wrapper := @WrapListByte capacity in
  forall (vtmp varg vstream : string) (stream : list byte)
    (tenv tenv' tenv'': Telescope ADTValue)
    (n : byte) ext env
    pArg pNext fWrite8,
    ((|stream |) + 1 <= wordToNat capacity)%nat ->
    PreconditionSet tenv' ext [[[vtmp; vstream; varg]]] ->
    GLabelMap.MapsTo fWrite8 (Axiomatic BytesADTSpec.Push) env ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      pArg
    {{ [[ ` vstream ->> stream as _]]::[[ ` varg ->> n as _]]::tenv' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream ++ n :: nil as _]]::tenv' }}
      pNext
    {{ [[ ` vstream ->> stream ++ n :: nil as _]]::tenv'' }} ∪ {{ ext }} // env ->
    {{ [[ ` vstream ->> stream as _]]::tenv }}
      Seq pArg (Seq (Call vtmp fWrite8 [vstream; varg]) pNext)
    {{ [[ ` vstream ->> stream ++ n :: nil as _]]::tenv'' }} ∪ {{ ext }} // env.
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

Lemma wordToNat_inj {sz} :
  forall (w1 w2: word sz),
    wordToNat w1 = wordToNat w2 ->
    w1 = w2.
Proof.
  intros * H.
  apply (f_equal (@natToWord sz)) in H.
  rewrite !natToWord_wordToNat in H.
  assumption.
Qed.

Lemma BoundedN_BoundedNat {sz} :
  forall x, lt x (pow2 sz) -> N.lt (N.of_nat x) (Npow2 sz).
Proof.
  intros.
  apply Nomega.Nlt_in.
  rewrite Nat2N.id, Npow2_nat.
  assumption.
Qed.

Lemma BtoW_BoundedNat8ToByte_natToWord :
  forall w,
    BtoW (BoundedNat8ToByte w) = natToWord 32 (` w).
Proof.
  intros; apply wordToN_inj.
  unfold BoundedNat8ToByte, BtoW, zext.
  rewrite (InternetChecksum.wordToN_extend 8 24).
  destruct w as (? & pr); rewrite !IL.natToWordToN.
  - reflexivity.
  - simpl; apply BoundedN_BoundedNat in pr;
    etransitivity; eauto; reflexivity.
  - apply BoundedN_BoundedNat; assumption.
Qed.

Lemma WrapByte_BoundedNat8ToByte_WrapNat8_compat :
  forall w,
    wrap (BoundedNat8ToByte w) = wrap w.
Proof.
  intros.
  unfold wrap, WrapByte.
  rewrite BtoW_BoundedNat8ToByte_natToWord; reflexivity.
Qed.

Lemma ByteString_transform_padding_0_left :
  forall str1 str2,
    padding str1 = 0 ->
    padding (transform str1 str2) = padding str2.
Proof.
  intros * H; rewrite transform_padding_eq, H.
  apply NPeano.Nat.mod_small.
  destruct str2; assumption.
Qed.

Lemma ByteString_transform_padding_0 :
  forall str1 str2,
    padding str1 = 0 ->
    padding str2 = 0 ->
    padding (transform str1 str2) = 0.
Proof.
  intros * H H'; rewrite transform_padding_eq, H, H'.
  reflexivity.
Qed.

Lemma EncodeBoundedNat8_padding_0 : (* {cache} {cacheAddNat : CacheAdd cache nat} : *)
  forall (w: BoundedNat 8), (* (c: @CacheEncode cache), *)
    padding (fst (EncodeBoundedNat w tt)) = 0.
Proof.
  intros; rewrite EncodeBoundedNat8_simplify; reflexivity.
Qed.

Lemma ProgOk_Add_snd_under_fn_ret :
  forall {A A' B av} (f: B -> Telescope av) (g: A -> A') (kfst: NameTag av _) (cpair: A * B) tenv tenv' ext env p1 p2,
    {{ tenv }}
      p1
      {{ [[ NTNone  ->>  cpair as pair ]]
          :: [[ kfst  ->> g (fst pair) as p1 ]]
          :: TelAppend (f (snd pair)) tenv' }} ∪ {{ ext }} // env ->
    {{ [[ NTNone  ->>  cpair as pair ]]
        :: [[ kfst  ->> g (fst pair) as p1 ]]
        :: TelAppend (f (snd pair)) tenv' }}
      p2
      {{ [[ NTNone  ->>  cpair as pair ]]
          :: [[ kfst  ->> g (fst pair) as p1 ]]
          :: TelAppend (Nil) tenv' }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq p1 p2)
      {{ [[ kfst  ->> g (fst cpair) as p1 ]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros; eapply CompileSeq; try eassumption.
  repeat setoid_rewrite Propagate_anonymous_ret.
  repeat setoid_rewrite Propagate_anonymous_ret in H.
  repeat setoid_rewrite Propagate_anonymous_ret in H0.
  assumption.
Qed.

Hint Rewrite EncodeBoundedNat8_simplify :  f2f_binencoders_autorewrite_db.
Hint Rewrite ByteString_transformer_eq_app : f2f_binencoders_autorewrite_db.
Hint Resolve WrapByte_BoundedNat8ToByte_WrapNat8_compat : compile_do_side_conditions_db.

Ltac _compile_CallWrite :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let post' := (eval simpl in post) in
            lazymatch post' with
            | Cons _ (ret (_ ++ ?arg :: nil)) _ =>
              let vtmp := gensym "tmp" in
              let varg := gensym "arg" in
              lazymatch arg with
              | BoundedNat8ToByte _ => eapply (CompileCallWrite8 _ vtmp varg)
              end
            end).

Ltac _compile_SameWrap :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            lazymatch post with
            | [[ ?k ->> BoundedNat8ToByte ?w as _ ]] :: ?tail =>
              rewrite (TelEq_same_wrap (BoundedNat8ToByte w) w)
            end).

Ltac _compile_CallAllocString ::=
  may_alloc_head;
  let vtmp := gensym "tmp" in
  eapply (CompileCallAllocString vtmp).

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

(* Lemma ByteString_length_transform_le : *)
(*   forall str1 str2 l1 l2 l, *)
(*     (l1 + l2 <= l)%nat -> *)
(*     padding str1 = 0 -> *)
(*     padding str2 = 0 -> *)
(*     (List.length (byteString str1) <= l1)%nat -> *)
(*     (List.length (byteString str2) <= l2)%nat -> *)
(*     (List.length (byteString (transform str1 str2)) <= l)%nat. *)
(* Proof. *)
(*   intros. *)
(*   unfold transform, ByteStringTransformer. *)
(*   rewrite ByteString_transformer_eq_app by assumption; simpl. *)
(*   rewrite app_length. *)
(*   omega. *)
(* Qed. *)

(* Open Scope nat_scope. *)

(* Lemma write8_side_condition_length_EncodeBoundedNat8 : *)
(*   forall x (w: BoundedNat 8), *)
(*     1 <= x -> *)
(*     List.length (byteString (fst (EncodeBoundedNat w tt))) <= x. *)
(* Proof. *)
(*   intros; rewrite EncodeBoundedNat8_simplify. *)
(*   assumption. *)
(* Qed. *)

(* Lemma write8_side_condition_plus_minus : *)
(*   forall n p, *)
(*     n <= p -> *)
(*     n + 1 <= S p. *)
(* Proof. *)
(*   intros; omega. *)
(* Qed. *)

(* Ltac t := *)
(*   match goal with *)
(*   |  |- context[wordToNat (natToWord _ (S ?x))] => change (wordToNat (natToWord _ (S x))) with (S x) *)
(*   |  |- List.length _ + 1 <= _ => apply write8_side_condition_plus_minus *)
(*   | _ => progress (change (length (byteString transform_id)) with 0) *)
(*   | _ => eapply ByteString_length_transform_le *)
(*   | _ => eapply write8_side_condition_length_EncodeBoundedNat8 *)
(*   |  |- padding _ = 0 => _compile_decide_padding_0 *)
(*   |  |- 0 <= _ => apply Le.le_refl *)
(*   |  |- S _ <= _ => apply Le.le_refl *)
(*   | _ => progress simpl (_ + _) *)
(*   | _ => omega *)
(*   end. *)

Open Scope nat_scope.

Lemma ByteString_transform_length :
  forall str1 str2,
    padding str1 = 0 ->
    padding str2 = 0 ->
    List.length (byteString (transform str1 str2)) =
    List.length (byteString str1) + List.length (byteString str2).
Proof.
  unfold transform, ByteStringTransformer; intros.
  rewrite ByteString_transformer_eq_app by assumption; simpl.
  rewrite app_length; reflexivity.
Qed.

Lemma EncodeBoundedNat8_length :
  forall (w: BoundedNat 8),
    List.length (byteString (fst (EncodeBoundedNat w tt))) = 1.
Proof.
  intros; rewrite EncodeBoundedNat8_simplify; reflexivity.
Qed.

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
  | [  |- List.length (byteString (?x)) + 1 <= _ ] => _compile_decide_write8_side_condition
  end.

Ltac _encode_prepare_cache ::=
  may_alloc_head; (* Only create bindings for the cache once. *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | Cons (NTSome _) (ret (byteString (fst (Compose.compose _ _ _ _)))) _ =>
              apply ProgOk_Add_snd_under_fn_ret with (f := fun _ => Nil)
            end).

Ltac _encode_cleanup ::=
  match goal with
  | _ => match_ProgOk
          ltac:(fun prog pre post ext env =>
                  match post with
                  | [[ ret (_, _) as _]] :: _ =>
                    apply Propagate_anonymous_ret__fast
                  end)
  | _ => progress simpl
  | _ => progress autounfold with f2f_binencoders_autorewrite_db
  | _ => progress autorewrite with f2f_binencoders_autorewrite_db
  | [  |- context[wordToNat (natToWord _ (S ?x))] ] => change (wordToNat (natToWord _ (S x))) with (S x)
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

Example FourWords_compile :
  let wrapper := @WrapListByte (natToWord _ 512) in
  ParametricExtraction
    #vars      fourWords
    #program   ret (FourWords_encode fourWords)
    #arguments (FourWordsAsCollectionOfVariables
                  (NTSome "w0") (NTSome "w1") (NTSome "w2") (NTSome "w3") fourWords)
    #env       MicroEncoders_Env.
Proof.
  intros.
  unfold FourWords_encode.
  Time compile_encoder_t.
  repeat (apply CompileDeallocSCA_discretely; try compile_encoder_t).
  (* FIXME use these only in the microbenchmarks *)
  Ltac _compile_mutation ::= fail.
  Ltac _compile_constructor ::= fail.
  Ltac _compile_destructor ::= fail.
Defined.

Eval lazy in (extract_facade FourWords_compile).

Print Assumptions FourWords_compile.

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

Typeclasses eauto := 10.

Instance WrapListOfBoundedValues :
  (* FIXME when the elements of the list inject into W, we should have a
     canonical into lists of words. *)
  FacadeWrapper (Value ADTValue) (list (BoundedN 8)). Admitted.

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
  eauto using map_inj, wrap_inj.
Qed.

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

