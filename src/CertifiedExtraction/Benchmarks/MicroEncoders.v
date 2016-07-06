Require Import Benchmarks.MicroEncodersSetup.

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

Open Scope nat_scope.

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

