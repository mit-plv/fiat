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
  let wrapper := WrapInstance (H := (@WrapListByte (natToWord _ 512))) in
  ParametricExtraction
    #vars      fourWords
    #program   ret (FourWords_encode fourWords)
    #arguments (FourWordsAsCollectionOfVariables
                  (NTSome "w0") (NTSome "w1") (NTSome "w2") (NTSome "w3") fourWords)
    #env       MicroEncoders_Env.
Proof.
  Time compile_encoder_t.
Defined.

Eval lazy in (extract_facade FourWords_compile).

Print Assumptions FourWords_compile.

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
     ThenC (encode_list_Impl EncodeBoundedNat (proj1_sig mr.(f3)))) tt)) : list byte.

Definition MixedRecordAsCollectionOfVariables
  {av} vf1 vf2 vf3 ll : Telescope av :=
  [[ vf1 ->> ll.(f1) as _ ]] ::
  [[ vf2 ->> ll.(f2) as _ ]] ::
  [[ vf3 ->> ll.(f3) as _ ]] :: Nil.

Hint Unfold MixedRecord_encode : f2f_binencoders_autorewrite_db.
Hint Unfold MixedRecordAsCollectionOfVariables : f2f_binencoders_autorewrite_db.

Example MixedRecord_compile :
  let wrapper := WrapInstance (H := @WrapListByte (natToWord _ 512)) in
  ParametricExtraction
    #vars      mixedRecord
    #program   ret (MixedRecord_encode mixedRecord)
    #arguments (MixedRecordAsCollectionOfVariables
                  (NTSome "f1") (NTSome "f2") (NTSome "f3") mixedRecord)
    #env       MicroEncoders_Env.
Proof.
  Time compile_encoder_t.
Defined.

Eval lazy in (extract_facade MixedRecord_compile).

Print Assumptions MixedRecord_compile.

Record MixedRecord2 :=
  { g0 : byte;
    g1 : byte;
    g2 : BoundedList (BoundedNat 8) (pow2 8);
    g3 : BoundedList (BoundedNat 8) (pow2 8);
    g4 : BoundedNat 8;
    g5 : BoundedNat 8;
    g6 : BoundedNat 8;
    g7 : BoundedList (BoundedNat 8) (pow2 8) }.

Definition MixedRecord2_encode (mr: MixedRecord2) :=
  byteString
    (fst (  (encode_word_Impl mr.(g0)
      ThenC (encode_word_Impl mr.(g1))
      ThenC (encode_list_Impl EncodeBoundedNat (proj1_sig mr.(g2)))
      ThenC (encode_list_Impl EncodeBoundedNat (proj1_sig mr.(g3)))
      ThenC (EncodeBoundedNat mr.(g4))
      ThenC (EncodeBoundedNat mr.(g5))
      ThenC (EncodeBoundedNat mr.(g6))
      ThenC (EncodeBoundedNat mr.(g6))
      ThenC (encode_list_Impl EncodeBoundedNat (proj1_sig mr.(g7)))
      DoneC) ())).

Definition MixedRecord2AsCollectionOfVariables
  {av} vg0 vg1 vg2 vg3 vg4 vg5 vg6 vg7 mr : Telescope av :=
  [[ vg0 ->> mr.(g0) as _]] ::
  [[ vg1 ->> mr.(g1) as _]] ::
  [[ vg2 ->> mr.(g2) as _]] ::
  [[ vg3 ->> mr.(g3) as _]] ::
  [[ vg4 ->> mr.(g4) as _]] ::
  [[ vg5 ->> mr.(g5) as _]] ::
  [[ vg6 ->> mr.(g6) as _]] ::
  [[ vg7 ->> mr.(g7) as _]] ::
  Nil.

Hint Unfold MixedRecord2_encode : f2f_binencoders_autorewrite_db.
Hint Unfold MixedRecord2AsCollectionOfVariables : f2f_binencoders_autorewrite_db.

Example MixedRecord2_compile :
  let wrapper := WrapInstance (H := @WrapListByte (natToWord _ 1024)) in
  ParametricExtraction
    #vars      mixedRecord2
    #program   ret (MixedRecord2_encode mixedRecord2)
    #arguments (MixedRecord2AsCollectionOfVariables
                  (NTSome "g0") (NTSome "g1") (NTSome "g2")
                  (NTSome "g3") (NTSome "g4") (NTSome "g5")
                  (NTSome "g6") (NTSome "g7") mixedRecord2)
    #env       MicroEncoders_Env.
Proof.
  Time compile_encoder_t.
Defined.

Eval lazy in (extract_facade MixedRecord2_compile).

Print Assumptions MixedRecord2_compile.
