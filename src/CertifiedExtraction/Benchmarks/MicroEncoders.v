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
