Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Arith.Arith
        Coq.Program.Program
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Bedrock.Memory.

(* An ADT for interfacing with RADL_Flag values. *)

Definition radl_i2f := Word.natToWord 32.

Definition radl_OPERATIONAL_FLAGS := Eval simpl in radl_i2f 15.
Definition radl_STALE_VALUE := Eval simpl in radl_i2f 1.
Definition radl_STALE_MBOX :=    Eval simpl in radl_i2f 2.
Definition radl_STALE := Eval simpl in radl_i2f 3.
Definition radl_OPERATIONAL_1 := Eval simpl in radl_i2f 4.
Definition radl_OPERATIONAL_2 := Eval simpl in radl_i2f 8.

Definition radl_FAILURE_FLAGS := Eval simpl in Word.wneg radl_OPERATIONAL_FLAGS.

Definition radl_TIMEOUT_VALUE := Eval simpl in radl_i2f 16.
Definition radl_TIMEOUT_MBOX := Eval simpl in radl_i2f 32.
Definition radl_TIMEOUT := Eval simpl in radl_i2f 48.

Definition radl_FAILURE_1 := Eval simpl in radl_i2f 64.
Definition radl_FAILURE_2 := Eval simpl in radl_i2f 128.

Definition RADLFlagADTSig :=
  ADTsignature {
      Constructor "init" : Memory.W             -> rep,
      Method "is_stale"      : rep x unit -> rep x bool,
      Method "is_value_stale" : rep x unit -> rep x bool,
      Method "is_mbox_stale"      : rep x unit -> rep x bool,
      Method "is_failing" : rep x unit -> rep x bool,       
      Method "is_timeout"      : rep x unit -> rep x bool,
      Method "is_value_timeout" : rep x unit -> rep x bool,
      Method "is_mbox_timeout" : rep x unit -> rep x bool }.

Definition radl_is_stale (f : Memory.W) :=
  Word.weqb (Word.wand f radl_STALE) radl_STALE.

Definition radl_is_value_stale (f : Memory.W) :=
  Word.weqb (Word.wand f radl_STALE_VALUE) radl_STALE_VALUE.
Definition radl_is_mbox_stale (f : Memory.W) :=
  Word.weqb (Word.wand f radl_STALE_MBOX) radl_STALE_MBOX.
Definition radl_is_failing (f : Memory.W) :=
  Word.weqb (Word.wand f radl_FAILURE_FLAGS) radl_FAILURE_FLAGS.
Definition radl_is_timeout (f : Memory.W) :=
  Word.weqb (Word.wand f radl_TIMEOUT) radl_TIMEOUT.

Definition radl_is_value_timeout (f : Memory.W) :=
  Word.weqb (Word.wand f radl_TIMEOUT_VALUE) radl_TIMEOUT_VALUE.
Definition radl_is_mbox_timeout (f : Memory.W) :=
  Word.weqb (Word.wand f radl_TIMEOUT_MBOX) radl_TIMEOUT_MBOX.

Definition RADL_FlagADT : DecoratedcADT RADLFlagADTSig :=
  cADTRep Memory.W {
     Def Constructor "init" (w : Memory.W) : rep := w,
     Def Method "is_stale"  (w : rep, _ : unit) : bool :=
       (w, radl_is_stale w),
     Def Method "is_value_stale" (w : rep, _ : unit) : bool :=
       (w, radl_is_value_stale w),
     Def Method "is_mbox_stale"  (w : rep, _ : unit) : bool :=
       (w, radl_is_mbox_stale w),
     Def Method "is_failing"   (w : rep, _ : unit) : bool :=
       (w, radl_is_failing w),
     Def Method "is_timeout"   (w : rep, _ : unit) : bool :=
       (w, radl_is_timeout w),
     Def Method "is_value_timeout"   (w : rep, _ : unit) : bool :=
       (w, radl_is_value_timeout w),
     Def Method "is_mbox_timeout"   (w : rep, _ : unit) : bool :=
       (w, radl_is_mbox_timeout w) }.                                                           
