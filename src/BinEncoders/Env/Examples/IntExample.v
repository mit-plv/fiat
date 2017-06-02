Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Common.ComposeCheckSum
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.CInt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        compcert.lib.Integers.

Module IntEncoder := CInt.Make(Wordsize_32).

Import IntEncoder.

Definition Simple_Format_Spec
           (p : int * list int) :=
        encode_nat_Spec 8 (|snd p|)
  ThenC encode_int_Spec Int.wordsize (fst p)
  ThenC encode_list_Spec (encode_int_Spec Int.wordsize) (snd p)
  DoneC.

Definition Simply_OK (p : int * list int) :=
  ((|snd p|) < pow2 8)%nat.

Definition Simple_Format_decoder
  : CorrectDecoderFor Simply_OK Simple_Format_Spec.
Proof.
  start_synthesizing_decoder.
  normalize_compose transformer.
  repeat first [apply innt_decode_correct; auto
               | solve [ intros; apply intrange]
               | intros; simpl; match goal with |- _ /\ _ => split; intuition eauto end 
               | decode_step idtac].
  synthesize_cache_invariant.
  cbv beta; optimize_decoder_impl.
Defined.

Definition Simple_Format_decoder_impl :=
  Eval simpl in (fst (projT1 Simple_Format_decoder)).

Print Simple_Format_decoder_impl.
