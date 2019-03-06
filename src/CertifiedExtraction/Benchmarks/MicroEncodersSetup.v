Require Export
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Compose
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Lib.FixList
        Fiat.Narcissus.BinLib.FixInt.

Require Export
        Fiat.CertifiedExtraction.RemoveSkips
        Fiat.CertifiedExtraction.Benchmarks.MicrobenchmarksSetup
        Fiat.CertifiedExtraction.Extraction.BinEncoders.BinEncoders.

Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Export
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.Narcissus.Automation.SolverOpt
        Fiat.Narcissus.BinLib.Bool
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.Enum
        Fiat.Narcissus.BinLib.FixInt
        Fiat.Narcissus.Common.Compose
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Lib.FixList
        Fiat.Narcissus.Lib.IList
        Fiat.Narcissus.Lib2.Bool
        Fiat.Narcissus.Lib2.EnumOpt
        Fiat.Narcissus.Lib2.FixListOpt
        Fiat.Narcissus.Lib2.NatOpt
        Fiat.Narcissus.Lib2.NoCache
        Fiat.Narcissus.Lib2.SumTypeOpt
        Fiat.Narcissus.Lib2.Vector
        Fiat.Narcissus.Lib2.WordOpt
        Fiat.Narcissus.Lib2.IPChecksum.

Open Scope binencoders_scope.

Unset Implicit Arguments.

Ltac _encode_prepare_cache :=
  may_alloc_head; (* Only create bindings for the cache once. *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match post with
            | Cons (NTSome _) (ret (byteString (fst (Compose.compose _ _ _ _)))) _ =>
              apply ProgOk_Add_snd_under_fn_ret with (f := fun _ => Nil)
            end).

Ltac _encode_start_compiling :=
  match goal with
  | |- sigT _ => eexists;
               let H := fresh in
               intros H *; destruct H
               (* FIXME: apply RemoveSkips_ProgOk *)
  end.

Ltac compile_encoder_step :=
  (* try _encode_show_progress; *)
  match goal with
  | _ => _encode_start_compiling
  | _ => _compile_encode_do_side_conditions
  | _ => _encode_cleanup
  | _ => _encode_prepare_cache
  | _ => _compile_encode_list
  | _ => _compile_CallWrite
  | _ => _compile_Read
  | _ => _compile_SameWrap
  | _ => _compile_CallListLength
  | _ => _compile_CallAllocString
  | _ => _compile_constant_SCA
  | _ => _compile_dealloc_SCA
  | _ => _compile_compose
  | _ => _compile_step
  end.

Ltac compile_encoder_t :=
  progress (repeat repeat compile_encoder_step).

Global Opaque Compose.compose.
Global Opaque Transformer.transform_id.

Definition MicroEncoders_Env : Env ADTValue :=
  (GLabelMap.empty (FuncSpec _))
    ### ("ByteString", "New") ->> (Axiomatic BytesADTSpec.New)
    ### ("ByteString", "Push") ->> (Axiomatic BytesADTSpec.Push)
    ### ("list[W]", "Pop") ->> (Axiomatic WordListADTSpec.Pop)
    ### ("list[W]", "Empty") ->> (Axiomatic WordListADTSpec.Empty)
    ### ("list[W]", "Delete") ->> (Axiomatic WordListADTSpec.Delete)
    ### ("list[W]", "Length") ->> (Axiomatic WordListADTSpec.Length).

(* FIXME use these only in the microbenchmarks *)
Ltac _compile_mutation ::= fail.
Ltac _compile_constructor ::= fail.
Ltac _compile_destructor ::= fail.

Notation "x 'ThenC' y" := (compose _ x y).
Notation "x 'DoneC'"   := (x ThenC fun e => (transform_id, e)).

Open Scope nat_scope.
Open Scope list_scope.

