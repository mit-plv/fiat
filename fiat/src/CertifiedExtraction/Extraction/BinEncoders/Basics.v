Require Export Coq.NArith.NArith.

Require Export Bedrock.Memory Bedrock.Word.
Require Export
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

Unset Implicit Arguments.

Open Scope nat_scope.

Notation BoundedList A size := { ls: list A | List.length ls < size }.
Notation BoundedNat size := { n: nat | (n < pow2 size)%nat }.
Notation BoundedN size := { n: N | (n < FixInt.exp2 size)%N }.

Definition BoundedListLength {A size} (ls : BoundedList A (pow2 size)) : BoundedNat size :=
  exist _ (length (` ls)) (proj2_sig ls).

Section Nat.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  (* TODO move *)
  Definition EncodeBoundedNat {k} (n : BoundedNat k) (ce : CacheEncode) : B * CacheEncode :=
    (* NToWord + N.of_nat needed for performance (otherwise [apply] doesn't terminate) *)
    encode_word_Impl (@NToWord k (N.of_nat (`n))) ce.
End Nat.

(* TODO move *)
Definition BtoW (b: B) : W :=
  (zext b 24).
