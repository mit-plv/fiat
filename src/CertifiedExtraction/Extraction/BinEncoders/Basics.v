Require Export Coq.NArith.NArith.

Require Export Bedrock.Memory Bedrock.Word.
Require Export
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
