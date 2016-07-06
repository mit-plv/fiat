Require Export Coq.NArith.NArith.

Require Export Bedrock.Memory Bedrock.Word.
Require Import
        Fiat.BinEncoders.Env.Lib.FixList
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.Lib.IList
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.BinLib.Bool
        Fiat.BinEncoders.Env.BinLib.Enum.

Unset Implicit Arguments.

Open Scope nat_scope.

Notation BoundedList A size := { ls: list A | List.length ls < size }.
Notation BoundedNat size := { n: nat | (n < pow2 size)%nat }.
Notation BoundedN size := { n: N | (n < FixInt.exp2 size)%N }.