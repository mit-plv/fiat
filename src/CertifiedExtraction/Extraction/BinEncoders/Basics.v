Require Export Coq.NArith.NArith.

Require Export Bedrock.Memory.
Require Import
        Fiat.BinEncoders.Env.Lib.FixList
        Fiat.BinEncoders.Env.BinLib.FixInt
        Fiat.BinEncoders.Env.Lib.IList
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.BinLib.Bool
        Fiat.BinEncoders.Env.BinLib.Enum.

Unset Implicit Arguments.

Notation BitArray size := { bs: list bool | List.length bs = size }.
Notation BoundedN size := { n: N | (n < FixInt.exp2 size)%N }.
