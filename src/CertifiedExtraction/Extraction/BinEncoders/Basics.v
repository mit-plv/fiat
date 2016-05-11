Require Export Coq.NArith.NArith.

Require Export Bedrock.Memory.

Require Export BinEncoders.Env.Examples.Dns. (* FIXME use more precise imports *)
Unset Implicit Arguments.

Notation BitArray size := { bs: list bool | List.length bs = size }.
Notation BoundedN size := { n: N | (n < FixInt.exp2 size)%N }.
