Require Import Bedrock.Bedrock Bedrock.Platform.tests.RtosDriver Bedrock.AMD64_gas.

Module M.
  Definition heapSize := (1024 * 1024)%N.
End M.

Module E := Make(M).

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
