Require Import Bedrock.Bedrock Bedrock.Platform.tests.ListBuilderDriver Bedrock.AMD64_gas.

Module M.
  Definition heapSize := 1024.
End M.

Module E := Make(M).

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
