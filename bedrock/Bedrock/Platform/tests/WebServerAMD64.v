Require Import Bedrock.Bedrock Bedrock.Platform.tests.WebServerDriver Bedrock.AMD64_gas.

Module M.
  Definition heapSize := (1024 * 1024 * 25)%N.
  Definition port : W := 8080%N.
  Definition numWorkers : W := 10.
End M.

Module E := Make(M).

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
