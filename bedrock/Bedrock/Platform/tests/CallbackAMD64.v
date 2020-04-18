Require Import Bedrock.Bedrock Bedrock.Platform.tests.CallbackDriver Bedrock.AMD64_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
