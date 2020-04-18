Require Import Bedrock.Bedrock Bedrock.Platform.tests.RosMasterDriver Bedrock.AMD64_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
