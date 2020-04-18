Require Import Bedrock.Bedrock Bedrock.Platform.tests.RosMasterDriver Bedrock.I386_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
