Require Import Bedrock.Bedrock Bedrock.Platform.tests.MiniMasterDriver Bedrock.I386_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
