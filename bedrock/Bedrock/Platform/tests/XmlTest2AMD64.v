Require Import Bedrock.Bedrock Bedrock.Platform.tests.XmlTest2Driver Bedrock.AMD64_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
