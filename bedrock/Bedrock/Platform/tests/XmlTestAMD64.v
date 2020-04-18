Require Import Bedrock.Bedrock Bedrock.Platform.tests.XmlTestDriver Bedrock.AMD64_gas.

Definition compiled := moduleS E.m.
Recursive Extraction compiled.
