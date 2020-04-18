Require Import Bedrock.Bedrock Bedrock.Examples.Factorial Bedrock.AMD64_gas.

Definition compiled := moduleS factProg.
Recursive Extraction compiled.
