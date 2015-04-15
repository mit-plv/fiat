Require Import Bedrock AMD64_gas Examples.ExtractingFiniteSetsExamples.

Definition compiled := moduleS sumUnique.all.
Recursive Extraction compiled.
