Require Import Bedrock AMD64_gas ADTExamples.ExtractingFiniteSetsExamples.

Definition compiled := moduleS sumUnique.all.
Recursive Extraction compiled.
