Require Import Bedrock.Examples.AutoSep Bedrock.Examples.Malloc Bedrock.Examples.comparison.Server.


Definition program := link mallocM m.

Theorem closed : Imports program = LabelMap.empty _.
  reflexivity.
Qed.

Theorem ok : moduleOk program.
  link mallocMOk ok.
Qed.

Require Import Bedrock.AMD64_gas.

Definition compiled := moduleS program.
Recursive Extraction compiled.
