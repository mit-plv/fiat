Set Implicit Arguments.

Require Import Bedrock.Labels.
Require Import Bedrock.Platform.Cito.GLabel.

Definition to_bedrock_label (l : glabel) : label := (fst l, Global (snd l)).

Coercion to_bedrock_label : glabel >-> label.

Definition from_bedrock_label_map A (f : label -> A) (lbl : glabel) := f lbl.
