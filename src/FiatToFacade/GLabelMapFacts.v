
  Require Import Bedrock.Platform.Cito.GLabelMap.
  Require Import Coq.FSets.FMapFacts.
  Include (Properties GLabelMap).
  Include (Facts GLabelMap).
  Require Import Bedrock.Platform.Cito.FMapFacts1.
  Include (WFacts_fun GLabelKey.GLabel_as_OT GLabelMap).
