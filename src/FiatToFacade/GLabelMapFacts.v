Require Export Fiat.Common.Coq__8_4__8_5__Compat.

  Require Import Bedrock.Platform.Cito.GLabelMap.
  Require Import Coq.FSets.FMapFacts.
  Module bug_4066_workaround_1 := (Properties GLabelMap).
  Include bug_4066_workaround_1.
  Module bug_4066_workaround_2 := (Facts GLabelMap).
  Include bug_4066_workaround_2.
  Require Import Bedrock.Platform.Cito.FMapFacts1.
  Module bug_4066_workaround_3 := (WFacts_fun GLabelKey.GLabel_as_OT GLabelMap).
  Include bug_4066_workaround_3.
