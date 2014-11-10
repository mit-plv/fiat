
  Require Import GLabelMap.
  Require Import FMapFacts.
  Include (Properties GLabelMap).
  Include (Facts GLabelMap).
  Require Import FMapFacts1.
  Include (WFacts_fun GLabelKey.GLabel_as_OT GLabelMap).
