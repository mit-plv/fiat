Set Implicit Arguments.

Require Import Bedrock.LabelMap.
Require Import Coq.Structures.Equalities.
Module K := Make_UDT LabelKey.
Module M := LabelMap.
Require Import Coq.FSets.FMapFacts.
Include (Properties M).
Include (Facts M).
Require Import Bedrock.Platform.Cito.FMapFacts1.
Include (WFacts_fun K M).
Include (UWFacts_fun K M).
Require Import Bedrock.Platform.Cito.FMapFacts2.
Include (UWFacts_fun K M).
