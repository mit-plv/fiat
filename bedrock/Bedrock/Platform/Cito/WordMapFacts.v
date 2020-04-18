Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.WordKey.
Module K := W_as_UDT.
Require Import Bedrock.Platform.Cito.WordMap.
Module M := WordMap.
Require Import Coq.FSets.FMapFacts.
Include (Properties M).
Include (Facts M).
Require Import Bedrock.Platform.Cito.FMapFacts1.
Include (WFacts_fun K M).
Include (UWFacts_fun K M).
Require Import Bedrock.Platform.Cito.FMapFacts2.
Include (UWFacts_fun K M).
