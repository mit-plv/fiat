Set Implicit Arguments.

Require Import Bedrock.StringSet.
Require Import Coq.Structures.Equalities.
Module K := Make_UDT StringKey.
Module M := StringSet.
Require Import Coq.FSets.FSetProperties.
Include (Properties M).
Require Import Coq.FSets.FSetFacts.
Include (Facts M).
Require Import Bedrock.Platform.Cito.FSetFacts1.
Include (UWFacts_fun K M).
