Set Implicit Arguments.

Require Import Bedrock.StringSet.
Module String_as_OT := StringKey.

Require Import Coq.FSets.FMapAVL.
Module Import StringMap := Make String_as_OT.

Require Import Coq.Structures.OrdersAlt.
Module String_as_OT_new := Update_OT String_as_OT.
Require Import Coq.Structures.Equalities.
Module String_as_UDT := Make_UDT String_as_OT.
