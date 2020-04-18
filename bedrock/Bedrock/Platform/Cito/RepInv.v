Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.

Module Type RepInv (Import E : ADT).

  Require Import Bedrock.Platform.AutoSep.

  Definition RepInv := W -> ADTValue -> HProp.

  Parameter rep_inv : RepInv.

  Hypothesis rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.

End RepInv.
