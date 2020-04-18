Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.examples.FiniteSet.

Import Memory.

Inductive ADTValue :=
| Cell : W -> ADTValue
| Arr : list W -> ADTValue
| FSet : WordSet.t -> ADTValue.

Require Import Bedrock.Platform.Cito.ADT.

Module ExampleADT <: ADT.

  Definition ADTValue := ADTValue.

End ExampleADT.
