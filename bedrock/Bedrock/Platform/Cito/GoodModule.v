Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.GoodFunction.
Require Import Bedrock.Platform.Cito.NameDecoration.

Record GoodModule :=
  {
    Name : string;
    GoodModuleName : IsGoodModuleName Name;
    Functions : list GoodFunction;
    NoDupFuncNames : NoDup (map (fun (f : GoodFunction) => SyntaxFunc.Name f) Functions)
  }.
