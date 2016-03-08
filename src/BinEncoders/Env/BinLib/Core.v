Require Import
        Fiat.BinEncoders.Env.Common.Specs.

Set Implicit Arguments.

Definition btransformer : Transformer :=
  {| bin := list bool;
     transform := @app _;
     transform_id := nil;
     transform_id_pf := @app_nil_l _;
     transform_assoc := @app_assoc _ |}.
