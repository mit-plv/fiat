Require Import
        Fiat.BinEncoders.Env.Common.Specs.

Set Implicit Arguments.

Definition btransformer : Transformer :=
  {| bin := list bool;
     transform := @app _;
     transform_id := nil;
     transform_id_left := @app_nil_l _;
     transform_id_right := @app_nil_r _;
     transform_assoc := @app_assoc _ |}.
