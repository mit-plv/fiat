Require Import
        Fiat.BinEncoders.Env.Common.Specs.

Set Implicit Arguments.

Notation bin := (list bool).

Global Instance btransformer : Transformer bin :=
  {| transform := @app _;
     bin_measure := (@length bool);
     transform_measure b b' := app_length b b';
     transform_id := nil;
     transform_id_left := @app_nil_l _;
     transform_id_right := @app_nil_r _;
     transform_assoc := @app_assoc _ |}.
