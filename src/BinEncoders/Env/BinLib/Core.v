Require Import
        Fiat.BinEncoders.Env.Common.Specs.

Set Implicit Arguments.

Definition bin := list bool.

Definition btransformer : Transformer bin :=
  {| transform := @app _;
     transform_id := nil;
     transform_id_pf := @app_nil_l _;
     transform_assoc := @app_assoc _ |}.

Definition bctx (A : Type) := prod A nat.

Definition bctx_equiv {E E'} (ctx_equiv : E -> E' -> Prop) :=
  fun (e : bctx E) (e' : bctx E') => ctx_equiv (fst e) (fst e') /\ snd e = snd e'.
