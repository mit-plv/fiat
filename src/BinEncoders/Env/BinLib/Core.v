Require Import
        Fiat.BinEncoders.Env.Common.Specs.

Set Implicit Arguments.

Definition bin := list bool.

Definition bapp {A : Type} := @app A.

Definition bctx (A : Type) := prod A nat.

Definition bctx_equiv {E E'} (ctx_equiv : E -> E' -> Prop) :=
  fun (e : bctx E) (e' : bctx E') => ctx_equiv (fst e) (fst e') /\ snd e = snd e'.
