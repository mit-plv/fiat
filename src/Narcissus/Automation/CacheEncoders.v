Require Import
        Fiat.Common.ilist
        Fiat.Common.Tactics.HintDbExtra
        Fiat.Common.Tactics.TransparentAbstract
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Narcissus.BinLib.AlignedDecoders.

(* Tactics for caching intermediate encoder definitions. *)
(* The current use case is for the various encoders for sums. *)

Create HintDb formatCache.

Ltac fold_encoders :=
  (repeat foreach [ formatCache ] run (fun id => progress fold id in *)).

Ltac cache_encoders :=
  repeat match goal with
         | |- context [icons (fun (a : ?z) => @?f a) _] =>
           let p' := fresh "encoder" in
           let H'' := fresh in
           assert True as H'' by
                 (clear;
                  (cache_term (fun a : z => f a) as p' run (fun id => fold id in *; add id to formatCache)) ; exact I);
           fold_encoders; clear H''
         | |- context [align_format_list (fun (a : ?z) => @?f a) _ _] =>
           let p' := fresh "encoder" in
           let H'' := fresh in
           assert True as H'' by
                 (clear;
                  (cache_term (fun a : z => f a) as p' run (fun id => fold id in *; add id to formatCache)) ; exact I);
           fold_encoders; clear H''
         end.
