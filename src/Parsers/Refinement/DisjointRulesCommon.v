Require Import Fiat.Common.Tactics.PrintContext.

Ltac get_hyp_of_shape shape :=
  lazymatch goal with
  | [ H' : shape |- _ ] => H'
  | _ => let dummy := match goal with
                      | _ => idtac "In context:";
                             print_context ();
                             fail 1 "Could not find a hypothesis of shape" shape
                                  "Maybe you forgot to run do_disjoint_precomputations"
                      end in
         constr:(I : I)
  end.
