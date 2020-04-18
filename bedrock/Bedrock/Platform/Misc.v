Require Import Bedrock.Platform.AutoSep.

Set Implicit Arguments.


Ltac make_Himp := match goal with
                    | [ |- interp _ (![?P] _ ---> ![?Q] _)%PropX ] =>
                      let H := fresh in assert (P ===> Q); [ | rewrite sepFormula_eq in *; apply H ]
                    | [ |- himp _ ?P ?Q ] => let H := fresh in assert (H : P ===> Q); [ | apply H ]
                  end.
