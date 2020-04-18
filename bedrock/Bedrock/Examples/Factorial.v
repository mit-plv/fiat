Require Import Bedrock.Examples.AutoSep.

(** Factorial is mandatory, isn't it? *)

Inductive factR : W -> W -> Prop :=
| FR0 : factR 0 1
| FRS : forall w r : W, w <> 0 -> factR (w ^- $1) r -> factR w (w ^* r).

Lemma FR0' : forall w : W, w = 0 -> factR w $1.
  intros; subst; apply FR0.
Qed.

Lemma FRS' : forall w r v : W, w <> 0 -> factR (w ^- $1) r -> v = w ^* r -> factR w v.
  intros; subst; eapply FRS; eauto.
Qed.

Hint Resolve FR0' FRS'.

Definition factS : spec := SPEC("n") reserving 1
  PRE[V] Emp
  POST[R] [| factR (V "n") R |].

Definition fact := bmodule "fact" {{
  bfunction "fact"("n", "acc") [factS]
    "acc" <- 1;;

    [PRE[V] Emp
     POST[R] [| exists r, factR (V "n") r /\ R = V "acc" ^* r |] ]
    While ("n" <> 0) {
      "acc" <- "n" * "acc";;
      "n" <- "n" - 1
    };;

    Return "acc"
  end
}}.

Lemma times_1 : forall (n m x : W), factR n x
  -> m = $1 ^* x
  -> factR n m.
  intros; subst; replace ($1 ^* x) with x by W_eq; auto.
Qed.

Hint Resolve times_1.

Theorem factOk : moduleOk fact.
(*TIME  Clear Timing Profile. *)
  vcgen; abstract (sep_auto; eauto; words).

  (* sep_canceler ltac:(isConst) auto_ext ltac:(hints_ext_simplifier auto_ext).  *)
  (* simpl. intros. refine (H8 _ _ _ _).  *)
(*TIME  Print Timing Profile. *)
Qed.

Definition factDriver := bimport [[ "fact"!"fact" @ [factS] ]]
  bmodule "factDriver" {{
    bfunction "main"("x") [SPEC reserving 4
      PRE[_] Emp
      POST[R] [| R = $24 |] ]
      "x" <-- Call "fact"!"fact"(4)
      [PRE[_, R] Emp
       POST[R'] [| R' = R |]];;
      Return "x"
    end
  }}.

Theorem factR_4 : forall r, factR 4 r -> r = 24.
  intros;
    repeat match goal with
             | [ H : factR _ _ |- _ ] => inversion H; clear H; subst; []
           end;
    match goal with
      | [ H : factR _ _ |- _ ] => inversion H; clear H; subst; [ reflexivity
        | elimtype False; match goal with
                            | [ H : _ |- _ ] => apply H; reflexivity
                          end ]
    end.
Qed.

Hint Resolve factR_4.

Theorem factDriverOk : moduleOk factDriver.
(*TIME  Clear Timing Profile. *)
  vcgen; abstract (sep_auto; words).
(*TIME  Print Timing Profile. *)
Qed.

Definition factProg := link fact factDriver.

Theorem factProgOk : moduleOk factProg.
  link factOk factDriverOk.
Qed.
