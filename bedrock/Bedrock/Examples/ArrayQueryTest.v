Require Import Bedrock.Examples.AutoSep.


Fixpoint countNonzero (ws : list W) : nat :=
  match ws with
    | nil => O
    | w :: ws => if weq w $0 then countNonzero ws else S (countNonzero ws)
  end.

Definition mainS := SPEC("arr", "len") reserving 3
  Al arr,
  PRE[V] [| V "len" = length arr |] * array arr (V "arr")
  POST[R] [| R = countNonzero arr |] * array arr (V "arr").

Definition m := bmodule "m" {{
  bfunction "main"("arr", "len", "acc", "index", "value") [mainS]
    "acc" <- 0;;

    [After prefix Approaching all
      PRE[V] [| V "acc" = countNonzero prefix |]
      POST[R] [| R = countNonzero all |] ]
    For "index" Holding "value" in "arr" Size "len"
      Where (Value <> 0) {
      "acc" <- "acc" + 1
    };;

    Return "acc"
  end
}}.

Lemma countNonzero_app : forall ws2 ws1,
  countNonzero (ws1 ++ ws2) = countNonzero ws1 + countNonzero ws2.
  induction ws1; simpl; intuition;
    match goal with
      | [ |- context[if ?E then _ else _] ] => destruct E
    end; intuition.
Qed.

Lemma skip : forall val x,
  wneb val 0 <> true
  -> forall ws, x = natToW (countNonzero ws)
    -> x = countNonzero (ws ++ val :: nil).
  intros; subst; rewrite countNonzero_app; simpl;
    unfold wneb, natToW in *;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; intuition.
Qed.

Lemma increment : forall val x,
  wneb val 0 = true
  -> forall ws, x = natToW (countNonzero ws)
    -> x ^+ $1 = natToW (countNonzero (ws ++ val :: nil)).
  intros; subst; rewrite countNonzero_app; simpl;
    unfold wneb, natToW in *;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; discriminate || post; auto.
Qed.

Hint Immediate skip increment.
Hint Resolve tt.

Theorem mOk : moduleOk m.
  vcgen; abstract (for0; sep_auto; eauto).
Qed.
