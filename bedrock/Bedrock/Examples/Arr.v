Require Import Coq.omega.Omega.
Require Import Bedrock.Examples.AutoSep.

Set Implicit Arguments.


Definition copyS : spec := SPEC("dst", "src", "sz") reserving 3
  Al src, Al dst,
  PRE[V] array src (V "src") * array dst (V "dst")
    * [| V "sz" = length src |] * [| V "sz" = length dst |]
  POST[_] array src (V "src") * array src (V "dst").

Definition agreeUpTo (a b : list W) (i : nat) :=
  exists c, length c = i
    /\ exists a', a = c ++ a'
    /\ exists b', b = c ++ b'.

Definition array := bmodule "array" {{
  bfunction "copy"("dst", "src", "sz", "i", "to", "from") [copyS]
    "i" <- 0;;

    [Al src, Al dst,
      PRE[V] array src (V "src") * array dst (V "dst")
        * [| V "sz" = length src |] * [| V "sz" = length dst |]
        * [| agreeUpTo dst src (wordToNat (V "i")) |]
      POST[_] array src (V "src") * array src (V "dst")]
    While ("i" < "sz") {
      "to" <- 4 * "i";;
      "to" <- "dst" + "to";;

      "from" <- 4 * "i";;
      "from" <- "src" + "from";;

      "from" <-* "from";;
      "to" *<- "from";;

      "i" <- "i" + 1
    };;

    Return 0
  end
}}.

Lemma agreeUpTo_0 : forall a b, agreeUpTo a b 0.
  unfold agreeUpTo; exists nil; simpl; eauto.
Qed.

Local Hint Resolve agreeUpTo_0.

Lemma agreeUpTo_S : forall a b n, agreeUpTo a b (wordToNat n)
  -> n < natToW (length a)
  -> n < natToW (length b)
  -> goodSize (length a)
  -> agreeUpTo (Array.upd a n (Array.sel b n)) b (wordToNat (n ^+ $1)).
  unfold agreeUpTo; intros;
    repeat match goal with
             | [ H : Logic.ex _ |- _ ] => destruct H; intuition; subst
           end; autorewrite with Arr in *.

  exists (x ++ Array.sel (x ++ x1) n :: nil).

  autorewrite with Arr; simpl.
  rewrite H3; intuition eauto.

  destruct x1; simpl in *.
  rewrite H3 in H1.
  unfold natToW in H1; autorewrite with Arr in H1; generalize H1; clear; intros; nomega.

  destruct x0; simpl in *.
  rewrite H3 in H0.
  unfold natToW in H0; autorewrite with Arr in H0; generalize H0; clear; intros; nomega.

  exists x0; autorewrite with Arr; intuition.
  exists x1; autorewrite with Arr; intuition.
Qed.

Local Hint Resolve agreeUpTo_S.

Lemma agreeUpTo_done : forall a b n,
  agreeUpTo a b n
  -> (length a <= n)%nat
  -> (length b <= n)%nat
  -> a = b.
  unfold agreeUpTo; firstorder; subst.
  rewrite app_length in *.
  assert (length x0 = 0) by omega.
  destruct x0; simpl in *; try omega.
  destruct x1; simpl in *; try omega.
  auto.
Qed.

Local Hint Extern 1 (_ < _) => congruence.

Theorem arrayOk : moduleOk array.
  vcgen; abstract (sep_auto;
    match goal with
      | [ |- himp _ (Array.array ?A _) (Array.array ?B _) ] =>
        replace B with A by (eapply agreeUpTo_done; eauto 10); reflexivity
      | _ => eauto 10
    end).
Qed.
