Require Import Coq.omega.Omega.
Require Import Bedrock.Examples.AutoSep.

(** * A trivial example to make sure the array proof automation isn't completely borked *)

Definition readS : spec := SPEC("x") reserving 0
  Al ls,
  PRE[V] [| $3 < natToW (length ls) |] * array ls (V "x")
  POST[R] [| R = selN ls 3 |] * array ls (V "x").

Definition writeS : spec := SPEC("x") reserving 0
  Al ls,
  PRE[V] [| $3 < natToW (length ls) |] * array ls (V "x")
  POST[_] array (updN ls 3 11) (V "x").

Definition bump := map (fun w : W => w ^+ $1).

Definition bumpS : spec := SPEC("arr", "len") reserving 3
  Al ls,
  PRE[V] [| V "len" = $ (length ls) |] * array ls (V "arr")
  POST[_] array (bump ls) (V "arr").

Open Scope list_scope.

Definition arrays := bmodule "read" {{
  bfunction "read"("x") [readS]
    "x" <- "x" + 12;;
    "x" <-* "x";;
    Return "x"
  end with bfunction "write"("x") [writeS]
    "x" <- "x" + 12;;
    "x" *<- 11;;
    Return 0
  end with bfunction "bump"("arr", "len", "i", "tmp", "tmp2") [bumpS]
    "i" <- 0;;
    [Al ls, Al done, Al pending,
      PRE[V] [| V "len" = $ (length ls) |] * [| V "i" = $ (length done) |] * [| ls = done ++ pending |]
        * array ls (V "arr")
      POST[_] Ex ls', [| ls' = done ++ bump pending |] * array ls' (V "arr") ]
    While ("i" < "len") {
      "tmp" <- 4 * "i";;
      "tmp" <- "arr" + "tmp";;
      "tmp2" <-* "tmp";;
      "tmp" *<- "tmp2" + 1;;
      "i" <- "i" + 1
    };;
    Return 0
  end
}}.

Hint Rewrite app_length : sepFormula.

Lemma shift_pos : forall (ls1 ls2 : list W),
  (length ls1 < length (ls1 ++ ls2))%nat
  -> length ls1 + length ls2 = length (ls1 ++ hd (natToW 0) ls2 ^+ natToW 1 :: nil) + length (tl ls2).
  intros; autorewrite with sepFormula in *;
    destruct ls2; simpl in *; unfold W; omega.
Qed.

Ltac pure' := intros; repeat match goal with
                               | [ H : sel _ _ = _ |- _ ] => rewrite H in *
                             end;
  try match goal with
        | [ _ : context[length (?A ++ ?B)] |- _ ] =>
          assert (goodSize (length (A ++ B))) by (eapply containsArray_goodSize; eauto)
      end;
  autorewrite with sepFormula in *; simpl length in *; autorewrite with sepFormula.

Ltac pure := pure'; try (apply f_equal; apply shift_pos; pure'); eauto 7.

Lemma nil_front : forall A n,
  n = @length A nil + n.
  reflexivity.
Qed.

Hint Immediate nil_front.

Lemma shift_updN : forall v pending done,
  (length pending > 0)%nat
  -> updN (done ++ pending) (length done) v = done ++ v :: tl pending.
  induction done; simpl; intuition;
    destruct pending; simpl in *; auto; omega.
Qed.

Theorem selN_hd : forall pending done,
  selN (done ++ pending) (length done) = hd $0 pending.
  induction done; simpl; intuition;
    destruct pending; reflexivity.
Qed.

Hint Rewrite shift_updN selN_hd using solve [ eauto ] : sepFormula.

Hint Rewrite DepList.pf_list_simpl : sepFormula.

Hint Rewrite sel_selN upd_updN using solve [ eauto 6 ] : sepFormula.

Hint Resolve shift_pos.

Lemma not_done_yet : forall A (done pending : list A),
  natToW (length done) < $ (length done + length pending)
  -> (length pending > 0)%nat.
  destruct pending; simpl; intuition;
    rewrite <- plus_n_O in *; unfold natToW in *; nomega.
Qed.

Hint Immediate not_done_yet.

Lemma shift_reorg : forall pending,
  (length pending > 0)%nat
  -> hd $0 pending ^+ $1 :: bump (tl pending)
  = bump pending.
  intros; autorewrite with sepFormula in *; destruct pending; simpl in *; auto; omega.
Qed.

Hint Rewrite shift_reorg using solve [ eauto ] : sepFormula.

Hint Rewrite Npow2_nat wordToN_nat wordToNat_natToWord_idempotent
  using nomega : N.

Lemma now_done : forall A (done pending : list A),
  natToW (length done + length pending) <= $ (length done)
  -> goodSize (length done + length pending)
  -> pending = nil.
  destruct pending; simpl; intuition; elimtype False; eauto.
Qed.

Hint Resolve now_done.

Lemma unbump : forall done pending,
  pending = nil
  -> done ++ pending = done ++ bump pending.
  intros; subst; reflexivity.
Qed.

Hint Resolve unbump.

Hint Rewrite wordToNat_natToW_goodSize using solve [ eauto ] : N.

Lemma bound_nat : forall (done pending : list W),
  natToW (length done) < natToW (length done + length pending)
  -> goodSize (length (done ++ hd $0 pending ^+ $1 :: tl pending))
  -> (length done < length done + length pending)%nat.
  intros; autorewrite with sepFormula N in *; simpl in *;
    apply lt_goodSize'; eauto; destruct pending; simpl in *; eauto using goodSize_weaken.
Qed.

Hint Resolve bound_nat.

Hint Extern 1 (himp _ _ _) => reflexivity.

Lemma goodSize_prefix : forall a b : list W,
  goodSize (length (a ++ b))
  -> goodSize (length a).
  intros; autorewrite with sepFormula in *; eapply goodSize_weaken; eauto.
Qed.

Lemma goodSize_full : forall a b : list W,
  goodSize (length (a ++ b))
  -> goodSize (length a + length b).
  intros; autorewrite with sepFormula in *; eapply goodSize_weaken; eauto.
Qed.

Hint Extern 1 (goodSize (length _)) => eapply goodSize_prefix; eapply containsArray_goodSize.
Hint Extern 1 (goodSize (length _ + length _)) => eapply goodSize_full; eapply containsArray_goodSize.

Hint Extern 1 (_ < _)%nat => apply lt_goodSize'; [ assumption | | ].

Theorem arraysOk : moduleOk arrays.
(*TIME  Clear Timing Profile. *)
  vcgen; abstract (sep_auto; pure).
(*TIME  Print Timing Profile. *)
Qed.
