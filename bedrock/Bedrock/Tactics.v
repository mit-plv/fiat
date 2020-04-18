Require Import Coq.omega.Omega.
Require Import Bedrock.Reflection.
Require Import Coq.Bool.Bool.

Ltac think' ext solver :=
  repeat (match goal with
            | [ H : Some _ = Some _ |- _ ] => inversion H ; clear H ; subst
            | [ H : inl _ = inr _ |- _ ] => inversion H ; clear H ; subst
            | [ H : inr _ = inr _ |- _ ] => inversion H ; clear H ; subst
            | [ H : _ |- _ ] => erewrite H in * |- by solver
            | [ H : _ |- _ ] => erewrite H by solver
            | [ H : andb _ _ = true |- _ ] =>
              apply andb_true_iff in H ; destruct H
            | [ H : orb _ _ = false |- _ ] =>
              apply orb_false_iff in H ; destruct H
            | [ H : Equivalence.equiv _ _ |- _ ] =>
              unfold Equivalence.equiv in H ; subst
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ H : exists x, _ |- _ ] => destruct H
            | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
              ((consider X ; try congruence); [ intros ]) ||
                (consider X ; solve [ congruence | solver ])
          end || (progress ext)).

Ltac think := think' idtac ltac:(eauto).


(** Lemmas About Lists **)
Require Import Coq.Lists.List.
Lemma nth_error_None_length : forall (T : Type) (ls : list T) (n : nat),
  nth_error ls n = None -> length ls <= n.
Proof.
  induction ls; destruct n; simpl; intros; think; try omega. inversion H.
  eapply IHls in H. omega.
Qed.

Lemma map_nth_error_full : forall T U (F : T -> U) ls n,
  nth_error (map F ls) n = match nth_error ls n with
                             | None => None
                             | Some v => Some (F v)
                           end.
Proof.
  induction ls; destruct n; simpl; intros; think; auto.
Qed.
