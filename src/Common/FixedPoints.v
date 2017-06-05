Require Import Coq.Arith.EqNat Coq.Arith.Compare_dec Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.
Set Implicit Arguments.

Local Arguments leb !_ !_.

Section fixedpoints.
  Context {A : Type}
          (sizeof : A -> nat)
          (step : A -> A)
          (step_monotonic : forall a, sizeof (step a) <= sizeof a)
          (step_eq : forall a, sizeof (step a) = sizeof a -> step a = a)
          (upperbound : A).

  Definition greatest_fixpoint_step
             (greatest_fixpoint : nat -> A -> A)
             (sz : nat)
             (a : A)
    : A
    := match sz with
       | 0 => a
       | S sz'
         => let a' := step a in
            let sza := sizeof a in
            let sza' := sizeof a' in
            if leb (S sza') sza
            then greatest_fixpoint sz' a'
            else a
       end.

  Fixpoint greatest_fixpoint' (sz : nat)
    : A -> A
    := greatest_fixpoint_step greatest_fixpoint' sz.

  Definition greatest_fixpoint (a : A) := greatest_fixpoint' (sizeof a) a.

  Lemma greatest_fixpoint_fixpoint a : step (greatest_fixpoint a) = greatest_fixpoint a.
  Proof.
    unfold greatest_fixpoint.
    set (sz := sizeof a).
    assert (H : sizeof a <= sz) by reflexivity.
    clearbody sz.
    revert dependent a.
    induction sz as [|sz IHsz].
    { simpl.
      intros a Hle.
      assert (sizeof (step a) <= 0) by (etransitivity; [ apply step_monotonic | apply Hle ]).
      apply step_eq; omega. }
    { simpl.
      intros.
      repeat match goal with
             | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
             | [ H : leb _ _ = true |- _ ]
               => apply leb_iff in H
             | [ H : leb _ _ = false |- _ ]
               => apply leb_iff_conv in H
             | _ => solve [ eauto with nocore ]
             | [ |- step _ = _ ] => apply step_eq
             | _ => omega
             | [ H : forall a, _ -> _ = _ |- _ ] => rewrite H by omega
             | [ H : _ < _ |- _ ] => hnf in H
             | [ H : S _ <= S _ |- _ ] => apply Le.le_S_n in H
             | [ H : sizeof ?x <= ?y, H' : ?y <= sizeof (step ?x) |- _ ]
               => let H'' := fresh in
                  assert (H'' : sizeof (step x) <= sizeof x) by apply step_monotonic;
                    assert (sizeof x = y) by omega;
                    assert (y = sizeof (step x)) by omega;
                    clear H H' H''
             | [ H : sizeof ?x <= sizeof (step ?x) |- _ ]
               => let H'' := fresh in
                  assert (H'' : sizeof (step x) <= sizeof x) by apply step_monotonic;
                    assert (sizeof x = sizeof (step x)) by omega;
                    clear H H''
             end. }
  Qed.
End fixedpoints.

Section listpair.
  Context {A B : Type}
          (fA : list A -> list B -> A -> bool)
          (fB : list A -> list B -> B -> bool)
          (upperA : list A)
          (upperB : list B).

  Definition sizeof_pair (lss : list A * list B) : nat
    := length (fst lss) + length (snd lss).

  Let step (lss : list A * list B) : list A * list B
    := (filter (fA (fst lss) (snd lss)) (fst lss),
        filter (fB (fst lss) (snd lss)) (snd lss)).

  Lemma step_monotonic lss : sizeof_pair (step lss) <= sizeof_pair lss.
  Proof.
    unfold step, sizeof_pair; simpl;
      apply Plus.plus_le_compat;
      apply length_filter.
  Qed.

  Lemma step_eq lss
    : sizeof_pair (step lss) = sizeof_pair lss -> step lss = lss.
  Proof.
    unfold sizeof_pair, step; simpl.
    destruct lss as [lsA lsB]; simpl.
    intro H.
    repeat match goal with
           | [ H : context[filter ?f ?ls] |- _ ]
             => unique pose proof (length_filter f ls)
           end.
    match goal with
    | [ H : ?x + ?y = ?x' + ?y' |- _ = _ :> list _ * list _ ]
      => assert (x = x') by omega;
           assert (y = y') by omega;
           clear H
    end.
    rewrite !length_filter_eq by omega.
    reflexivity.
  Qed.

  Definition greatest_fixpoint_of_lists : list A * list B
    := greatest_fixpoint sizeof_pair step (upperA, upperB).

  Definition greatest_fixpoint_of_lists_fixpoint
    : step greatest_fixpoint_of_lists = greatest_fixpoint_of_lists.
  Proof.
    apply greatest_fixpoint_fixpoint.
    { intros; apply step_monotonic. }
    { intros; apply step_eq; assumption. }
  Qed.

  Lemma greatest_fixpoint_of_lists_correct_1
        (lsA := fst greatest_fixpoint_of_lists)
        (lsB := snd greatest_fixpoint_of_lists)
    : fold_right andb true (map (fA lsA lsB) lsA) = true.
  Proof.
    unfold lsA at 2.
    rewrite <- greatest_fixpoint_of_lists_fixpoint.
    unfold step; simpl.
    apply fold_right_andb_true_map_filter.
  Qed.

  Lemma greatest_fixpoint_of_lists_correct_2
        (lsA := fst greatest_fixpoint_of_lists)
        (lsB := snd greatest_fixpoint_of_lists)
    : fold_right andb true (map (fB lsA lsB) lsB) = true.
  Proof.
    unfold lsB at 2.
    rewrite <- greatest_fixpoint_of_lists_fixpoint.
    unfold step; simpl.
    apply fold_right_andb_true_map_filter.
  Qed.
End listpair.
