(** * Miscellaneous Well-Foundedness Facts *)
Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import Coq.Setoids.Setoid Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Classes.Morphisms Coq.Init.Wf.
Require Import Fiat.Common.Telescope.Core.
Require Import Fiat.Common.Telescope.Instances.
Require Import Fiat.Common.Telescope.Equality.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Scheme Induction for Acc Sort Prop.
Scheme Induction for Acc Sort Set.
Scheme Induction for Acc Sort Type.

Section wf.
  Global Instance well_founded_subrelation {A}
    : Proper (flip subrelation ==> impl) (@well_founded A).
  Proof.
    intros R R' HR Rwf a.
    induction (Rwf a) as [a Ra R'a].
    constructor; intros y Hy.
    apply R'a, HR, Hy.
  Defined.

  Fixpoint no_wf_cycle_helper {A} {R : relation A} x y
           (H0 : R x y) (H1 : R y x) (wf : Acc R x)
    : False
    := match wf with
       | Acc_intro f => @no_wf_cycle_helper A R y x H1 H0 (f _ H1)
       end.

  Global Instance no_wf_cycle {A R} (Rwf : @well_founded A R) : Asymmetric R.
  Proof.
    intros x y H0 H1.
    specialize (Rwf x).
    eapply no_wf_cycle_helper; [ .. | eassumption ]; eassumption.
  Qed.

  Inductive RT_closure {A} (R : relation A) : relation A :=
  | cinject {x y} : R x y -> RT_closure R x y
  | crefl {x} : RT_closure R x x
  | ctrans {x y z} : RT_closure R x y -> RT_closure R y z -> RT_closure R x z.

  Fixpoint Acc_subrelation {A} (R1 R2 : relation A) (v : A) (Hacc : Acc R1 v)
        (HR : forall x y, RT_closure R2 y v -> R2 x y -> R1 x y) {struct Hacc}
    : Acc R2 v.
  Proof.
    destruct Hacc as [Hacc].
    constructor.
    intros y Hy.
    specialize (fun pf => @Acc_subrelation A R1 R2 y (Hacc y pf)).
    specialize (@Acc_subrelation (HR _ _ (@crefl _ _ _) Hy)).
    apply Acc_subrelation; clear -HR Hy.
    intros x y' Hxy Hr2.
    apply HR; clear HR; [ | assumption ].
    clear -Hy Hxy.
    eapply ctrans; [ eassumption | eapply cinject; eassumption ].
  Defined.

  Section wf_acc_of.
    Context A (RA : relation A).

    Definition well_founded_acc_relation_of
              B (f : B -> A) (fA : forall b, Acc RA (f b))
      : relation B
      := fun b0 b1 => match fA b1 with
                      | Acc_intro fAb1 => exists pf,
                                          fAb1 (f b0) pf = fA b0
                      end.


    Lemma well_founded_well_founded_acc_relation_of B f fA
      : well_founded (@well_founded_acc_relation_of B f fA).
    Proof.
      intro b.
      constructor.
      unfold well_founded_acc_relation_of.
      generalize (fA b).
      generalize (f b).
      lazymatch goal with
      | [ |- forall a' wf', @?P a' wf' ]
        => apply (@Acc_ind_dep A RA P)
      end.
      intros a Ha IH y [pf Hy].
      constructor.
      intros z Hz.
      specialize (IH (f y) pf z).
      apply IH; clear IH.
      destruct Hy.
      apply Hz.
    Defined.

    Fixpoint Acc_RA_of B (f : B -> A) b (ac : Acc RA (f b))
      : Acc (fun x y => RA (f x) (f y)) b.
    Proof.
      refine match ac with
             | Acc_intro fg => Acc_intro _ (fun y Ry => @Acc_RA_of _ _ _ (fg _ _))
             end.
      assumption.
    Defined.

    Lemma well_founded_RA_of B (f : B -> A) (wf_A : well_founded RA)
      : well_founded (fun x y => RA (f x) (f y)).
    Proof.
      intro a.
      apply Acc_RA_of, wf_A.
    Defined.
  End wf_acc_of.

  Section wf_acc_of_option.
    Context A (RA : relation A).

    Definition well_founded_acc_relation_of_opt
              B (f : B -> option A) (fA : forall b, match f b with
                                                    | Some fb => Acc RA fb
                                                    | None => True
                                                    end)
      : relation B
      := fun b0 b1
         => match f b1 as fb1 return match fb1 with
                                     | Some fb => Acc RA fb
                                     | None => True
                                     end -> _
            with
            | Some fb1
              => fun fAb
                 => match fAb with
                    | Acc_intro fAb1
                      => match f b0 as fb0 return match fb0 with
                                                  | Some fb => Acc RA fb
                                                  | None => True
                                                  end -> _
                         with
                         | Some fb0
                           => fun fAb0 => exists pf,
                                  fAb1 fb0 pf = fAb0
                         | None => fun _ => False
                         end (fA b0)
                    end
            | None => fun _ => False
            end (fA b1).

    Lemma well_founded_well_founded_acc_relation_of_opt B f fA
      : well_founded (@well_founded_acc_relation_of_opt B f fA).
    Proof.
      intro b.
      constructor.
      unfold well_founded_acc_relation_of_opt.
      generalize (fA b).
      generalize (f b).
      intros [fb|].
      { revert fb.
        lazymatch goal with
        | [ |- forall a' wf', @?P a' wf' ]
          => apply (@Acc_ind_dep A RA P)
        end.
        intros a Ha IH y.
        constructor.
        generalize dependent (fA y).
        destruct (f y) as [fy|] eqn:Hfy.
        { intros y0 [pf Hy].
          intros z Hz.
          specialize (IH fy pf z).
          apply IH; clear IH.
          destruct Hy.
          apply Hz. }
        { intros ? []. } }
      { intros ?? []. }
    Defined.

    Fixpoint Acc_RA_of_opt B (f : B -> option A) b v (Heq : f b = Some v)
             (ac : Acc RA v) {struct ac}
      : Acc (fun x y => match f x, f y with
                        | Some fx, Some fy => RA fx fy
                        | _, _ => False
                        end) b.
    Proof.
      destruct ac as [fg].
      constructor.
      intros y Ry.
      specialize (fun v H Rv => Acc_RA_of_opt B f y v H (fg _ Rv)); clear fg.
      destruct (f y) as [fy|] eqn:Hfy.
      { specialize (Acc_RA_of_opt _ eq_refl).
        destruct (f b) as [fb|] eqn:Hfb.
        { inversion Heq; clear Heq; subst.
          specialize (Acc_RA_of_opt Ry).
          assumption. }
        { destruct Ry. } }
      { destruct Ry. }
    Defined.

    Lemma well_founded_RA_of_opt B (f : B -> option A) (wf_A : well_founded RA)
      : well_founded (fun x y => match f x, f y with
                                 | Some fx, Some fy => RA fx fy
                                 | _, _ => False
                                 end).
    Proof.
      intro a.
      destruct (f a) eqn:H.
      { eapply Acc_RA_of_opt, wf_A; eassumption. }
      { constructor.
        intro y.
        destruct (f y); [ rewrite H | ]; intros []. }
    Defined.
  End wf_acc_of_option.

  Section wf_prod.
    Context A B (RA : relation A) (RB : relation B).

    Definition prod_relation : relation (A * B)
      := fun ab a'b' =>
           RA (fst ab) (fst a'b') \/ (fst a'b' = fst ab /\ RB (snd ab) (snd a'b')).

    Fixpoint well_founded_prod_relation_helper
             a b
             (wf_A : Acc RA a) (wf_B : well_founded RB) {struct wf_A}
    : Acc prod_relation (a, b)
      := match wf_A with
           | Acc_intro fa => (fix wf_B_rec b' (wf_B' : Acc RB b') : Acc prod_relation (a, b')
                              := Acc_intro
                                   _
                                   (fun ab =>
                                      match ab as ab return prod_relation ab (a, b') -> Acc prod_relation ab with
                                        | (a'', b'') =>
                                          fun pf =>
                                            match pf with
                                              | or_introl pf'
                                                => @well_founded_prod_relation_helper
                                                     _ _
                                                     (fa _ pf')
                                                     wf_B
                                              | or_intror (conj pfa pfb)
                                                => match wf_B' with
                                                     | Acc_intro fb
                                                       => eq_rect
                                                            _
                                                            (fun a'' => Acc prod_relation (a'', b''))
                                                            (wf_B_rec _ (fb _ pfb))
                                                            _
                                                            pfa
                                                   end
                                            end
                                      end)
                             ) b (wf_B b)
         end.

    Definition well_founded_prod_relation : well_founded RA -> well_founded RB -> well_founded prod_relation.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_prod_relation_helper; auto.
    Defined.
  End wf_prod.

  Section wf_sig.
    Context A B (RA : relation A) (RB : forall a : A, relation (B a)).

    Definition sigT_relation : relation (sigT B)
      := fun ab a'b' =>
           RA (projT1 ab) (projT1 a'b') \/ (exists pf : projT1 a'b' = projT1 ab, RB (projT2 ab)
                                                                                    (eq_rect _ B (projT2 a'b') _ pf)).

    Fixpoint well_founded_sigT_relation_helper
             a b
             (wf_A : Acc RA a) (wf_B : forall a, well_founded (@RB a)) {struct wf_A}
    : Acc sigT_relation (existT _ a b).
    Proof.
      refine match wf_A with
               | Acc_intro fa => (fix wf_B_rec b' (wf_B' : Acc (@RB a) b') : Acc sigT_relation (existT _ a b')
                                  := Acc_intro
                                       _
                                       (fun ab =>
                                          match ab as ab return sigT_relation ab (existT _ a b') -> Acc sigT_relation ab with
                                            | existT a'' b'' =>
                                              fun pf =>
                                                match pf with
                                                  | or_introl pf'
                                                    => @well_founded_sigT_relation_helper
                                                         _ _
                                                         (fa _ pf')
                                                         wf_B
                                                  | or_intror (ex_intro pfa pfb)
                                                    => match wf_B' with
                                                         | Acc_intro fb
                                                           => _(*eq_rect
                                                            _
                                                            (fun a'' => Acc sigT_relation (existT B a'' _(*b''*)))
                                                            (wf_B_rec _ (fb _ _(*pfb*)))
                                                            _
                                                            pfa*)
                                                       end
                                                end
                                          end)
                                 ) b (wf_B a b)
             end;
      simpl in *.
      destruct pfa; simpl in *.
      exact (wf_B_rec _ (fb _ pfb)).
    Defined.

    Definition well_founded_sigT_relation : well_founded RA
                                            -> (forall a, well_founded (@RB a))
                                            -> well_founded sigT_relation.
    Proof.
      intros wf_A wf_B [a b]; hnf in *.
      apply well_founded_sigT_relation_helper; auto.
    Defined.
  End wf_sig.

  Section wf_projT1.
    Context A (B : A -> Type) (R : relation A).

    Definition projT1_relation : relation (sigT B)
      := fun ab a'b' =>
           R (projT1 ab) (projT1 a'b').

    Definition well_founded_projT1_relation : well_founded R -> well_founded projT1_relation.
    Proof.
      intros wf [a b]; hnf in *.
      induction (wf a) as [a H IH].
      constructor.
      intros y r.
      specialize (IH _ r (projT2 y)).
      destruct y.
      exact IH.
    Defined.
  End wf_projT1.

  Section wf_iterated_prod_of.
    Context A (R : relation A) (Rwf : well_founded R).

    Fixpoint iterated_prod (n : nat) : Type
      := match n with
         | 0 => unit
         | S n' => A * iterated_prod n'
         end%type.

    Fixpoint iterated_prod_relation {n} : relation (iterated_prod n)
      := match n return relation (iterated_prod n) with
         | 0 => fun _ _ => False
         | S n' => prod_relation R (@iterated_prod_relation n')
         end.

    Fixpoint nat_eq_transfer (P : nat -> Type) (n m : nat) : P n -> (P m) + (EqNat.beq_nat n m = false)
      := match n, m return P n -> (P m) + (EqNat.beq_nat n m = false) with
         | 0, 0 => fun x => inl x
         | S n', S m' => @nat_eq_transfer (fun v => P (S v)) n' m'
         | _, _ => fun _ => inr eq_refl
         end.

    Fixpoint nat_eq_transfer_refl (P : nat -> Type) (n : nat) : forall v : P n, nat_eq_transfer P n n v = inl v
      := match n return forall v : P n, nat_eq_transfer P n n v = inl v with
         | 0 => fun v => eq_refl
         | S n' => @nat_eq_transfer_refl (fun k => P (S k)) n'
         end.

    Fixpoint nat_eq_transfer_neq (P : nat -> Type) (n m : nat)
      : forall v : P n, (if EqNat.beq_nat n m as b return ((P m) + (b = false)) -> Prop
                         then fun _ => True
                         else fun v => v = inr eq_refl)
                          (nat_eq_transfer P n m v)
      := match n, m return forall v : P n, (if EqNat.beq_nat n m as b return ((P m) + (b = false)) -> Prop
                                            then fun _ => True
                                            else fun v => v = inr eq_refl)
                                             (nat_eq_transfer P n m v)
         with
         | 0, 0 => fun _ => I
         | S n', S m' => @nat_eq_transfer_neq (fun v => P (S v)) n' m'
         | _, _ => fun _ => eq_refl
         end.

    Definition iterated_prod_relation_of
               B (sz : B -> nat) (f : forall b, iterated_prod (sz b))
      : relation B
      := fun x y => match nat_eq_transfer _ (sz x) (sz y) (f x) with
                    | inl fx => iterated_prod_relation fx (f y)
                    | inr _ => False
                    end.

    Definition iterated_prod_relation_of_opt
               B (sz : nat) (f : B -> option (iterated_prod sz))
      : relation B
      := fun x y => match f x, f y with
                    | Some fx, Some fy => iterated_prod_relation fx fy
                    | _, _ => False
                    end.

    Lemma well_founded_iterated_prod_relation {n} : well_founded (@iterated_prod_relation n).
    Proof.
      induction n as [|n IHn]; simpl.
      { constructor; intros ? []. }
      { apply well_founded_prod_relation; assumption. }
    Defined.

    Lemma well_founded_iterated_prod_relation_of_opt {B n f} : well_founded (@iterated_prod_relation_of_opt B n f).
    Proof.
      unfold iterated_prod_relation_of_opt.
      apply well_founded_RA_of_opt, well_founded_iterated_prod_relation.
    Defined.

    Local Ltac handle_nat_eq_transfer
      := repeat lazymatch goal with
                | [ |- forall n0 n1, @?P n0 n1 ]
                  => let n0' := fresh "n" in
                     let n1' := fresh "n" in
                     let H := fresh in
                     let H' := fresh in
                     intros n0' n1';
                     destruct (@nat_eq_transfer (P n0') n0' n1') as [H|H];
                     [ clear n1'; revert n0'
                     | apply H
                     | lazymatch goal with
                       | [ |- appcontext[@nat_eq_transfer iterated_prod n1' n0'] ]
                         => pose proof (@nat_eq_transfer_neq iterated_prod n1' n0') as H';
                            cbv beta in *;
                            generalize dependent (nat_eq_transfer iterated_prod n1' n0');
                            let Heq := fresh in
                            destruct (EqNat.beq_nat n1' n0') eqn:Heq;
                            [ apply EqNat.beq_nat_true_iff in Heq; subst; rewrite <- EqNat.beq_nat_refl in H;
                              exfalso; clear -H; congruence
                            | ]
                       | [ |- appcontext[@nat_eq_transfer iterated_prod n0' n1'] ]
                         => pose proof (@nat_eq_transfer_neq iterated_prod n0' n1') as H';
                            cbv beta in *;
                            generalize dependent (nat_eq_transfer iterated_prod n0' n1');
                            rewrite H
                       end
                     ]
                end;
         repeat match goal with
                | _ => reflexivity
                | [ H : False |- _ ] => exfalso; exact H
                | [ H : forall v, _ = inr _ |- _ ] => rewrite H
                | _ => intro
                end.

    Lemma RT_closure_same_size B (sz : B -> nat) (f : forall b, iterated_prod (sz b))
          a b
          (H : RT_closure (iterated_prod_relation_of sz f) a b)
      : sz a = sz b.
    Proof.
      induction H as [x y H | | ].
      { unfold iterated_prod_relation_of in *.
        generalize dependent (f x).
        generalize dependent (f y).
        generalize dependent (sz x).
        generalize dependent (sz y).
        handle_nat_eq_transfer. }
      { reflexivity. }
      { etransitivity; eassumption. }
    Defined.

    Lemma well_founded_iterated_prod_relation_of
          B (sz : B -> nat) (f : forall b, iterated_prod (sz b))
      : well_founded (@iterated_prod_relation_of B sz f).
    Proof.
      intro b.
      pose proof (@well_founded_RA_of_opt (iterated_prod (sz b)) iterated_prod_relation B) as wf.
      specialize (wf (fun b' => match nat_eq_transfer _ (sz b') (sz b) (f b') with
                                | inl v => Some v
                                | inr _ => None
                                end)).
      specialize (wf well_founded_iterated_prod_relation).
      eapply Acc_subrelation; [ eapply wf | clear wf ].
      intros x y H.
      apply RT_closure_same_size in H.
      unfold iterated_prod_relation_of.
      generalize dependent (f b).
      generalize dependent (f x).
      generalize dependent (f y).
      generalize dependent (sz y).
      intros ??; subst.
      clear y.
      generalize dependent (sz b).
      generalize dependent (sz x).
      clear.
      handle_nat_eq_transfer.
      rewrite !nat_eq_transfer_refl in *.
      assumption.
    Defined.
  End wf_iterated_prod_of.

  Section wf_functions.
    Context A (R : relation A).

    Local Infix "<" := R.
    Local Notation "x <= y" := (x = y \/ x < y).

    Context (bot : A) (bot_bot : forall a, bot <= a)
            (Rwf : well_founded R)
            (B : Type).

    Definition function_relation : relation (B -> A)
      := fun f g => (forall x, f x <= g x)
                    /\ exists x, f x <> g x.

    Definition is_finite_for (ls : list B) (f : B -> A)
      := forall x, ~List.In x ls -> f x = bot.

    Definition iterated_prod_of_function_for (ls : list B) (f : B -> A)
      : iterated_prod A (List.length ls)
      := list_rect (fun ls => iterated_prod A (List.length ls))
                   tt
                   (fun x _ v => (f x, v))
                   ls.

    Global Instance is_finite_for_Proper_fr
      : Proper (eq ==> function_relation ==> flip impl) is_finite_for.
    Proof.
      unfold is_finite_for, function_relation.
      intros ls g ?; subst g.
      intros f g [Hle Hne] Hfin x Hnin.
      specialize (Hle x); specialize (Hfin x Hnin).
      destruct Hle as [Heq|Hlt]; [ congruence | ].
      specialize (bot_bot (f x)).
      destruct bot_bot as [Heq|Hlt']; [ congruence | ].
      rewrite Hfin in Hlt.
      clear -Hlt Hlt' Rwf.
      exfalso; eapply no_wf_cycle; eassumption.
    Qed.

    Global Instance is_finite_for_Proper_frc
      : Proper (eq ==> RT_closure function_relation ==> flip impl) is_finite_for.
    Proof.
      intros ls ls' ? f g H Hfin.
      induction H as [ ?? H | | ].
      { eapply is_finite_for_Proper_fr; eassumption. }
      { subst; assumption. }
      { subst; eauto with nocore. }
    Qed.

    Lemma function_subrelation ls (f : B -> A) (H : is_finite_for ls f)
      : forall x y : B -> A,
        RT_closure function_relation y f ->
        function_relation x y ->
        iterated_prod_relation_of R (fun _ : B -> A => length ls)
                                  (iterated_prod_of_function_for ls) x y.
    Proof.
      clear -H.
      intros g h Hhf Hgh.
      assert (Hfinh : is_finite_for ls h) by (rewrite Hhf; assumption).
      assert (Hfing : is_finite_for ls g) by (rewrite Hgh; assumption).
      clear -Hgh Hfinh Hfing.
      unfold iterated_prod_relation_of, function_relation, iterated_prod_of_function_for in *.
      rewrite nat_eq_transfer_refl.
      destruct Hgh as [Hle Hne].
      destruct Hne as [b Hne].
      unfold is_finite_for in *.
      assert (Hin : ~~List.In b ls).
      { intro Hnin.
        rewrite Hfinh in Hne by assumption.
        rewrite Hfing in Hne by assumption.
        congruence. }
      clear Hfinh Hfing.
      induction ls as [|x xs IHxs];
        [ | specialize (Hle x) ];
        simpl; unfold prod_relation; simpl in *;
          intuition (congruence || tauto).
    Qed.

    Definition function_relation_Acc ls (f : B -> A) (H : is_finite_for ls f)
      : Acc function_relation f.
    Proof.
      pose proof (@well_founded_iterated_prod_relation_of
                    A R Rwf (B -> A) (fun _ => List.length ls) (@iterated_prod_of_function_for ls) f)
        as wf.
      eapply Acc_subrelation; [ eexact wf | ].
      apply function_subrelation; assumption.
    Defined.
  End wf_functions.
End wf.
