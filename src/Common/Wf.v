(** * Miscellaneous Well-Foundedness Facts *)
Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import Coq.Setoids.Setoid Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Classes.Morphisms Coq.Init.Wf.
Require Import Fiat.Common.Telescope.Core.
Require Import Fiat.Common.Telescope.Instances.
Require Import Fiat.Common.Telescope.Equality.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Section wf.
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
End wf.

Local Ltac Fix_eq_t F_ext Rwf :=
  intros;
  unfold Fix;
  rewrite <- Fix_F_eq;
  apply F_ext; intros;
  repeat match goal with
           | [ |- appcontext[Fix_F _ _ (?f ?x)] ] => generalize (f x)
         end;
  clear -F_ext Rwf;
  match goal with
    | [ |- forall x : Acc _ ?a, _ ] => induction (Rwf a)
  end;
  intros; rewrite <- !Fix_F_eq;
  apply F_ext; eauto.

Local Ltac Fix_Proper_t Fix_eq wf :=
  change (@flatten_forall_eq_relation) with (@flatten_forall_eq);
  let H := fresh "H" in
  let a := fresh "a" in
  unfold forall_relation, pointwise_relation, respectful;
  intros ?? H a; repeat intro;
  induction (wf a);
  rewrite !Fix_eq; [ erewrite H; [ reflexivity | .. ] | .. ]; eauto; intros;
  [ etransitivity; [ symmetry; apply H; reflexivity | apply H; eassumption ]; reflexivity
  | etransitivity; [ apply H; eassumption | symmetry; apply H; reflexivity ]; reflexivity ].

Section FixV.
  Context A (B : A -> Telescope)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a, flattenT (B a) Type).

  Local Notation FixV := (@Fix A R Rwf (fun a : A => flatten_forall (P a))).

  Section F.
    Context (F : forall x : A, (forall y : A, R y x -> flatten_forall (P y)) -> flatten_forall (P x)).

    Definition FixV_eq
               (F_ext : forall x (f g : forall y, R y x -> flatten_forall (P y)),
                          (forall y (p : R y x), flatten_forall_eq (f y p) (g y p))
                          -> flatten_forall_eq (@F x f) (@F x g))
    : forall a, flatten_forall_eq (@FixV F a) (@F a (fun y (_ : R y a) => @FixV F y)).
    Proof. Fix_eq_t F_ext Rwf. Defined.

    Definition FixV_rect
               (Q : forall a, flattenT (Telescope_append (B a) (P a)) Type)
               (H0 : forall x, (forall y, R y x -> flatten_append_forall (@Q y) (@FixV F y))
                              -> flatten_append_forall (@Q x) (@F x (fun (y : A) (_ : R y x) => @FixV F y)))
               (F_ext : forall x (f g : forall y, R y x -> flatten_forall (@P y)),
                          (forall y (p : R y x), flatten_forall_eq (f y p) (g y p))
                          -> flatten_forall_eq (@F x f) (@F x g))
               a
    : flatten_append_forall (@Q a) (@FixV F a).
    Proof.
      induction (Rwf a).
      eapply flatten_append_forall_Proper; auto with nocore.
      symmetry; eapply FixV_eq; auto with nocore.
    Defined.
  End F.

  Global Instance FixV_Proper_eq
  : Proper
      ((forall_relation
          (fun a =>
             (forall_relation
                (fun a' =>
                   pointwise_relation
                     _
                     (flatten_forall_eq_relation)))
               ==> flatten_forall_eq_relation))
         ==> (forall_relation (fun a => flatten_forall_eq_relation)))
      FixV.
  Proof. Fix_Proper_t @FixV_eq Rwf. Qed.
End FixV.

Arguments FixV_Proper_eq {A B R Rwf P} _ _ _ _.

Local Arguments flatten_forall / .
Local Arguments flattenT / .
Local Arguments flatten_forall_eq / .
Local Arguments flatten_forall_eq_relation / .
Local Arguments flatten_append_forall / .

Local Notation type_of x := ((fun T (y : T) => T) _ x).

Section FixVTransfer.
  Context A (B B' : A -> Telescope)
          (f0 : forall a, flattenT_sig (B a) -> flattenT_sig (B' a))
          (g0 : forall a, flattenT_sig (B' a) -> flattenT_sig (B a))
          (sect : forall a x, g0 a (f0 a x) = x)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a, flattenT (B a) Type).

  Let P' : forall a, flattenT (B' a) Type
    := fun a => flattenT_unapply (fun x => flattenT_apply (P a) (g0 _ x)).

  Local Notation FixV := (@Fix A R Rwf (fun a : A => flatten_forall (P a))).
  Local Notation FixV' := (@Fix A R Rwf (fun a : A => flatten_forall (P' a))).

  Section F.
    Context (F : forall x : A, (forall y : A, R y x -> flatten_forall (P y)) -> flatten_forall (P x)).

    Let transfer
    : forall y,
        flatten_forall
          (flattenT_unapply
             (fun x : flattenT_sig (B y) => flattenT_apply (P' y) (f0 y x)))
        -> flatten_forall (P y).
    Proof.
      intro y.
      refine (flatten_forall_eq_rect
                (transitivity
                   ((_ : Proper (pointwise_relation _ _ ==> _) flattenT_unapply)
                      _ _
                      (fun x' => transitivity
                                   (symmetry (flattenT_apply_unapply _ _))
                                   (f_equal (flattenT_apply _) (sect _ _))))
                   (symmetry (flattenT_unapply_apply _)))).
    Defined.

    Let transfer'
    : forall a,
        flatten_forall (P a)
        -> flatten_forall (P' a).
    Proof.
      intro a.
      refine (fun f' => flatten_forall_unapply (fun x' => flatten_forall_apply f' (g0 _ x'))).
    Defined.

    Let untransfer'
    : forall a,
        flatten_forall (P' a)
        -> flatten_forall (P a).
    Proof.
      intro a.
      refine (fun f' => _).
      refine (transfer
                _
                (flatten_forall_unapply (fun x => flatten_forall_apply f' (f0 _ x)))).
    Defined.

    Let F' : forall x : A, (forall y : A, R y x -> flatten_forall (P' y)) -> flatten_forall (P' x)
      := fun a F' => transfer' _ (@F a (fun y pf => transfer _ (flatten_forall_unapply (fun x => flatten_forall_apply (F' y pf) (f0 _ x))))).


    Context (F_ext : forall x (f g : forall y, R y x -> flatten_forall (P y)),
                       (forall y (p : R y x), flatten_forall_eq (f y p) (g y p))
                       -> flatten_forall_eq (@F x f) (@F x g)).

    Lemma F'_ext
    : forall x (f g : forall y, R y x -> flatten_forall (P' y)),
        (forall y (p : R y x), flatten_forall_eq (f y p) (g y p))
        -> flatten_forall_eq (@F' x f) (@F' x g).
    Proof.
      intros x f' g' IH.
      subst F' transfer transfer'; cbv beta.
      apply (_ : Proper (forall_relation _ ==> _) flatten_forall_unapply); intro.
      apply flatten_forall_apply_Proper.
      apply F_ext; intros.
      refine ((_ : Proper (flatten_forall_eq ==> _) (@flatten_forall_eq_rect _ _ _ _)) _ _ _).
      apply (_ : Proper (forall_relation _ ==> _) flatten_forall_unapply); intro.
      apply flatten_forall_apply_Proper.
      apply IH.
    Qed.

    Definition FixV_transfer_eq
               a
    : flatten_forall_eq (@FixV F a) (untransfer' _ (@FixV' F' a)).
    Proof.
      induction (Rwf a).
      rewrite FixV_eq by eauto with nocore.
      etransitivity_rev _.
      { unfold transfer, untransfer'; cbv beta.
        apply flatten_forall_eq_rect_Proper, flatten_forall_unapply_Proper; intro.
        apply flatten_forall_apply_Proper.
        rewrite FixV_eq by auto using F'_ext with nocore.
        reflexivity. }
      etransitivity.
      { apply F_ext; intros.
        set_evars.
        match goal with
          | [ H : forall y r, flatten_forall_eq _ _ |- _ ] => rewrite H by assumption
        end.
        match goal with
          | [ |- ?R ?a (?e ?x ?y) ]
            => revert x y
        end.
        match goal with
          | [ H := ?e |- _ ] => is_evar e; subst H
        end.
        match goal with
          | [ |- forall x y, ?R (@?LHS x y) (?RHS x y) ]
            => unify LHS RHS; cbv beta
        end.
        reflexivity. }
      lazymatch goal with
        | [ |- appcontext[FixV' ?F] ]
          => generalize (FixV' F)
      end.
      subst F'; cbv beta.
      subst untransfer' transfer transfer'; cbv beta.
      intro.
      rewrite flatten_forall_eq_rect_trans.
      match goal with
        | [ |- appcontext[flatten_forall_eq_rect
                            (flattenT_unapply_Proper ?P ?Q ?H)
                            (flatten_forall_unapply ?f)] ]
          => rewrite (@flatten_forall_eq_rect_flattenT_unapply_Proper _ P Q H f)
      end.
      etransitivity_rev _.
      { apply flatten_forall_eq_rect_Proper.
        apply flatten_forall_unapply_Proper; intro.
        match goal with
          | [ |- appcontext[@transitivity _ (@eq ?A) ?P] ]
            => change (@transitivity _ (@eq ?A) P) with (@eq_trans A)
        end.
        match goal with
          | [ |- appcontext[@symmetry _ (@eq ?A) ?P] ]
            => change (@symmetry _ (@eq ?A) P) with (@eq_sym A)
        end.
        set_evars.
        rewrite @transport_pp.
        match goal with
          | [ |- appcontext G[eq_rect _ (fun T => T) (flatten_forall_apply (flatten_forall_unapply ?k) ?x0) _ (eq_sym (flattenT_apply_unapply ?f1 ?x0))] ]
            => let H := fresh in
               pose proof (@eq_rect_symmetry_flattenT_apply_unapply _ f1 x0 k) as H;
                 cbv beta in H |- *;
                 let RHS := match type of H with _ = ?RHS => constr:RHS end in
                 let LHS := match type of H with ?LHS = _ => constr:LHS end in
                 let G' := context G[LHS] in
                 change G';
                   rewrite H;
                   clear H
        end.
        match goal with
          | [ |- context[f_equal _ ?p] ]
            => destruct p; unfold f_equal; simpl @eq_rect
        end.
        subst_body.
        reflexivity. }
      rewrite flatten_forall_eq_rect_symmetry_flattenT_unapply_apply.
      apply F_ext; intros.
      reflexivity.
    Qed.
  End F.
End FixVTransfer.

Section Fix_rect.
  Context (A : Type).
  Local Notation T := (fun _ : A => bottom).

  Let Fix_rect' := @FixV_rect A T.
  Let Fix_rect'T := Eval simpl in type_of Fix_rect'.

  Let Fix_Proper_eq' := @FixV_Proper_eq A T.
  Let Fix_Proper_eq'T := Eval simpl in type_of Fix_Proper_eq'.

  Definition Fix_rect : Fix_rect'T := Fix_rect'.
  Definition Fix_Proper_eq : Fix_Proper_eq'T := Fix_Proper_eq'.
End Fix_rect.

Arguments Fix_Proper_eq {A R Rwf P} _ _ _ _.
Global Existing Instance Fix_Proper_eq.

(** A variant of [Fix] that has a nice [Fix_eq] for functions which
    doesn't require [functional_extensionality]. *)
Section Fix1.
  Context A (B : A -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a, B a -> Type).

  Local Notation Fix1 := (@Fix A R Rwf (fun a : A => forall b, @P a b)).
  Local Notation T := (fun a => tele (B a) (fun _ => bottom)).

  Let Fix1_eq' := @FixV_eq A T R Rwf P.
  Let Fix1_eq'T := Eval simpl in type_of Fix1_eq'.

  Let Fix1_rect' := @FixV_rect A T R Rwf P.
  Let Fix1_rect'T := Eval simpl in type_of Fix1_rect'.

  Let Fix1_Proper_eq' := @FixV_Proper_eq A T R Rwf P.
  Let Fix1_Proper_eq'T := Eval simpl in type_of Fix1_Proper_eq'.

  Definition Fix1_eq : Fix1_eq'T := Fix1_eq'.
  Definition Fix1_rect : Fix1_rect'T := Fix1_rect'.
  Definition Fix1_Proper_eq : Fix1_Proper_eq'T := Fix1_Proper_eq'.
End Fix1.

Arguments Fix1_Proper_eq {A B R Rwf P} _ _ _ _ _.
Global Existing Instance Fix1_Proper_eq.

(** A variant of [Fix] that has a nice [Fix_eq] for functions which
    doesn't require [functional_extensionality]. *)
Section Fix2.
  Context A (B : A -> Type) (C : forall a, B a -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b, C a b -> Type).

  Local Notation Fix2 := (@Fix A R Rwf (fun a : A => forall b c, @P a b c)).
  Local Notation T := (fun a => tele (B a) (fun b => tele (@C a b) (fun _ => bottom))).

  Let Fix2_eq' := @FixV_eq A T R Rwf P.
  Let Fix2_eq'T := Eval simpl in type_of Fix2_eq'.

  Let Fix2_rect' := @FixV_rect A T R Rwf P.
  Let Fix2_rect'T := Eval simpl in type_of Fix2_rect'.

  Let Fix2_Proper_eq' := @FixV_Proper_eq A T R Rwf P.
  Let Fix2_Proper_eq'T := Eval simpl in type_of Fix2_Proper_eq'.

  Definition Fix2_eq : Fix2_eq'T := Fix2_eq'.
  Definition Fix2_rect : Fix2_rect'T := Fix2_rect'.
  Definition Fix2_Proper_eq : Fix2_Proper_eq'T := Fix2_Proper_eq'.
End Fix2.

Arguments Fix2_Proper_eq {A B C R Rwf P} _ _ _ _ _ _.
Global Existing Instance Fix2_Proper_eq.

(** A variant of [Fix] that has a nice [Fix_eq] for functions which
    doesn't require [functional_extensionality]. *)
Section Fix3.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c, D a b c -> Type).

  Local Notation Fix3 := (@Fix A R Rwf (fun a : A => forall b c d, @P a b c d)).
  Local Notation T := (fun a => tele _ (fun b => tele _ (fun c => tele (@D a b c) (fun _ => bottom)))).

  Let Fix3_eq' := @FixV_eq A T R Rwf P.
  Let Fix3_eq'T := Eval simpl in type_of Fix3_eq'.

  Let Fix3_rect' := @FixV_rect A T R Rwf P.
  Let Fix3_rect'T := Eval simpl in type_of Fix3_rect'.

  Let Fix3_Proper_eq' := @FixV_Proper_eq A T R Rwf P.
  Let Fix3_Proper_eq'T := Eval simpl in type_of Fix3_Proper_eq'.

  Definition Fix3_eq : Fix3_eq'T := Fix3_eq'.
  Definition Fix3_rect : Fix3_rect'T := Fix3_rect'.
  Definition Fix3_Proper_eq : Fix3_Proper_eq'T := Fix3_Proper_eq'.
End Fix3.

Arguments Fix3_Proper_eq {A B C D R Rwf P} _ _ _ _ _ _ _.
Global Existing Instance Fix3_Proper_eq.

Section Fix4.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type) (E : forall a b c, D a b c -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c d, E a b c d -> Type).

  Local Notation Fix4 := (@Fix A R Rwf (fun a : A => forall b c d e, @P a b c d e)).
  Local Notation T := (fun a => tele _ (fun b => tele _ (fun c => tele _ (fun d => tele (@E a b c d) (fun _ => bottom))))).

  Let Fix4_eq' := @FixV_eq A T R Rwf P.
  Let Fix4_eq'T := Eval simpl in type_of Fix4_eq'.

  Let Fix4_rect' := @FixV_rect A T R Rwf P.
  Let Fix4_rect'T := Eval simpl in type_of Fix4_rect'.

  Let Fix4_Proper_eq' := @FixV_Proper_eq A T R Rwf P.
  Let Fix4_Proper_eq'T := Eval simpl in type_of Fix4_Proper_eq'.

  Definition Fix4_eq : Fix4_eq'T := Fix4_eq'.
  Definition Fix4_rect : Fix4_rect'T := Fix4_rect'.
  Definition Fix4_Proper_eq : Fix4_Proper_eq'T := Fix4_Proper_eq'.
End Fix4.

Arguments Fix4_Proper_eq {A B C D E R Rwf P} _ _ _ _ _ _ _ _.
Global Existing Instance Fix4_Proper_eq.

Section Fix5.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type) (E : forall a b c, D a b c -> Type) (H : forall a b c d, E a b c d -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c d e, H a b c d e -> Type).

  Local Notation Fix5 := (@Fix A R Rwf (fun a : A => forall b c d e h, @P a b c d e h)).
  Local Notation T := (fun a => tele _ (fun b => tele _ (fun c => tele _ (fun d => tele _ (fun e => tele (@H a b c d e) (fun _ => bottom)))))).

  Let Fix5_eq' := @FixV_eq A T R Rwf P.
  Let Fix5_eq'T := Eval simpl in type_of Fix5_eq'.

  Let Fix5_rect' := @FixV_rect A T R Rwf P.
  Let Fix5_rect'T := Eval simpl in type_of Fix5_rect'.

  Let Fix5_Proper_eq' := @FixV_Proper_eq A T R Rwf P.
  Let Fix5_Proper_eq'T := Eval simpl in type_of Fix5_Proper_eq'.

  Definition Fix5_eq : Fix5_eq'T := Fix5_eq'.
  Definition Fix5_rect : Fix5_rect'T := Fix5_rect'.
  Definition Fix5_Proper_eq : Fix5_Proper_eq'T := Fix5_Proper_eq'.
End Fix5.

Arguments Fix5_Proper_eq {A B C D E H R Rwf P} _ _ _ _ _ _ _ _ _.
Global Existing Instance Fix5_Proper_eq.

Section Fix6.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type) (E : forall a b c, D a b c -> Type) (H : forall a b c d, E a b c d -> Type) (I : forall a b c d e, H a b c d e -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c d e h, I a b c d e h -> Type).

  Local Notation Fix6 := (@Fix A R Rwf (fun a : A => forall b c d e h i, @P a b c d e h i)).
  Local Notation T := (fun a => tele _ (fun b => tele _ (fun c => tele _ (fun d => tele _ (fun e => tele _ (fun h => tele (@I a b c d e h) (fun _ => bottom))))))).

  Let Fix6_eq' := @FixV_eq A T R Rwf P.
  Let Fix6_eq'T := Eval simpl in type_of Fix6_eq'.

  Let Fix6_rect' := @FixV_rect A T R Rwf P.
  Let Fix6_rect'T := Eval simpl in type_of Fix6_rect'.

  Let Fix6_Proper_eq' := @FixV_Proper_eq A T R Rwf P.
  Let Fix6_Proper_eq'T := Eval simpl in type_of Fix6_Proper_eq'.

  Definition Fix6_eq : Fix6_eq'T := Fix6_eq'.
  Definition Fix6_rect : Fix6_rect'T := Fix6_rect'.
  Definition Fix6_Proper_eq : Fix6_Proper_eq'T := Fix6_Proper_eq'.
End Fix6.

Arguments Fix6_Proper_eq {A B C D E H I R Rwf P} _ _ _ _ _ _ _ _ _ _.
Global Existing Instance Fix6_Proper_eq.

Section Fix7.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type) (E : forall a b c, D a b c -> Type) (H : forall a b c d, E a b c d -> Type) (I : forall a b c d e, H a b c d e -> Type) (J : forall a b c d e h, I a b c d e h -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c d e h i, J a b c d e h i -> Type).

  Local Notation Fix7 := (@Fix A R Rwf (fun a : A => forall b c d e h i j, @P a b c d e h i j)).
  Local Notation T := (fun a => tele _ (fun b => tele _ (fun c => tele _ (fun d => tele _ (fun e => tele _ (fun h => tele _ (fun i => tele (@J a b c d e h i) (fun _ => bottom)))))))).

  Let Fix7_eq' := @FixV_eq A T R Rwf P.
  Let Fix7_eq'T := Eval simpl in type_of Fix7_eq'.

  Let Fix7_rect' := @FixV_rect A T R Rwf P.
  Let Fix7_rect'T := Eval simpl in type_of Fix7_rect'.

  Let Fix7_Proper_eq' := @FixV_Proper_eq A T R Rwf P.
  Let Fix7_Proper_eq'T := Eval simpl in type_of Fix7_Proper_eq'.

  Definition Fix7_eq : Fix7_eq'T := Fix7_eq'.
  Definition Fix7_rect : Fix7_rect'T := Fix7_rect'.
  Definition Fix7_Proper_eq : Fix7_Proper_eq'T := Fix7_Proper_eq'.
End Fix7.

Arguments Fix7_Proper_eq {A B C D E H I J R Rwf P} _ _ _ _ _ _ _ _ _ _ _.
Global Existing Instance Fix7_Proper_eq.

Section Fix8.
  Context A (B : A -> Type) (C : forall a, B a -> Type) (D : forall a b, C a b -> Type) (E : forall a b c, D a b c -> Type) (H : forall a b c d, E a b c d -> Type) (I : forall a b c d e, H a b c d e -> Type) (J : forall a b c d e h, I a b c d e h -> Type) (K : forall a b c d e h i, J a b c d e h i -> Type)
          (R : A -> A -> Prop) (Rwf : well_founded R)
          (P : forall a b c d e h i j, K a b c d e h i j -> Type).

  Local Notation Fix8 := (@Fix A R Rwf (fun a : A => forall b c d e h i j k, @P a b c d e h i j k)).
  Local Notation T := (fun a => tele _ (fun b => tele _ (fun c => tele _ (fun d => tele _ (fun e => tele _ (fun h => tele _ (fun i => tele _ (fun j => tele (@K a b c d e h i j) (fun _ => bottom))))))))).

  Let Fix8_eq' := @FixV_eq A T R Rwf P.
  Let Fix8_eq'T := Eval simpl in type_of Fix8_eq'.

  Let Fix8_rect' := @FixV_rect A T R Rwf P.
  Let Fix8_rect'T := Eval simpl in type_of Fix8_rect'.

  Let Fix8_Proper_eq' := @FixV_Proper_eq A T R Rwf P.
  Let Fix8_Proper_eq'T := Eval simpl in type_of Fix8_Proper_eq'.

  Definition Fix8_eq : Fix8_eq'T := Fix8_eq'.
  Definition Fix8_rect : Fix8_rect'T := Fix8_rect'.
  Definition Fix8_Proper_eq : Fix8_Proper_eq'T := Fix8_Proper_eq'.
End Fix8.

Arguments Fix8_Proper_eq {A B C D E H I J K R Rwf P} _ _ _ _ _ _ _ _ _ _ _ _.
Global Existing Instance Fix8_Proper_eq.
